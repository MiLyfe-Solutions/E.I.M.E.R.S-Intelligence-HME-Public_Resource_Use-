import V185TrunkScan23Chunk0691

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4092213 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_4092213 : Nat := 118140960795 + 4092213 * 2 ^ 59
def prefixEnd_4092213 : Nat := 4983230072969 + 3 ^ 40 * 4092213 * 2
def baseEnd_4092213 : Nat := 2101272209577502931517761

theorem tailTrace_4092213 : CollatzResearch.WordTrace tailWord_4092213 prefixEnd_4092213 2101272209577502931517761 := by
  unfold tailWord_4092213
  simp only [CollatzResearch.WordTrace]
  refine ⟨149255269923618670183689293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99503513282412446789126195 149255269923618670183689293)
  ·
    refine ⟨55970726221357001318883485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149255269923618670183689293 55970726221357001318883485)
    ·
      refine ⟨20989022333008875494581307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55970726221357001318883485 20989022333008875494581307)
      ·
        refine ⟨31483533499513313241871961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20989022333008875494581307 31483533499513313241871961)
        ·
          refine ⟨23612650124634984931403971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31483533499513313241871961 23612650124634984931403971)
          ·
            refine ⟨35418975186952477397105957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23612650124634984931403971 35418975186952477397105957)
            ·
              refine ⟨6641057847553589511957367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35418975186952477397105957 6641057847553589511957367)
              ·
                refine ⟨9961586771330384267936051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6641057847553589511957367 9961586771330384267936051)
                ·
                  refine ⟨14942380156995576401904077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9961586771330384267936051 14942380156995576401904077)
                  ·
                    refine ⟨5603392558873341150714029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14942380156995576401904077 5603392558873341150714029)
                    ·
                      refine ⟨2101272209577502931517761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5603392558873341150714029 2101272209577502931517761)
                      ·
                        rfl

theorem cell23_4092213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_4092213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092213 prefixEnd_4092213 := by exact prefixLift 4092213
  have htrace : WordTrace (prefixWord ++ tailWord_4092213) baseStart_4092213 baseEnd_4092213 := by
    simpa [prefixWord, tailWord_4092213, baseEnd_4092213] using wordTrace_append hprefix tailTrace_4092213
  have hstable : (prefixWord ++ tailWord_4092213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092213).length < 2 ^ (prefixWord ++ tailWord_4092213).sum := by decide
  have hdescent : baseEnd_4092213 < baseStart_4092213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092223 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 3, 3, 2]
def baseStart_4092223 : Nat := 118140960795 + 4092223 * 2 ^ 59
def prefixEnd_4092223 : Nat := 4983230072969 + 3 ^ 40 * 4092223 * 2
def baseEnd_4092223 : Nat := 2101277344384047892392715

theorem tailTrace_4092223 : CollatzResearch.WordTrace tailWord_4092223 prefixEnd_4092223 2101277344384047892392715 := by
  unfold tailWord_4092223
  simp only [CollatzResearch.WordTrace]
  refine ⟨149255634653582441891553323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99503756435721627927702215 149255634653582441891553323)
  ·
    refine ⟨223883451980373662837329985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149255634653582441891553323 223883451980373662837329985)
    ·
      refine ⟨167912588985280247127997489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223883451980373662837329985 167912588985280247127997489)
      ·
        refine ⟨125934441738960185345998117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167912588985280247127997489 125934441738960185345998117)
        ·
          refine ⟨23612707826055034752374647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125934441738960185345998117 23612707826055034752374647)
          ·
            refine ⟨35419061739082552128561971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23612707826055034752374647 35419061739082552128561971)
            ·
              refine ⟨53128592608623828192842957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35419061739082552128561971 53128592608623828192842957)
              ·
                refine ⟨19923222228233935572316109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53128592608623828192842957 19923222228233935572316109)
                ·
                  refine ⟨7471208335587725839618541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19923222228233935572316109 7471208335587725839618541)
                  ·
                    refine ⟨2801703125845397189856953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7471208335587725839618541 2801703125845397189856953)
                    ·
                      refine ⟨2101277344384047892392715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2801703125845397189856953 2101277344384047892392715)
                      ·
                        rfl

theorem cell23_4092223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 3, 2].length) (baseStart_4092223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092223 prefixEnd_4092223 := by exact prefixLift 4092223
  have htrace : WordTrace (prefixWord ++ tailWord_4092223) baseStart_4092223 baseEnd_4092223 := by
    simpa [prefixWord, tailWord_4092223, baseEnd_4092223] using wordTrace_append hprefix tailTrace_4092223
  have hstable : (prefixWord ++ tailWord_4092223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092223).length < 2 ^ (prefixWord ++ tailWord_4092223).sum := by decide
  have hdescent : baseEnd_4092223 < baseStart_4092223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092240 : List Nat := [2, 1, 1, 1, 1, 7, 1, 3, 1, 3, 2]
def baseStart_4092240 : Nat := 118140960795 + 4092240 * 2 ^ 59
def prefixEnd_4092240 : Nat := 4983230072969 + 3 ^ 40 * 4092240 * 2
def baseEnd_4092240 : Nat := 2101286073555174325880137

theorem tailTrace_4092240 : CollatzResearch.WordTrace tailWord_4092240 prefixEnd_4092240 2101286073555174325880137 := by
  unfold tailWord_4092240
  simp only [CollatzResearch.WordTrace]
  refine ⟨74628127347260426897461087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99504169796347235863281449 74628127347260426897461087)
  ·
    refine ⟨111942191020890640346191631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74628127347260426897461087 111942191020890640346191631)
    ·
      refine ⟨167913286531335960519287447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111942191020890640346191631 167913286531335960519287447)
      ·
        refine ⟨251869929797003940778931171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167913286531335960519287447 251869929797003940778931171)
        ·
          refine ⟨377804894695505911168396757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251869929797003940778931171 377804894695505911168396757)
          ·
            refine ⟨8854802219425919793009299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 377804894695505911168396757 8854802219425919793009299)
            ·
              refine ⟨13282203329138879689513949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8854802219425919793009299 13282203329138879689513949)
              ·
                refine ⟨4980826248427079883567731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13282203329138879689513949 4980826248427079883567731)
                ·
                  refine ⟨7471239372640619825351597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4980826248427079883567731 7471239372640619825351597)
                  ·
                    refine ⟨2801714764740232434506849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7471239372640619825351597 2801714764740232434506849)
                    ·
                      refine ⟨2101286073555174325880137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2801714764740232434506849 2101286073555174325880137)
                      ·
                        rfl

theorem cell23_4092240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 1, 3, 2].length) (baseStart_4092240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092240 prefixEnd_4092240 := by exact prefixLift 4092240
  have htrace : WordTrace (prefixWord ++ tailWord_4092240) baseStart_4092240 baseEnd_4092240 := by
    simpa [prefixWord, tailWord_4092240, baseEnd_4092240] using wordTrace_append hprefix tailTrace_4092240
  have hstable : (prefixWord ++ tailWord_4092240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092240).length < 2 ^ (prefixWord ++ tailWord_4092240).sum := by decide
  have hdescent : baseEnd_4092240 < baseStart_4092240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092313 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 2, 5, 2]
def baseStart_4092313 : Nat := 118140960795 + 4092313 * 2 ^ 59
def prefixEnd_4092313 : Nat := 4983230072969 + 3 ^ 40 * 4092313 * 2
def baseEnd_4092313 : Nat := 2101323557642952540267301

theorem tailTrace_4092313 : CollatzResearch.WordTrace tailWord_4092313 prefixEnd_4092313 2101323557642952540267301 := by
  unfold tailWord_4092313
  simp only [CollatzResearch.WordTrace]
  refine ⟨149258917223256387262329593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99505944815504258174886395 149258917223256387262329593)
  ·
    refine ⟨111944187917442290446747195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149258917223256387262329593 111944187917442290446747195)
    ·
      refine ⟨167916281876163435670120793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111944187917442290446747195 167916281876163435670120793)
      ·
        refine ⟨125937211407122576752590595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167916281876163435670120793 125937211407122576752590595)
        ·
          refine ⟨188905817110683865128885893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125937211407122576752590595 188905817110683865128885893)
          ·
            refine ⟨35419840708253224711666105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188905817110683865128885893 35419840708253224711666105)
            ·
              refine ⟨26564880531189918533749579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35419840708253224711666105 26564880531189918533749579)
              ·
                refine ⟨39847320796784877800624369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26564880531189918533749579 39847320796784877800624369)
                ·
                  refine ⟨29885490597588658350468277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39847320796784877800624369 29885490597588658350468277)
                  ·
                    refine ⟨2801764743523936720356401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29885490597588658350468277 2801764743523936720356401)
                    ·
                      refine ⟨2101323557642952540267301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2801764743523936720356401 2101323557642952540267301)
                      ·
                        rfl

theorem cell23_4092313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 5, 2].length) (baseStart_4092313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092313 prefixEnd_4092313 := by exact prefixLift 4092313
  have htrace : WordTrace (prefixWord ++ tailWord_4092313) baseStart_4092313 baseEnd_4092313 := by
    simpa [prefixWord, tailWord_4092313, baseEnd_4092313] using wordTrace_append hprefix tailTrace_4092313
  have hstable : (prefixWord ++ tailWord_4092313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092313).length < 2 ^ (prefixWord ++ tailWord_4092313).sum := by decide
  have hdescent : baseEnd_4092313 < baseStart_4092313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092343 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 4]
def baseStart_4092343 : Nat := 118140960795 + 4092343 * 2 ^ 59
def prefixEnd_4092343 : Nat := 4983230072969 + 3 ^ 40 * 4092343 * 2
def baseEnd_4092343 : Nat := 2101338962062587422892163

theorem tailTrace_4092343 : CollatzResearch.WordTrace tailWord_4092343 prefixEnd_4092343 2101338962062587422892163 := by
  unfold tailWord_4092343
  simp only [CollatzResearch.WordTrace]
  refine ⟨149260011413147702385921683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99506674275431801590614455 149260011413147702385921683)
  ·
    refine ⟨223890017119721553578882525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149260011413147702385921683 223890017119721553578882525)
    ·
      refine ⟨83958756419895582592080947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223890017119721553578882525 83958756419895582592080947)
      ·
        refine ⟨125938134629843373888121421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83958756419895582592080947 125938134629843373888121421)
        ·
          refine ⟨47226800486191265208045533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125938134629843373888121421 47226800486191265208045533)
          ·
            refine ⟨17710050182321724453017075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47226800486191265208045533 17710050182321724453017075)
            ·
              refine ⟨26565075273482586679525613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17710050182321724453017075 26565075273482586679525613)
              ·
                refine ⟨9961903227555970004822105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26565075273482586679525613 9961903227555970004822105)
                ·
                  refine ⟨7471427420666977503616579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9961903227555970004822105 7471427420666977503616579)
                  ·
                    refine ⟨11207141131000466255424869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7471427420666977503616579 11207141131000466255424869)
                    ·
                      refine ⟨2101338962062587422892163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11207141131000466255424869 2101338962062587422892163)
                      ·
                        rfl

theorem cell23_4092343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_4092343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092343 prefixEnd_4092343 := by exact prefixLift 4092343
  have htrace : WordTrace (prefixWord ++ tailWord_4092343) baseStart_4092343 baseEnd_4092343 := by
    simpa [prefixWord, tailWord_4092343, baseEnd_4092343] using wordTrace_append hprefix tailTrace_4092343
  have hstable : (prefixWord ++ tailWord_4092343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092343).length < 2 ^ (prefixWord ++ tailWord_4092343).sum := by decide
  have hdescent : baseEnd_4092343 < baseStart_4092343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092383 : List Nat := [1, 1, 2, 3, 3, 2, 2, 3, 6]
def baseStart_4092383 : Nat := 118140960795 + 4092383 * 2 ^ 59
def prefixEnd_4092383 : Nat := 4983230072969 + 3 ^ 40 * 4092383 * 2
def baseEnd_4092383 : Nat := 233484389032085251821331

theorem tailTrace_4092383 : CollatzResearch.WordTrace tailWord_4092383 prefixEnd_4092383 233484389032085251821331 := by
  unfold tailWord_4092383
  simp only [CollatzResearch.WordTrace]
  refine ⟨149261470333002789217377803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99507646888668526144918535 149261470333002789217377803)
  ·
    refine ⟨223892205499504183826066705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149261470333002789217377803 223892205499504183826066705)
    ·
      refine ⟨167919154124628137869550029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223892205499504183826066705 167919154124628137869550029)
      ·
        refine ⟨62969682796735551701081261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167919154124628137869550029 62969682796735551701081261)
        ·
          refine ⟨23613631048775831887905473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62969682796735551701081261 23613631048775831887905473)
          ·
            refine ⟨17710223286581873915929105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23613631048775831887905473 17710223286581873915929105)
            ·
              refine ⟨13282667464936405436946829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17710223286581873915929105 13282667464936405436946829)
              ·
                refine ⟨4981000299351152038855061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13282667464936405436946829 4981000299351152038855061)
                ·
                  refine ⟨233484389032085251821331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4981000299351152038855061 233484389032085251821331)
                  ·
                    rfl

theorem cell23_4092383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 6].length) (baseStart_4092383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092383 prefixEnd_4092383 := by exact prefixLift 4092383
  have htrace : WordTrace (prefixWord ++ tailWord_4092383) baseStart_4092383 baseEnd_4092383 := by
    simpa [prefixWord, tailWord_4092383, baseEnd_4092383] using wordTrace_append hprefix tailTrace_4092383
  have hstable : (prefixWord ++ tailWord_4092383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092383).length < 2 ^ (prefixWord ++ tailWord_4092383).sum := by decide
  have hdescent : baseEnd_4092383 < baseStart_4092383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092397 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_4092397 : Nat := 118140960795 + 4092397 * 2 ^ 59
def prefixEnd_4092397 : Nat := 4983230072969 + 3 ^ 40 * 4092397 * 2
def baseEnd_4092397 : Nat := 2101366690017930211616915

theorem tailTrace_4092397 : CollatzResearch.WordTrace tailWord_4092397 prefixEnd_4092397 2101366690017930211616915 := by
  unfold tailWord_4092397
  simp only [CollatzResearch.WordTrace]
  refine ⟨149261980954952069608387445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99507987303301379738924963 149261980954952069608387445)
  ·
    refine ⟨13993310714526756525786323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149261980954952069608387445 13993310714526756525786323)
    ·
      refine ⟨20989966071790134788679485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13993310714526756525786323 20989966071790134788679485)
      ·
        refine ⟨7871237276921300545754807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20989966071790134788679485 7871237276921300545754807)
        ·
          refine ⟨11806855915381950818632211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7871237276921300545754807 11806855915381950818632211)
          ·
            refine ⟨17710283873072926227948317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11806855915381950818632211 17710283873072926227948317)
            ·
              refine ⟨6641356452402347335480619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17710283873072926227948317 6641356452402347335480619)
              ·
                refine ⟨9962034678603521003220929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6641356452402347335480619 9962034678603521003220929)
                ·
                  refine ⟨7471526008952640752415697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9962034678603521003220929 7471526008952640752415697)
                  ·
                    refine ⟨5603644506714480564311773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7471526008952640752415697 5603644506714480564311773)
                    ·
                      refine ⟨2101366690017930211616915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5603644506714480564311773 2101366690017930211616915)
                      ·
                        rfl

theorem cell23_4092397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_4092397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092397 prefixEnd_4092397 := by exact prefixLift 4092397
  have htrace : WordTrace (prefixWord ++ tailWord_4092397) baseStart_4092397 baseEnd_4092397 := by
    simpa [prefixWord, tailWord_4092397, baseEnd_4092397] using wordTrace_append hprefix tailTrace_4092397
  have hstable : (prefixWord ++ tailWord_4092397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092397).length < 2 ^ (prefixWord ++ tailWord_4092397).sum := by decide
  have hdescent : baseEnd_4092397 < baseStart_4092397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092427 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 3, 1, 3]
def baseStart_4092427 : Nat := 118140960795 + 4092427 * 2 ^ 59
def prefixEnd_4092427 : Nat := 4983230072969 + 3 ^ 40 * 4092427 * 2
def baseEnd_4092427 : Nat := 2101382094437565094241777

theorem tailTrace_4092427 : CollatzResearch.WordTrace tailWord_4092427 prefixEnd_4092427 2101382094437565094241777 := by
  unfold tailWord_4092427
  simp only [CollatzResearch.WordTrace]
  refine ⟨149263075144843384731979535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99508716763228923154653023 149263075144843384731979535)
  ·
    refine ⟨223894612717265077097969303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149263075144843384731979535 223894612717265077097969303)
    ·
      refine ⟨335841919075897615646953955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223894612717265077097969303 335841919075897615646953955)
      ·
        refine ⟨503762878613846423470430933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335841919075897615646953955 503762878613846423470430933)
        ·
          refine ⟨11806942467512025550088225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 503762878613846423470430933 11806942467512025550088225)
          ·
            refine ⟨8855206850634019162566169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11806942467512025550088225 8855206850634019162566169)
            ·
              refine ⟨6641405137975514371924627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8855206850634019162566169 6641405137975514371924627)
              ·
                refine ⟨9962107706963271557886941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6641405137975514371924627 9962107706963271557886941)
                ·
                  refine ⟨3735790390111226834207603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9962107706963271557886941 3735790390111226834207603)
                  ·
                    refine ⟨5603685585166840251311405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3735790390111226834207603 5603685585166840251311405)
                    ·
                      refine ⟨2101382094437565094241777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5603685585166840251311405 2101382094437565094241777)
                      ·
                        rfl

theorem cell23_4092427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 1, 3].length) (baseStart_4092427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092427 prefixEnd_4092427 := by exact prefixLift 4092427
  have htrace : WordTrace (prefixWord ++ tailWord_4092427) baseStart_4092427 baseEnd_4092427 := by
    simpa [prefixWord, tailWord_4092427, baseEnd_4092427] using wordTrace_append hprefix tailTrace_4092427
  have hstable : (prefixWord ++ tailWord_4092427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092427).length < 2 ^ (prefixWord ++ tailWord_4092427).sum := by decide
  have hdescent : baseEnd_4092427 < baseStart_4092427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092433 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 4]
def baseStart_4092433 : Nat := 118140960795 + 4092433 * 2 ^ 59
def prefixEnd_4092433 : Nat := 4983230072969 + 3 ^ 40 * 4092433 * 2
def baseEnd_4092433 : Nat := 2101385175321492070766749

theorem tailTrace_4092433 : CollatzResearch.WordTrace tailWord_4092433 prefixEnd_4092433 2101385175321492070766749 := by
  unfold tailWord_4092433
  simp only [CollatzResearch.WordTrace]
  refine ⟨149263293982821647756697953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99508862655214431837798635 149263293982821647756697953)
  ·
    refine ⟨111947470487116235817523465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149263293982821647756697953 111947470487116235817523465)
    ·
      refine ⟨83960602865337176863142599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111947470487116235817523465 83960602865337176863142599)
      ·
        refine ⟨125940904298005765294713899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83960602865337176863142599 125940904298005765294713899)
        ·
          refine ⟨188911356447008647942070849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125940904298005765294713899 188911356447008647942070849)
          ·
            refine ⟨141683517335256485956553137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188911356447008647942070849 141683517335256485956553137)
            ·
              refine ⟨106262638001442364467414853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141683517335256485956553137 106262638001442364467414853)
              ·
                refine ⟨19924244625270443337640285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106262638001442364467414853 19924244625270443337640285)
                ·
                  refine ⟨7471591734476416251615107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19924244625270443337640285 7471591734476416251615107)
                  ·
                    refine ⟨11207387601714624377422661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7471591734476416251615107 11207387601714624377422661)
                    ·
                      refine ⟨2101385175321492070766749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11207387601714624377422661 2101385175321492070766749)
                      ·
                        rfl

theorem cell23_4092433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_4092433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092433 prefixEnd_4092433 := by exact prefixLift 4092433
  have htrace : WordTrace (prefixWord ++ tailWord_4092433) baseStart_4092433 baseEnd_4092433 := by
    simpa [prefixWord, tailWord_4092433, baseEnd_4092433] using wordTrace_append hprefix tailTrace_4092433
  have hstable : (prefixWord ++ tailWord_4092433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092433).length < 2 ^ (prefixWord ++ tailWord_4092433).sum := by decide
  have hdescent : baseEnd_4092433 < baseStart_4092433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092450 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 1, 8, 2]
def baseStart_4092450 : Nat := 118140960795 + 4092450 * 2 ^ 59
def prefixEnd_4092450 : Nat := 4983230072969 + 3 ^ 40 * 4092450 * 2
def baseEnd_4092450 : Nat := 2101393904492618504254171

theorem tailTrace_4092450 : CollatzResearch.WordTrace tailWord_4092450 prefixEnd_4092450 2101393904492618504254171 := by
  unfold tailWord_4092450
  simp only [CollatzResearch.WordTrace]
  refine ⟨37315978505940014915016701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99509276015840039773377869 37315978505940014915016701)
  ·
    refine ⟨13993491939727505593131263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37315978505940014915016701 13993491939727505593131263)
    ·
      refine ⟨20990237909591258389696895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13993491939727505593131263 20990237909591258389696895)
      ·
        refine ⟨31485356864386887584545343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20990237909591258389696895 31485356864386887584545343)
        ·
          refine ⟨47228035296580331376818015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31485356864386887584545343 47228035296580331376818015)
          ·
            refine ⟨70842052944870497065227023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47228035296580331376818015 70842052944870497065227023)
            ·
              refine ⟨106263079417305745597840535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70842052944870497065227023 106263079417305745597840535)
              ·
                refine ⟨159394619125958618396760803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106263079417305745597840535 159394619125958618396760803)
                ·
                  refine ⟨239091928688937927595141205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159394619125958618396760803 239091928688937927595141205)
                  ·
                    refine ⟨2801858539323491339005561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 239091928688937927595141205 2801858539323491339005561)
                    ·
                      refine ⟨2101393904492618504254171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2801858539323491339005561 2101393904492618504254171)
                      ·
                        rfl

theorem cell23_4092450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_4092450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092450 prefixEnd_4092450 := by exact prefixLift 4092450
  have htrace : WordTrace (prefixWord ++ tailWord_4092450) baseStart_4092450 baseEnd_4092450 := by
    simpa [prefixWord, tailWord_4092450, baseEnd_4092450] using wordTrace_append hprefix tailTrace_4092450
  have hstable : (prefixWord ++ tailWord_4092450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092450).length < 2 ^ (prefixWord ++ tailWord_4092450).sum := by decide
  have hdescent : baseEnd_4092450 < baseStart_4092450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092478 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 3, 1, 3]
def baseStart_4092478 : Nat := 118140960795 + 4092478 * 2 ^ 59
def prefixEnd_4092478 : Nat := 4983230072969 + 3 ^ 40 * 4092478 * 2
def baseEnd_4092478 : Nat := 2101408281950944394704043

theorem tailTrace_4092478 : CollatzResearch.WordTrace tailWord_4092478 prefixEnd_4092478 2101408281950944394704043 := by
  unfold tailWord_4092478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18658116908457327555260761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99509956845105746961390725 18658116908457327555260761)
  ·
    refine ⟨13993587681342995666445571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18658116908457327555260761 13993587681342995666445571)
    ·
      refine ⟨20990381522014493499668357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13993587681342995666445571 20990381522014493499668357)
      ·
        refine ⟨3935696535377717531187817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20990381522014493499668357 3935696535377717531187817)
        ·
          refine ⟨2951772401533288148390863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3935696535377717531187817 2951772401533288148390863)
          ·
            refine ⟨4427658602299932222586295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2951772401533288148390863 4427658602299932222586295)
            ·
              refine ⟨6641487903449898333879443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4427658602299932222586295 6641487903449898333879443)
              ·
                refine ⟨9962231855174847500819165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6641487903449898333879443 9962231855174847500819165)
                ·
                  refine ⟨3735836945690567812807187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9962231855174847500819165 3735836945690567812807187)
                  ·
                    refine ⟨5603755418535851719210781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3735836945690567812807187 5603755418535851719210781)
                    ·
                      refine ⟨2101408281950944394704043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5603755418535851719210781 2101408281950944394704043)
                      ·
                        rfl

theorem cell23_4092478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_4092478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092478 prefixEnd_4092478 := by exact prefixLift 4092478
  have htrace : WordTrace (prefixWord ++ tailWord_4092478) baseStart_4092478 baseEnd_4092478 := by
    simpa [prefixWord, tailWord_4092478, baseEnd_4092478] using wordTrace_append hprefix tailTrace_4092478
  have hstable : (prefixWord ++ tailWord_4092478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092478).length < 2 ^ (prefixWord ++ tailWord_4092478).sum := by decide
  have hdescent : baseEnd_4092478 < baseStart_4092478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092514 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4092514 : Nat := 118140960795 + 4092514 * 2 ^ 59
def prefixEnd_4092514 : Nat := 4983230072969 + 3 ^ 40 * 4092514 * 2
def baseEnd_4092514 : Nat := 2101426767254506253853877

theorem tailTrace_4092514 : CollatzResearch.WordTrace tailWord_4092514 prefixEnd_4092514 2101426767254506253853877 := by
  unfold tailWord_4092514
  simp only [CollatzResearch.WordTrace]
  refine ⟨37316562073882049647599149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99510832197018799060264397 37316562073882049647599149)
  ·
    refine ⟨13993710777705768617849681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37316562073882049647599149 13993710777705768617849681)
    ·
      refine ⟨10495283083279326463387261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13993710777705768617849681 10495283083279326463387261)
      ·
        refine ⟨3935731156229747423770223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10495283083279326463387261 3935731156229747423770223)
        ·
          refine ⟨5903596734344621135655335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3935731156229747423770223 5903596734344621135655335)
          ·
            refine ⟨8855395101516931703483003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5903596734344621135655335 8855395101516931703483003)
            ·
              refine ⟨13283092652275397555224505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8855395101516931703483003 13283092652275397555224505)
              ·
                refine ⟨9962319489206548166418379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13283092652275397555224505 9962319489206548166418379)
                ·
                  refine ⟨14943479233809822249627569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9962319489206548166418379 14943479233809822249627569)
                  ·
                    refine ⟨11207609425357366687220677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14943479233809822249627569 11207609425357366687220677)
                    ·
                      refine ⟨2101426767254506253853877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11207609425357366687220677 2101426767254506253853877)
                      ·
                        rfl

theorem cell23_4092514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4092514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092514 prefixEnd_4092514 := by exact prefixLift 4092514
  have htrace : WordTrace (prefixWord ++ tailWord_4092514) baseStart_4092514 baseEnd_4092514 := by
    simpa [prefixWord, tailWord_4092514, baseEnd_4092514] using wordTrace_append hprefix tailTrace_4092514
  have hstable : (prefixWord ++ tailWord_4092514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092514).length < 2 ^ (prefixWord ++ tailWord_4092514).sum := by decide
  have hdescent : baseEnd_4092514 < baseStart_4092514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092517 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 1, 3, 3]
def baseStart_4092517 : Nat := 118140960795 + 4092517 * 2 ^ 59
def prefixEnd_4092517 : Nat := 4983230072969 + 3 ^ 40 * 4092517 * 2
def baseEnd_4092517 : Nat := 2101428307696469742116363

theorem tailTrace_4092517 : CollatzResearch.WordTrace tailWord_4092517 prefixEnd_4092517 2101428307696469742116363 := by
  unfold tailWord_4092517
  simp only [CollatzResearch.WordTrace]
  refine ⟨149266357714517330102755805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99510905143011553401837203 149266357714517330102755805)
  ·
    refine ⟨55974884142943998788533427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149266357714517330102755805 55974884142943998788533427)
    ·
      refine ⟨83962326214415998182800141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55974884142943998788533427 83962326214415998182800141)
      ·
        refine ⟨31485872330405999318550053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83962326214415998182800141 31485872330405999318550053)
        ·
          refine ⟨5903601061951124872228135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31485872330405999318550053 5903601061951124872228135)
          ·
            refine ⟨8855401592926687308342203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5903601061951124872228135 8855401592926687308342203)
            ·
              refine ⟨13283102389390030962513305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8855401592926687308342203 13283102389390030962513305)
              ·
                refine ⟨9962326792042523221884979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13283102389390030962513305 9962326792042523221884979)
                ·
                  refine ⟨14943490188063784832827469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9962326792042523221884979 14943490188063784832827469)
                  ·
                    refine ⟨5603808820523919312310301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14943490188063784832827469 5603808820523919312310301)
                    ·
                      refine ⟨2101428307696469742116363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5603808820523919312310301 2101428307696469742116363)
                      ·
                        rfl

theorem cell23_4092517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_4092517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092517 prefixEnd_4092517 := by exact prefixLift 4092517
  have htrace : WordTrace (prefixWord ++ tailWord_4092517) baseStart_4092517 baseEnd_4092517 := by
    simpa [prefixWord, tailWord_4092517, baseEnd_4092517] using wordTrace_append hprefix tailTrace_4092517
  have hstable : (prefixWord ++ tailWord_4092517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092517).length < 2 ^ (prefixWord ++ tailWord_4092517).sum := by decide
  have hdescent : baseEnd_4092517 < baseStart_4092517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092527 : List Nat := [1, 1, 2, 1, 3, 2, 2, 5, 1, 3, 2]
def baseStart_4092527 : Nat := 118140960795 + 4092527 * 2 ^ 59
def prefixEnd_4092527 : Nat := 4983230072969 + 3 ^ 40 * 4092527 * 2
def baseEnd_4092527 : Nat := 2101433442503014702991317

theorem tailTrace_4092527 : CollatzResearch.WordTrace tailWord_4092527 prefixEnd_4092527 2101433442503014702991317 := by
  unfold tailWord_4092527
  simp only [CollatzResearch.WordTrace]
  refine ⟨149266722444481101810619835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99511148296320734540413223 149266722444481101810619835)
  ·
    refine ⟨223900083666721652715929753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149266722444481101810619835 223900083666721652715929753)
    ·
      refine ⟨167925062750041239536947315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223900083666721652715929753 167925062750041239536947315)
      ·
        refine ⟨251887594125061859305420973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167925062750041239536947315 251887594125061859305420973)
        ·
          refine ⟨94457847796898197239532865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251887594125061859305420973 94457847796898197239532865)
          ·
            refine ⟨70843385847673647929649649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94457847796898197239532865 70843385847673647929649649)
            ·
              refine ⟨53132539385755235947237237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70843385847673647929649649 53132539385755235947237237)
              ·
                refine ⟨4981175567414553370053491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53132539385755235947237237 4981175567414553370053491)
                ·
                  refine ⟨7471763351121830055080237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4981175567414553370053491 7471763351121830055080237)
                  ·
                    refine ⟨2801911256670686270655089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7471763351121830055080237 2801911256670686270655089)
                    ·
                      refine ⟨2101433442503014702991317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2801911256670686270655089 2101433442503014702991317)
                      ·
                        rfl

theorem cell23_4092527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 3, 2].length) (baseStart_4092527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092527 prefixEnd_4092527 := by exact prefixLift 4092527
  have htrace : WordTrace (prefixWord ++ tailWord_4092527) baseStart_4092527 baseEnd_4092527 := by
    simpa [prefixWord, tailWord_4092527, baseEnd_4092527] using wordTrace_append hprefix tailTrace_4092527
  have hstable : (prefixWord ++ tailWord_4092527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092527).length < 2 ^ (prefixWord ++ tailWord_4092527).sum := by decide
  have hdescent : baseEnd_4092527 < baseStart_4092527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092543 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 5]
def baseStart_4092543 : Nat := 118140960795 + 4092543 * 2 ^ 59
def prefixEnd_4092543 : Nat := 4983230072969 + 3 ^ 40 * 4092543 * 2
def baseEnd_4092543 : Nat := 2101441658193486640391243

theorem tailTrace_4092543 : CollatzResearch.WordTrace tailWord_4092543 prefixEnd_4092543 2101441658193486640391243 := by
  unfold tailWord_4092543
  simp only [CollatzResearch.WordTrace]
  refine ⟨149267306012423136543202283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99511537341615424362134855 149267306012423136543202283)
  ·
    refine ⟨223900959018634704814803425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149267306012423136543202283 223900959018634704814803425)
    ·
      refine ⟨167925719263976028611102569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223900959018634704814803425 167925719263976028611102569)
      ·
        refine ⟨125944289447982021458326927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167925719263976028611102569 125944289447982021458326927)
        ·
          refine ⟨188916434171973032187490391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125944289447982021458326927 188916434171973032187490391)
          ·
            refine ⟨283374651257959548281235587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188916434171973032187490391 283374651257959548281235587)
            ·
              refine ⟨425061976886939322421853381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283374651257959548281235587 425061976886939322421853381)
              ·
                refine ⟨79699120666301122954097509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425061976886939322421853381 79699120666301122954097509)
                ·
                  refine ⟨14943585124931460553893283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79699120666301122954097509 14943585124931460553893283)
                  ·
                    refine ⟨22415377687397190830839925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14943585124931460553893283 22415377687397190830839925)
                    ·
                      refine ⟨2101441658193486640391243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22415377687397190830839925 2101441658193486640391243)
                      ·
                        rfl

theorem cell23_4092543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_4092543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092543 prefixEnd_4092543 := by exact prefixLift 4092543
  have htrace : WordTrace (prefixWord ++ tailWord_4092543) baseStart_4092543 baseEnd_4092543 := by
    simpa [prefixWord, tailWord_4092543, baseEnd_4092543] using wordTrace_append hprefix tailTrace_4092543
  have hstable : (prefixWord ++ tailWord_4092543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092543).length < 2 ^ (prefixWord ++ tailWord_4092543).sum := by decide
  have hdescent : baseEnd_4092543 < baseStart_4092543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092563 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 7]
def baseStart_4092563 : Nat := 118140960795 + 4092563 * 2 ^ 59
def prefixEnd_4092563 : Nat := 4983230072969 + 3 ^ 40 * 4092563 * 2
def baseEnd_4092563 : Nat := 233494658645175173571239

theorem tailTrace_4092563 : CollatzResearch.WordTrace tailWord_4092563 prefixEnd_4092563 233494658645175173571239 := by
  unfold tailWord_4092563
  simp only [CollatzResearch.WordTrace]
  refine ⟨149268035472350679958930343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99512023648233786639286895 149268035472350679958930343)
  ·
    refine ⟨223902053208526019938395515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149268035472350679958930343 223902053208526019938395515)
    ·
      refine ⟨335853079812789029907593273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223902053208526019938395515 335853079812789029907593273)
      ·
        refine ⟨251889809859591772430694955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335853079812789029907593273 251889809859591772430694955)
        ·
          refine ⟨377834714789387658646042433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251889809859591772430694955 377834714789387658646042433)
          ·
            refine ⟨283376036092040743984531825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377834714789387658646042433 283376036092040743984531825)
            ·
              refine ⟨212532027069030557988398869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283376036092040743984531825 212532027069030557988398869)
              ·
                refine ⟨9962438768860807405706197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 212532027069030557988398869 9962438768860807405706197)
                ·
                  refine ⟨233494658645175173571239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9962438768860807405706197 233494658645175173571239)
                  ·
                    rfl

theorem cell23_4092563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 7].length) (baseStart_4092563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092563 prefixEnd_4092563 := by exact prefixLift 4092563
  have htrace : WordTrace (prefixWord ++ tailWord_4092563) baseStart_4092563 baseEnd_4092563 := by
    simpa [prefixWord, tailWord_4092563, baseEnd_4092563] using wordTrace_append hprefix tailTrace_4092563
  have hstable : (prefixWord ++ tailWord_4092563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092563).length < 2 ^ (prefixWord ++ tailWord_4092563).sum := by decide
  have hdescent : baseEnd_4092563 < baseStart_4092563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092574 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_4092574 : Nat := 118140960795 + 4092574 * 2 ^ 59
def prefixEnd_4092574 : Nat := 4983230072969 + 3 ^ 40 * 4092574 * 2
def baseEnd_4092574 : Nat := 2101457576093776019103601

theorem tailTrace_4092574 : CollatzResearch.WordTrace tailWord_4092574 prefixEnd_4092574 2101457576093776019103601 := by
  unfold tailWord_4092574
  simp only [CollatzResearch.WordTrace]
  refine ⟨18658554584413853604697597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99512291116873885891720517 18658554584413853604697597)
  ·
    refine ⟨6996957969155195101761599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18658554584413853604697597 6996957969155195101761599)
    ·
      refine ⟨10495436953732792652642399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6996957969155195101761599 10495436953732792652642399)
      ·
        refine ⟨15743155430599188978963599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10495436953732792652642399 15743155430599188978963599)
        ·
          refine ⟨23614733145898783468445399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15743155430599188978963599 23614733145898783468445399)
          ·
            refine ⟨35422099718848175202668099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23614733145898783468445399 35422099718848175202668099)
            ·
              refine ⟨53133149578272262804002149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35422099718848175202668099 53133149578272262804002149)
              ·
                refine ⟨9962465545926049275750403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53133149578272262804002149 9962465545926049275750403)
                ·
                  refine ⟨14943698318889073913625605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9962465545926049275750403 14943698318889073913625605)
                  ·
                    refine ⟨2801943434791701358804801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14943698318889073913625605 2801943434791701358804801)
                    ·
                      refine ⟨2101457576093776019103601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2801943434791701358804801 2101457576093776019103601)
                      ·
                        rfl

theorem cell23_4092574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_4092574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092574 prefixEnd_4092574 := by exact prefixLift 4092574
  have htrace : WordTrace (prefixWord ++ tailWord_4092574) baseStart_4092574 baseEnd_4092574 := by
    simpa [prefixWord, tailWord_4092574, baseEnd_4092574] using wordTrace_append hprefix tailTrace_4092574
  have hstable : (prefixWord ++ tailWord_4092574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092574).length < 2 ^ (prefixWord ++ tailWord_4092574).sum := by decide
  have hdescent : baseEnd_4092574 < baseStart_4092574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092591 : List Nat := [1, 1, 2, 1, 2, 7, 1, 2, 2, 2, 2]
def baseStart_4092591 : Nat := 118140960795 + 4092591 * 2 ^ 59
def prefixEnd_4092591 : Nat := 4983230072969 + 3 ^ 40 * 4092591 * 2
def baseEnd_4092591 : Nat := 2101466305264902452591023

theorem tailTrace_4092591 : CollatzResearch.WordTrace tailWord_4092591 prefixEnd_4092591 2101466305264902452591023 := by
  unfold tailWord_4092591
  simp only [CollatzResearch.WordTrace]
  refine ⟨149269056716249240740949627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99512704477499493827299751 149269056716249240740949627)
  ·
    refine ⟨223903585074373861111424441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149269056716249240740949627 223903585074373861111424441)
    ·
      refine ⟨167927688805780395833568331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223903585074373861111424441 167927688805780395833568331)
      ·
        refine ⟨251891533208670593750352497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167927688805780395833568331 251891533208670593750352497)
        ·
          refine ⟨188918649906502945312764373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251891533208670593750352497 188918649906502945312764373)
          ·
            refine ⟨4427780857183662780767915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 188918649906502945312764373 4427780857183662780767915)
            ·
              refine ⟨6641671285775494171151873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4427780857183662780767915 6641671285775494171151873)
              ·
                refine ⟨4981253464331620628363905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6641671285775494171151873 4981253464331620628363905)
                ·
                  refine ⟨3735940098248715471272929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4981253464331620628363905 3735940098248715471272929)
                  ·
                    refine ⟨2801955073686536603454697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3735940098248715471272929 2801955073686536603454697)
                    ·
                      refine ⟨2101466305264902452591023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2801955073686536603454697 2101466305264902452591023)
                      ·
                        rfl

theorem cell23_4092591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 2, 2].length) (baseStart_4092591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092591 prefixEnd_4092591 := by exact prefixLift 4092591
  have htrace : WordTrace (prefixWord ++ tailWord_4092591) baseStart_4092591 baseEnd_4092591 := by
    simpa [prefixWord, tailWord_4092591, baseEnd_4092591] using wordTrace_append hprefix tailTrace_4092591
  have hstable : (prefixWord ++ tailWord_4092591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092591).length < 2 ^ (prefixWord ++ tailWord_4092591).sum := by decide
  have hdescent : baseEnd_4092591 < baseStart_4092591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092597 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 7]
def baseStart_4092597 : Nat := 118140960795 + 4092597 * 2 ^ 59
def prefixEnd_4092597 : Nat := 4983230072969 + 3 ^ 40 * 4092597 * 2
def baseEnd_4092597 : Nat := 233496598460981047679555

theorem tailTrace_4092597 : CollatzResearch.WordTrace tailWord_4092597 prefixEnd_4092597 233496598460981047679555 := by
  unfold tailWord_4092597
  simp only [CollatzResearch.WordTrace]
  refine ⟨149269275554227503765668045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99512850369485002510445363 149269275554227503765668045)
  ·
    refine ⟨55975978332835313912125517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149269275554227503765668045 55975978332835313912125517)
    ·
      refine ⟨20990991874813242717047069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55975978332835313912125517 20990991874813242717047069)
      ·
        refine ⟨7871621953054966018892651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20990991874813242717047069 7871621953054966018892651)
        ·
          refine ⟨11807432929582449028338977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7871621953054966018892651 11807432929582449028338977)
          ·
            refine ⟨8855574697186836771254233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11807432929582449028338977 8855574697186836771254233)
            ·
              refine ⟨6641681022890127578440675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8855574697186836771254233 6641681022890127578440675)
              ·
                refine ⟨9962521534335191367661013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6641681022890127578440675 9962521534335191367661013)
                ·
                  refine ⟨233496598460981047679555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9962521534335191367661013 233496598460981047679555)
                  ·
                    rfl

theorem cell23_4092597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 7].length) (baseStart_4092597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092597 prefixEnd_4092597 := by exact prefixLift 4092597
  have htrace : WordTrace (prefixWord ++ tailWord_4092597) baseStart_4092597 baseEnd_4092597 := by
    simpa [prefixWord, tailWord_4092597, baseEnd_4092597] using wordTrace_append hprefix tailTrace_4092597
  have hstable : (prefixWord ++ tailWord_4092597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092597).length < 2 ^ (prefixWord ++ tailWord_4092597).sum := by decide
  have hdescent : baseEnd_4092597 < baseStart_4092597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092697 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 7, 1, 3]
def baseStart_4092697 : Nat := 118140960795 + 4092697 * 2 ^ 59
def prefixEnd_4092697 : Nat := 4983230072969 + 3 ^ 40 * 4092697 * 2
def baseEnd_4092697 : Nat := 2101520734214279037865535

theorem tailTrace_4092697 : CollatzResearch.WordTrace tailWord_4092697 prefixEnd_4092697 2101520734214279037865535 := by
  unfold tailWord_4092697
  simp only [CollatzResearch.WordTrace]
  refine ⟨149272922853865220844308345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99515281902576813896205563 149272922853865220844308345)
  ·
    refine ⟨111954692140398915633231259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149272922853865220844308345 111954692140398915633231259)
    ·
      refine ⟨167932038210598373449846889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111954692140398915633231259 167932038210598373449846889)
      ·
        refine ⟨125949028657948780087385167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167932038210598373449846889 125949028657948780087385167)
        ·
          refine ⟨188923542986923170131077751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125949028657948780087385167 188923542986923170131077751)
          ·
            refine ⟨283385314480384755196616627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188923542986923170131077751 283385314480384755196616627)
            ·
              refine ⟨425077971720577132794924941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283385314480384755196616627 425077971720577132794924941)
              ·
                refine ⟨159404239395216424798096853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 425077971720577132794924941 159404239395216424798096853)
                ·
                  refine ⟨3736036860825384956205395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 159404239395216424798096853 3736036860825384956205395)
                  ·
                    refine ⟨5604055291238077434308093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3736036860825384956205395 5604055291238077434308093)
                    ·
                      refine ⟨2101520734214279037865535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5604055291238077434308093 2101520734214279037865535)
                      ·
                        rfl

theorem cell23_4092697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_4092697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092697 prefixEnd_4092697 := by exact prefixLift 4092697
  have htrace : WordTrace (prefixWord ++ tailWord_4092697) baseStart_4092697 baseEnd_4092697 := by
    simpa [prefixWord, tailWord_4092697, baseEnd_4092697] using wordTrace_append hprefix tailTrace_4092697
  have hstable : (prefixWord ++ tailWord_4092697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092697).length < 2 ^ (prefixWord ++ tailWord_4092697).sum := by decide
  have hdescent : baseEnd_4092697 < baseStart_4092697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092707 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 3, 5, 2]
def baseStart_4092707 : Nat := 118140960795 + 4092707 * 2 ^ 59
def prefixEnd_4092707 : Nat := 4983230072969 + 3 ^ 40 * 4092707 * 2
def baseEnd_4092707 : Nat := 2101525869020823998740489

theorem tailTrace_4092707 : CollatzResearch.WordTrace tailWord_4092707 prefixEnd_4092707 2101525869020823998740489 := by
  unfold tailWord_4092707
  simp only [CollatzResearch.WordTrace]
  refine ⟨149273287583828992552172375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99515525055885995034781583 149273287583828992552172375)
  ·
    refine ⟨223909931375743488828258563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149273287583828992552172375 223909931375743488828258563)
    ·
      refine ⟨335864897063615233242387845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223909931375743488828258563 335864897063615233242387845)
      ·
        refine ⟨62974668199427856232947721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335864897063615233242387845 62974668199427856232947721)
        ·
          refine ⟨47231001149570892174710791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62974668199427856232947721 47231001149570892174710791)
          ·
            refine ⟨70846501724356338262066187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47231001149570892174710791 70846501724356338262066187)
            ·
              refine ⟨106269752586534507393099281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70846501724356338262066187 106269752586534507393099281)
              ·
                refine ⟨79702314439900880544824461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106269752586534507393099281 79702314439900880544824461)
                ·
                  refine ⟨29888367914962830204309173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79702314439900880544824461 29888367914962830204309173)
                  ·
                    refine ⟨2802034492027765331653985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29888367914962830204309173 2802034492027765331653985)
                    ·
                      refine ⟨2101525869020823998740489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2802034492027765331653985 2101525869020823998740489)
                      ·
                        rfl

theorem cell23_4092707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_4092707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092707 prefixEnd_4092707 := by exact prefixLift 4092707
  have htrace : WordTrace (prefixWord ++ tailWord_4092707) baseStart_4092707 baseEnd_4092707 := by
    simpa [prefixWord, tailWord_4092707, baseEnd_4092707] using wordTrace_append hprefix tailTrace_4092707
  have hstable : (prefixWord ++ tailWord_4092707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092707).length < 2 ^ (prefixWord ++ tailWord_4092707).sum := by decide
  have hdescent : baseEnd_4092707 < baseStart_4092707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092748 : List Nat := [2, 2, 1, 3, 3, 2, 2, 3, 1, 1, 3]
def baseStart_4092748 : Nat := 118140960795 + 4092748 * 2 ^ 59
def prefixEnd_4092748 : Nat := 4983230072969 + 3 ^ 40 * 4092748 * 2
def baseEnd_4092748 : Nat := 2101546921727658338327801

theorem tailTrace_4092748 : CollatzResearch.WordTrace tailWord_4092748 prefixEnd_4092748 2101546921727658338327801 := by
  unfold tailWord_4092748
  simp only [CollatzResearch.WordTrace]
  refine ⟨74637391488340228277207449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99516521984453637702943265 74637391488340228277207449)
  ·
    refine ⟨55978043616255171207905587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74637391488340228277207449 55978043616255171207905587)
    ·
      refine ⟨83967065424382756811858381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55978043616255171207905587 83967065424382756811858381)
      ·
        refine ⟨31487649534143533804446893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83967065424382756811858381 31487649534143533804446893)
        ·
          refine ⟨11807868575303825176667585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31487649534143533804446893 11807868575303825176667585)
          ·
            refine ⟨8855901431477868882500689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11807868575303825176667585 8855901431477868882500689)
            ·
              refine ⟨6641926073608401661875517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8855901431477868882500689 6641926073608401661875517)
              ·
                refine ⟨2490722277603150623203319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6641926073608401661875517 2490722277603150623203319)
                ·
                  refine ⟨3736083416404725934804979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2490722277603150623203319 3736083416404725934804979)
                  ·
                    refine ⟨5604125124607088902207469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3736083416404725934804979 5604125124607088902207469)
                    ·
                      refine ⟨2101546921727658338327801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5604125124607088902207469 2101546921727658338327801)
                      ·
                        rfl

theorem cell23_4092748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_4092748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092748 prefixEnd_4092748 := by exact prefixLift 4092748
  have htrace : WordTrace (prefixWord ++ tailWord_4092748) baseStart_4092748 baseEnd_4092748 := by
    simpa [prefixWord, tailWord_4092748, baseEnd_4092748] using wordTrace_append hprefix tailTrace_4092748
  have hstable : (prefixWord ++ tailWord_4092748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092748).length < 2 ^ (prefixWord ++ tailWord_4092748).sum := by decide
  have hdescent : baseEnd_4092748 < baseStart_4092748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092754 : List Nat := [3, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_4092754 : Nat := 118140960795 + 4092754 * 2 ^ 59
def prefixEnd_4092754 : Nat := 4983230072969 + 3 ^ 40 * 4092754 * 2
def baseEnd_4092754 : Nat := 2101550002611585314852773

theorem tailTrace_4092754 : CollatzResearch.WordTrace tailWord_4092754 prefixEnd_4092754 2101550002611585314852773 := by
  unfold tailWord_4092754
  simp only [CollatzResearch.WordTrace]
  refine ⟨37318750453664679894783329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99516667876439146386088877 37318750453664679894783329)
  ·
    refine ⟨27989062840248509921087497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37318750453664679894783329 27989062840248509921087497)
    ·
      refine ⟨20991797130186382440815623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27989062840248509921087497 20991797130186382440815623)
      ·
        refine ⟨31487695695279573661223435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20991797130186382440815623 31487695695279573661223435)
        ·
          refine ⟨47231543542919360491835153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31487695695279573661223435 47231543542919360491835153)
          ·
            refine ⟨35423657657189520368876365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47231543542919360491835153 35423657657189520368876365)
            ·
              refine ⟨13283871621446070138328637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35423657657189520368876365 13283871621446070138328637)
              ·
                refine ⟨4981451858042276301873239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13283871621446070138328637 4981451858042276301873239)
                ·
                  refine ⟨7472177787063414452809859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4981451858042276301873239 7472177787063414452809859)
                  ·
                    refine ⟨11208266680595121679214789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7472177787063414452809859 11208266680595121679214789)
                    ·
                      refine ⟨2101550002611585314852773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11208266680595121679214789 2101550002611585314852773)
                      ·
                        rfl

theorem cell23_4092754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_4092754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092754 prefixEnd_4092754 := by exact prefixLift 4092754
  have htrace : WordTrace (prefixWord ++ tailWord_4092754) baseStart_4092754 baseEnd_4092754 := by
    simpa [prefixWord, tailWord_4092754, baseEnd_4092754] using wordTrace_append hprefix tailTrace_4092754
  have hstable : (prefixWord ++ tailWord_4092754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092754).length < 2 ^ (prefixWord ++ tailWord_4092754).sum := by decide
  have hdescent : baseEnd_4092754 < baseStart_4092754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092757 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_4092757 : Nat := 118140960795 + 4092757 * 2 ^ 59
def prefixEnd_4092757 : Nat := 4983230072969 + 3 ^ 40 * 4092757 * 2
def baseEnd_4092757 : Nat := 2101551543053548803115259

theorem tailTrace_4092757 : CollatzResearch.WordTrace tailWord_4092757 prefixEnd_4092757 2101551543053548803115259 := by
  unfold tailWord_4092757
  simp only [CollatzResearch.WordTrace]
  refine ⟨149275111233647851091492525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99516740822431900727661683 149275111233647851091492525)
  ·
    refine ⟨55978166712617944159309697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149275111233647851091492525 55978166712617944159309697)
    ·
      refine ⟨41983625034463458119482273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55978166712617944159309697 41983625034463458119482273)
      ·
        refine ⟨31487718775847593589611705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41983625034463458119482273 31487718775847593589611705)
        ·
          refine ⟨23615789081885695192208779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31487718775847593589611705 23615789081885695192208779)
          ·
            refine ⟨35423683622828542788313169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23615789081885695192208779 35423683622828542788313169)
            ·
              refine ⟨26567762717121407091234877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35423683622828542788313169 26567762717121407091234877)
              ·
                refine ⟨9962911018920527659213079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26567762717121407091234877 9962911018920527659213079)
                ·
                  refine ⟨14944366528380791488819619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9962911018920527659213079 14944366528380791488819619)
                  ·
                    refine ⟨22416549792571187233229429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14944366528380791488819619 22416549792571187233229429)
                    ·
                      refine ⟨2101551543053548803115259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22416549792571187233229429 2101551543053548803115259)
                      ·
                        rfl

theorem cell23_4092757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_4092757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092757 prefixEnd_4092757 := by exact prefixLift 4092757
  have htrace : WordTrace (prefixWord ++ tailWord_4092757) baseStart_4092757 baseEnd_4092757 := by
    simpa [prefixWord, tailWord_4092757, baseEnd_4092757] using wordTrace_append hprefix tailTrace_4092757
  have hstable : (prefixWord ++ tailWord_4092757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092757).length < 2 ^ (prefixWord ++ tailWord_4092757).sum := by decide
  have hdescent : baseEnd_4092757 < baseStart_4092757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092771 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 3, 2, 2]
def baseStart_4092771 : Nat := 118140960795 + 4092771 * 2 ^ 59
def prefixEnd_4092771 : Nat := 4983230072969 + 3 ^ 40 * 4092771 * 2
def baseEnd_4092771 : Nat := 2101558731782711748340195

theorem tailTrace_4092771 : CollatzResearch.WordTrace tailWord_4092771 prefixEnd_4092771 2101558731782711748340195 := by
  unfold tailWord_4092771
  simp only [CollatzResearch.WordTrace]
  refine ⟨149275621855597131482502167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99517081237064754321668111 149275621855597131482502167)
  ·
    refine ⟨223913432783395697223753251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149275621855597131482502167 223913432783395697223753251)
    ·
      refine ⟨335870149175093545835629877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223913432783395697223753251 335870149175093545835629877)
      ·
        refine ⟨31487826485165019922090301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 335870149175093545835629877 31487826485165019922090301)
        ·
          refine ⟨11807934931936882470783863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31487826485165019922090301 11807934931936882470783863)
          ·
            refine ⟨17711902397905323706175795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11807934931936882470783863 17711902397905323706175795)
            ·
              refine ⟨26567853596857985559263693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17711902397905323706175795 26567853596857985559263693)
              ·
                refine ⟨9962945098821744584723885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26567853596857985559263693 9962945098821744584723885)
                ·
                  refine ⟨3736104412058154219271457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9962945098821744584723885 3736104412058154219271457)
                  ·
                    refine ⟨2802078309043615664453593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3736104412058154219271457 2802078309043615664453593)
                    ·
                      refine ⟨2101558731782711748340195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2802078309043615664453593 2101558731782711748340195)
                      ·
                        rfl

theorem cell23_4092771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_4092771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092771 prefixEnd_4092771 := by exact prefixLift 4092771
  have htrace : WordTrace (prefixWord ++ tailWord_4092771) baseStart_4092771 baseEnd_4092771 := by
    simpa [prefixWord, tailWord_4092771, baseEnd_4092771] using wordTrace_append hprefix tailTrace_4092771
  have hstable : (prefixWord ++ tailWord_4092771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092771).length < 2 ^ (prefixWord ++ tailWord_4092771).sum := by decide
  have hdescent : baseEnd_4092771 < baseStart_4092771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092805 : List Nat := [1, 3, 1, 1, 3, 5, 1, 3, 1, 2, 2]
def baseStart_4092805 : Nat := 118140960795 + 4092805 * 2 ^ 59
def prefixEnd_4092805 : Nat := 4983230072969 + 3 ^ 40 * 4092805 * 2
def baseEnd_4092805 : Nat := 2101576190124964615315039

theorem tailTrace_4092805 : CollatzResearch.WordTrace tailWord_4092805 prefixEnd_4092805 2101576190124964615315039 := by
  unfold tailWord_4092805
  simp only [CollatzResearch.WordTrace]
  refine ⟨149276861937473955289239869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99517907958315970192826579 149276861937473955289239869)
  ·
    refine ⟨55978823226552733233464951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149276861937473955289239869 55978823226552733233464951)
    ·
      refine ⟨83968234839829099850197427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55978823226552733233464951 83968234839829099850197427)
      ·
        refine ⟨125952352259743649775296141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83968234839829099850197427 125952352259743649775296141)
        ·
          refine ⟨47232132097403868665736053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125952352259743649775296141 47232132097403868665736053)
          ·
            refine ⟨4428012384131612687412755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47232132097403868665736053 4428012384131612687412755)
            ·
              refine ⟨6642018576197419031119133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4428012384131612687412755 6642018576197419031119133)
              ·
                refine ⟨2490756966074032136669675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6642018576197419031119133 2490756966074032136669675)
                ·
                  refine ⟨3736135449111048205004513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2490756966074032136669675 3736135449111048205004513)
                  ·
                    refine ⟨2802101586833286153753385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3736135449111048205004513 2802101586833286153753385)
                    ·
                      refine ⟨2101576190124964615315039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2802101586833286153753385 2101576190124964615315039)
                      ·
                        rfl

theorem cell23_4092805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 1, 2, 2].length) (baseStart_4092805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092805 prefixEnd_4092805 := by exact prefixLift 4092805
  have htrace : WordTrace (prefixWord ++ tailWord_4092805) baseStart_4092805 baseEnd_4092805 := by
    simpa [prefixWord, tailWord_4092805, baseEnd_4092805] using wordTrace_append hprefix tailTrace_4092805
  have hstable : (prefixWord ++ tailWord_4092805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092805).length < 2 ^ (prefixWord ++ tailWord_4092805).sum := by decide
  have hdescent : baseEnd_4092805 < baseStart_4092805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092822 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_4092822 : Nat := 118140960795 + 4092822 * 2 ^ 59
def prefixEnd_4092822 : Nat := 4983230072969 + 3 ^ 40 * 4092822 * 2
def baseEnd_4092822 : Nat := 2101584919296091048802461

theorem tailTrace_4092822 : CollatzResearch.WordTrace tailWord_4092822 prefixEnd_4092822 2101584919296091048802461 := by
  unfold tailWord_4092822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9329842623650772949538045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99518321318941578128405813 9329842623650772949538045)
  ·
    refine ⟨3498690983869039856076767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9329842623650772949538045 3498690983869039856076767)
    ·
      refine ⟨5248036475803559784115151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3498690983869039856076767 5248036475803559784115151)
      ·
        refine ⟨7872054713705339676172727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5248036475803559784115151 7872054713705339676172727)
        ·
          refine ⟨11808082070558009514259091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7872054713705339676172727 11808082070558009514259091)
          ·
            refine ⟨17712123105837014271388637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11808082070558009514259091 17712123105837014271388637)
            ·
              refine ⟨6642046164688880351770739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17712123105837014271388637 6642046164688880351770739)
              ·
                refine ⟨9963069247033320527656109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6642046164688880351770739 9963069247033320527656109)
                ·
                  refine ⟨3736150967637495197871041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9963069247033320527656109 3736150967637495197871041)
                  ·
                    refine ⟨2802113225728121398403281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3736150967637495197871041 2802113225728121398403281)
                    ·
                      refine ⟨2101584919296091048802461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2802113225728121398403281 2101584919296091048802461)
                      ·
                        rfl

theorem cell23_4092822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_4092822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092822 prefixEnd_4092822 := by exact prefixLift 4092822
  have htrace : WordTrace (prefixWord ++ tailWord_4092822) baseStart_4092822 baseEnd_4092822 := by
    simpa [prefixWord, tailWord_4092822, baseEnd_4092822] using wordTrace_append hprefix tailTrace_4092822
  have hstable : (prefixWord ++ tailWord_4092822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092822).length < 2 ^ (prefixWord ++ tailWord_4092822).sum := by decide
  have hdescent : baseEnd_4092822 < baseStart_4092822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092847 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 3]
def baseStart_4092847 : Nat := 118140960795 + 4092847 * 2 ^ 59
def prefixEnd_4092847 : Nat := 4983230072969 + 3 ^ 40 * 4092847 * 2
def baseEnd_4092847 : Nat := 2101597756312453450989845

theorem tailTrace_4092847 : CollatzResearch.WordTrace tailWord_4092847 prefixEnd_4092847 2101597756312453450989845 := by
  unfold tailWord_4092847
  simp only [CollatzResearch.WordTrace]
  refine ⟨149278393803321796462268795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99518929202214530974845863 149278393803321796462268795)
  ·
    refine ⟨223917590704982694693403193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149278393803321796462268795 223917590704982694693403193)
    ·
      refine ⟨167938193028737021020052395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223917590704982694693403193 167938193028737021020052395)
      ·
        refine ⟨251907289543105531530078593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167938193028737021020052395 251907289543105531530078593)
        ·
          refine ⟨188930467157329148647558945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251907289543105531530078593 188930467157329148647558945)
          ·
            refine ⟨141697850367996861485669209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188930467157329148647558945 141697850367996861485669209)
            ·
              refine ⟨106273387775997646114251907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141697850367996861485669209 106273387775997646114251907)
              ·
                refine ⟨159410081663996469171377861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106273387775997646114251907 159410081663996469171377861)
                ·
                  refine ⟨29889390311999337969633349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159410081663996469171377861 29889390311999337969633349)
                  ·
                    refine ⟨5604260683499875869306253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29889390311999337969633349 5604260683499875869306253)
                    ·
                      refine ⟨2101597756312453450989845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5604260683499875869306253 2101597756312453450989845)
                      ·
                        rfl

theorem cell23_4092847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 3].length) (baseStart_4092847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092847 prefixEnd_4092847 := by exact prefixLift 4092847
  have htrace : WordTrace (prefixWord ++ tailWord_4092847) baseStart_4092847 baseEnd_4092847 := by
    simpa [prefixWord, tailWord_4092847, baseEnd_4092847] using wordTrace_append hprefix tailTrace_4092847
  have hstable : (prefixWord ++ tailWord_4092847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092847).length < 2 ^ (prefixWord ++ tailWord_4092847).sum := by decide
  have hdescent : baseEnd_4092847 < baseStart_4092847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092878 : List Nat := [4, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2]
def baseStart_4092878 : Nat := 118140960795 + 4092878 * 2 ^ 59
def prefixEnd_4092878 : Nat := 4983230072969 + 3 ^ 40 * 4092878 * 2
def baseEnd_4092878 : Nat := 2101613674212742829702203

theorem tailTrace_4092878 : CollatzResearch.WordTrace tailWord_4092878 prefixEnd_4092878 2101613674212742829702203 := by
  unfold tailWord_4092878
  simp only [CollatzResearch.WordTrace]
  refine ⟨18659940558276186094580911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99519682977472992504431525 18659940558276186094580911)
  ·
    refine ⟨27989910837414279141871367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18659940558276186094580911 27989910837414279141871367)
    ·
      refine ⟨41984866256121418712807051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27989910837414279141871367 41984866256121418712807051)
      ·
        refine ⟨62977299384182128069210577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41984866256121418712807051 62977299384182128069210577)
        ·
          refine ⟨47232974538136596051907933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62977299384182128069210577 47232974538136596051907933)
          ·
            refine ⟨17712365451801223519465475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47232974538136596051907933 17712365451801223519465475)
            ·
              refine ⟨26568548177701835279198213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17712365451801223519465475 26568548177701835279198213)
              ·
                refine ⟨4981602783319094114849665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26568548177701835279198213 4981602783319094114849665)
                ·
                  refine ⟨3736202087489320586137249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4981602783319094114849665 3736202087489320586137249)
                  ·
                    refine ⟨2802151565616990439602937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3736202087489320586137249 2802151565616990439602937)
                    ·
                      refine ⟨2101613674212742829702203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2802151565616990439602937 2101613674212742829702203)
                      ·
                        rfl

theorem cell23_4092878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_4092878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092878 prefixEnd_4092878 := by exact prefixLift 4092878
  have htrace : WordTrace (prefixWord ++ tailWord_4092878) baseStart_4092878 baseEnd_4092878 := by
    simpa [prefixWord, tailWord_4092878, baseEnd_4092878] using wordTrace_append hprefix tailTrace_4092878
  have hstable : (prefixWord ++ tailWord_4092878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092878).length < 2 ^ (prefixWord ++ tailWord_4092878).sum := by decide
  have hdescent : baseEnd_4092878 < baseStart_4092878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092897 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 1, 7]
def baseStart_4092897 : Nat := 118140960795 + 4092897 * 2 ^ 59
def prefixEnd_4092897 : Nat := 4983230072969 + 3 ^ 40 * 4092897 * 2
def baseEnd_4092897 : Nat := 700541143448392751788205

theorem tailTrace_4092897 : CollatzResearch.WordTrace tailWord_4092897 prefixEnd_4092897 700541143448392751788205 := by
  unfold tailWord_4092897
  simp only [CollatzResearch.WordTrace]
  refine ⟨149280217453140655001588945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99520144968760436667725963 149280217453140655001588945)
  ·
    refine ⟨111960163089855491251191709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149280217453140655001588945 111960163089855491251191709)
    ·
      refine ⟨41985061158695809219196891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111960163089855491251191709 41985061158695809219196891)
      ·
        refine ⟨62977591738043713828795337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41985061158695809219196891 62977591738043713828795337)
        ·
          refine ⟨47233193803532785371596503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62977591738043713828795337 47233193803532785371596503)
          ·
            refine ⟨70849790705299178057394755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47233193803532785371596503 70849790705299178057394755)
            ·
              refine ⟨106274686057948767086092133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70849790705299178057394755 106274686057948767086092133)
              ·
                refine ⟨19926503635865393828642275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106274686057948767086092133 19926503635865393828642275)
                ·
                  refine ⟨29889755453798090742963413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19926503635865393828642275 29889755453798090742963413)
                  ·
                    refine ⟨700541143448392751788205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29889755453798090742963413 700541143448392751788205)
                    ·
                      rfl

theorem cell23_4092897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_4092897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092897 prefixEnd_4092897 := by exact prefixLift 4092897
  have htrace : WordTrace (prefixWord ++ tailWord_4092897) baseStart_4092897 baseEnd_4092897 := by
    simpa [prefixWord, tailWord_4092897, baseEnd_4092897] using wordTrace_append hprefix tailTrace_4092897
  have hstable : (prefixWord ++ tailWord_4092897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092897).length < 2 ^ (prefixWord ++ tailWord_4092897).sum := by decide
  have hdescent : baseEnd_4092897 < baseStart_4092897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092901 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 7]
def baseStart_4092901 : Nat := 118140960795 + 4092901 * 2 ^ 59
def prefixEnd_4092901 : Nat := 4983230072969 + 3 ^ 40 * 4092901 * 2
def baseEnd_4092901 : Nat := 233513942696421804412733

theorem tailTrace_4092901 : CollatzResearch.WordTrace tailWord_4092901 prefixEnd_4092901 233513942696421804412733 := by
  unfold tailWord_4092901
  simp only [CollatzResearch.WordTrace]
  refine ⟨149280363345126163684734557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99520242230084109123156371 149280363345126163684734557)
  ·
    refine ⟨55980136254422311381775459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149280363345126163684734557 55980136254422311381775459)
    ·
      refine ⟨83970204381633467072663189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55980136254422311381775459 83970204381633467072663189)
      ·
        refine ⟨3936103330389068769031087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83970204381633467072663189 3936103330389068769031087)
        ·
          refine ⟨5904154995583603153546631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936103330389068769031087 5904154995583603153546631)
          ·
            refine ⟨8856232493375404730319947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5904154995583603153546631 8856232493375404730319947)
            ·
              refine ⟨13284348740063107095479921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8856232493375404730319947 13284348740063107095479921)
              ·
                refine ⟨9963261555047330321609941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13284348740063107095479921 9963261555047330321609941)
                ·
                  refine ⟨233513942696421804412733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9963261555047330321609941 233513942696421804412733)
                  ·
                    rfl

theorem cell23_4092901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 7].length) (baseStart_4092901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092901 prefixEnd_4092901 := by exact prefixLift 4092901
  have htrace : WordTrace (prefixWord ++ tailWord_4092901) baseStart_4092901 baseEnd_4092901 := by
    simpa [prefixWord, tailWord_4092901, baseEnd_4092901] using wordTrace_append hprefix tailTrace_4092901
  have hstable : (prefixWord ++ tailWord_4092901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092901).length < 2 ^ (prefixWord ++ tailWord_4092901).sum := by decide
  have hdescent : baseEnd_4092901 < baseStart_4092901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092918 : List Nat := [5, 1, 1, 1, 3, 2, 2, 3, 5]
def baseStart_4092918 : Nat := 118140960795 + 4092918 * 2 ^ 59
def prefixEnd_4092918 : Nat := 4983230072969 + 3 ^ 40 * 4092918 * 2
def baseEnd_4092918 : Nat := 233514912604324741466891

theorem tailTrace_4092918 : CollatzResearch.WordTrace tailWord_4092918 prefixEnd_4092918 233514912604324741466891 := by
  unfold tailWord_4092918
  simp only [CollatzResearch.WordTrace]
  refine ⟨9330061461629035974256463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99520655590709717058735605 9330061461629035974256463)
  ·
    refine ⟨13995092192443553961384695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9330061461629035974256463 13995092192443553961384695)
    ·
      refine ⟨20992638288665330942077043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13995092192443553961384695 20992638288665330942077043)
      ·
        refine ⟨31488957432997996413115565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20992638288665330942077043 31488957432997996413115565)
        ·
          refine ⟨11808359037374248654918337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31488957432997996413115565 11808359037374248654918337)
          ·
            refine ⟨8856269278030686491188753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11808359037374248654918337 8856269278030686491188753)
            ·
              refine ⟨6642201958523014868391565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8856269278030686491188753 6642201958523014868391565)
              ·
                refine ⟨2490825734446130575646837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6642201958523014868391565 2490825734446130575646837)
                ·
                  refine ⟨233514912604324741466891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2490825734446130575646837 233514912604324741466891)
                  ·
                    rfl

theorem cell23_4092918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_4092918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092918 prefixEnd_4092918 := by exact prefixLift 4092918
  have htrace : WordTrace (prefixWord ++ tailWord_4092918) baseStart_4092918 baseEnd_4092918 := by
    simpa [prefixWord, tailWord_4092918, baseEnd_4092918] using wordTrace_append hprefix tailTrace_4092918
  have hstable : (prefixWord ++ tailWord_4092918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092918).length < 2 ^ (prefixWord ++ tailWord_4092918).sum := by decide
  have hdescent : baseEnd_4092918 < baseStart_4092918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092937 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 2, 3, 5]
def baseStart_4092937 : Nat := 118140960795 + 4092937 * 2 ^ 59
def prefixEnd_4092937 : Nat := 4983230072969 + 3 ^ 40 * 4092937 * 2
def baseEnd_4092937 : Nat := 2101643969571358098864431

theorem tailTrace_4092937 : CollatzResearch.WordTrace tailWord_4092937 prefixEnd_4092937 2101643969571358098864431 := by
  unfold tailWord_4092937
  simp only [CollatzResearch.WordTrace]
  refine ⟨149281676372995741833045065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99521117581997161222030043 149281676372995741833045065)
  ·
    refine ⟨111961257279746806374783799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149281676372995741833045065 111961257279746806374783799)
    ·
      refine ⟨167941885919620209562175699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111961257279746806374783799 167941885919620209562175699)
      ·
        refine ⟨251912828879430314343263549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167941885919620209562175699 251912828879430314343263549)
        ·
          refine ⟨94467310829786367878723831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251912828879430314343263549 94467310829786367878723831)
          ·
            refine ⟨141700966244679551818085747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94467310829786367878723831 141700966244679551818085747)
            ·
              refine ⟨212551449367019327727128621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141700966244679551818085747 212551449367019327727128621)
              ·
                refine ⟨79706793512632247897673233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212551449367019327727128621 79706793512632247897673233)
                ·
                  refine ⟨59780095134474185923254925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79706793512632247897673233 59780095134474185923254925)
                  ·
                    refine ⟨22417535675427819721220597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59780095134474185923254925 22417535675427819721220597)
                    ·
                      refine ⟨2101643969571358098864431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22417535675427819721220597 2101643969571358098864431)
                      ·
                        rfl

theorem cell23_4092937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_4092937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092937 prefixEnd_4092937 := by exact prefixLift 4092937
  have htrace : WordTrace (prefixWord ++ tailWord_4092937) baseStart_4092937 baseEnd_4092937 := by
    simpa [prefixWord, tailWord_4092937, baseEnd_4092937] using wordTrace_append hprefix tailTrace_4092937
  have hstable : (prefixWord ++ tailWord_4092937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092937).length < 2 ^ (prefixWord ++ tailWord_4092937).sum := by decide
  have hdescent : baseEnd_4092937 < baseStart_4092937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092946 : List Nat := [3, 2, 5, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_4092946 : Nat := 118140960795 + 4092946 * 2 ^ 59
def prefixEnd_4092946 : Nat := 4983230072969 + 3 ^ 40 * 4092946 * 2
def baseEnd_4092946 : Nat := 2101648590897248563651891

theorem tailTrace_4092946 : CollatzResearch.WordTrace tailWord_4092946 prefixEnd_4092946 2101648590897248563651891 := by
  unfold tailWord_4092946
  simp only [CollatzResearch.WordTrace]
  refine ⟨37320501157490784092530673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99521336419975424246748461 37320501157490784092530673)
  ·
    refine ⟨27990375868118088069398005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37320501157490784092530673 27990375868118088069398005)
    ·
      refine ⟨2624097737636070756506063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27990375868118088069398005 2624097737636070756506063)
      ·
        refine ⟨3936146606454106134759095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2624097737636070756506063 3936146606454106134759095)
        ·
          refine ⟨5904219909681159202138643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936146606454106134759095 5904219909681159202138643)
          ·
            refine ⟨8856329864521738803207965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5904219909681159202138643 8856329864521738803207965)
            ·
              refine ⟨3321123699195652051202987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8856329864521738803207965 3321123699195652051202987)
              ·
                refine ⟨4981685548793478076804481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3321123699195652051202987 4981685548793478076804481)
                ·
                  refine ⟨3736264161595108557603361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4981685548793478076804481 3736264161595108557603361)
                  ·
                    refine ⟨2802198121196331418202521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3736264161595108557603361 2802198121196331418202521)
                    ·
                      refine ⟨2101648590897248563651891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2802198121196331418202521 2101648590897248563651891)
                      ·
                        rfl

theorem cell23_4092946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_4092946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092946 prefixEnd_4092946 := by exact prefixLift 4092946
  have htrace : WordTrace (prefixWord ++ tailWord_4092946) baseStart_4092946 baseEnd_4092946 := by
    simpa [prefixWord, tailWord_4092946, baseEnd_4092946] using wordTrace_append hprefix tailTrace_4092946
  have hstable : (prefixWord ++ tailWord_4092946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092946).length < 2 ^ (prefixWord ++ tailWord_4092946).sum := by decide
  have hdescent : baseEnd_4092946 < baseStart_4092946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092947 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 6]
def baseStart_4092947 : Nat := 118140960795 + 4092947 * 2 ^ 59
def prefixEnd_4092947 : Nat := 4983230072969 + 3 ^ 40 * 4092947 * 2
def baseEnd_4092947 : Nat := 2101649104377903059739385

theorem tailTrace_4092947 : CollatzResearch.WordTrace tailWord_4092947 prefixEnd_4092947 2101649104377903059739385 := by
  unfold tailWord_4092947
  simp only [CollatzResearch.WordTrace]
  refine ⟨149282041102959513540909095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99521360735306342360606063 149282041102959513540909095)
  ·
    refine ⟨223923061654439270311363643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149282041102959513540909095 223923061654439270311363643)
    ·
      refine ⟨335884592481658905467045465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223923061654439270311363643 335884592481658905467045465)
      ·
        refine ⟨251913444361244179100284099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335884592481658905467045465 251913444361244179100284099)
        ·
          refine ⟨377870166541866268650426149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251913444361244179100284099 377870166541866268650426149)
          ·
            refine ⟨70850656226599925371954903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 377870166541866268650426149 70850656226599925371954903)
            ·
              refine ⟨106275984339899888057932355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70850656226599925371954903 106275984339899888057932355)
              ·
                refine ⟨159413976509849832086898533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106275984339899888057932355 159413976509849832086898533)
                ·
                  refine ⟨29890120595596843516293475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159413976509849832086898533 29890120595596843516293475)
                  ·
                    refine ⟨44835180893395265274440213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29890120595596843516293475 44835180893395265274440213)
                    ·
                      refine ⟨2101649104377903059739385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44835180893395265274440213 2101649104377903059739385)
                      ·
                        rfl

theorem cell23_4092947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_4092947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092947 prefixEnd_4092947 := by exact prefixLift 4092947
  have htrace : WordTrace (prefixWord ++ tailWord_4092947) baseStart_4092947 baseEnd_4092947 := by
    simpa [prefixWord, tailWord_4092947, baseEnd_4092947] using wordTrace_append hprefix tailTrace_4092947
  have hstable : (prefixWord ++ tailWord_4092947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092947).length < 2 ^ (prefixWord ++ tailWord_4092947).sum := by decide
  have hdescent : baseEnd_4092947 < baseStart_4092947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092954 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3]
def baseStart_4092954 : Nat := 118140960795 + 4092954 * 2 ^ 59
def prefixEnd_4092954 : Nat := 4983230072969 + 3 ^ 40 * 4092954 * 2
def baseEnd_4092954 : Nat := 2101652698742484532351853

theorem tailTrace_4092954 : CollatzResearch.WordTrace tailWord_4092954 prefixEnd_4092954 2101652698742484532351853 := by
  unfold tailWord_4092954
  simp only [CollatzResearch.WordTrace]
  refine ⟨37320574103483538434103479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99521530942622769157609277 37320574103483538434103479)
  ·
    refine ⟨55980861155225307651155219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37320574103483538434103479 55980861155225307651155219)
    ·
      refine ⟨83971291732837961476732829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55980861155225307651155219 83971291732837961476732829)
      ·
        refine ⟨31489234399814235553774811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83971291732837961476732829 31489234399814235553774811)
        ·
          refine ⟨47233851599721353330662217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31489234399814235553774811 47233851599721353330662217)
          ·
            refine ⟨35425388699791014997996663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47233851599721353330662217 35425388699791014997996663)
            ·
              refine ⟨53138083049686522496994995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35425388699791014997996663 53138083049686522496994995)
              ·
                refine ⟨79707124574529783745492493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53138083049686522496994995 79707124574529783745492493)
                ·
                  refine ⟨29890171715448668904559685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79707124574529783745492493 29890171715448668904559685)
                  ·
                    refine ⟨5604407196646625419604941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29890171715448668904559685 5604407196646625419604941)
                    ·
                      refine ⟨2101652698742484532351853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5604407196646625419604941 2101652698742484532351853)
                      ·
                        rfl

theorem cell23_4092954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_4092954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092954 prefixEnd_4092954 := by exact prefixLift 4092954
  have htrace : WordTrace (prefixWord ++ tailWord_4092954) baseStart_4092954 baseEnd_4092954 := by
    simpa [prefixWord, tailWord_4092954, baseEnd_4092954] using wordTrace_append hprefix tailTrace_4092954
  have hstable : (prefixWord ++ tailWord_4092954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092954).length < 2 ^ (prefixWord ++ tailWord_4092954).sum := by decide
  have hdescent : baseEnd_4092954 < baseStart_4092954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092961 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 3, 4]
def baseStart_4092961 : Nat := 118140960795 + 4092961 * 2 ^ 59
def prefixEnd_4092961 : Nat := 4983230072969 + 3 ^ 40 * 4092961 * 2
def baseEnd_4092961 : Nat := 700552097702355334988107

theorem tailTrace_4092961 : CollatzResearch.WordTrace tailWord_4092961 prefixEnd_4092961 700552097702355334988107 := by
  unfold tailWord_4092961
  simp only [CollatzResearch.WordTrace]
  refine ⟨149282551724908793931918737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99521701149939195954612491 149282551724908793931918737)
  ·
    refine ⟨111961913793681595448939053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149282551724908793931918737 111961913793681595448939053)
    ·
      refine ⟨41985717672630598293352145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111961913793681595448939053 41985717672630598293352145)
      ·
        refine ⟨31489288254472948720014109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41985717672630598293352145 31489288254472948720014109)
        ·
          refine ⟨11808483095427355770005291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31489288254472948720014109 11808483095427355770005291)
          ·
            refine ⟨17712724643141033655007937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11808483095427355770005291 17712724643141033655007937)
            ·
              refine ⟨13284543482355775241255953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17712724643141033655007937 13284543482355775241255953)
              ·
                refine ⟨9963407611766831430941965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13284543482355775241255953 9963407611766831430941965)
                ·
                  refine ⟨3736277854412561786603237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9963407611766831430941965 3736277854412561786603237)
                  ·
                    refine ⟨700552097702355334988107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3736277854412561786603237 700552097702355334988107)
                    ·
                      rfl

theorem cell23_4092961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_4092961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092961 prefixEnd_4092961 := by exact prefixLift 4092961
  have htrace : WordTrace (prefixWord ++ tailWord_4092961) baseStart_4092961 baseEnd_4092961 := by
    simpa [prefixWord, tailWord_4092961, baseEnd_4092961] using wordTrace_append hprefix tailTrace_4092961
  have hstable : (prefixWord ++ tailWord_4092961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092961).length < 2 ^ (prefixWord ++ tailWord_4092961).sum := by decide
  have hdescent : baseEnd_4092961 < baseStart_4092961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092974 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 10]
def baseStart_4092974 : Nat := 118140960795 + 4092974 * 2 ^ 59
def prefixEnd_4092974 : Nat := 4983230072969 + 3 ^ 40 * 4092974 * 2
def baseEnd_4092974 : Nat := 233518107595063828233529

theorem tailTrace_4092974 : CollatzResearch.WordTrace tailWord_4092974 prefixEnd_4092974 233518107595063828233529 := by
  unfold tailWord_4092974
  simp only [CollatzResearch.WordTrace]
  refine ⟨18660378234232712144017747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99522017249241131434761317 18660378234232712144017747)
  ·
    refine ⟨27990567351349068216026621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18660378234232712144017747 27990567351349068216026621)
    ·
      refine ⟨10496462756755900581009983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27990567351349068216026621 10496462756755900581009983)
      ·
        refine ⟨15744694135133850871514975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10496462756755900581009983 15744694135133850871514975)
        ·
          refine ⟨23617041202700776307272463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15744694135133850871514975 23617041202700776307272463)
          ·
            refine ⟨35425561804051164460908695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23617041202700776307272463 35425561804051164460908695)
            ·
              refine ⟨53138342706076746691363043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35425561804051164460908695 53138342706076746691363043)
              ·
                refine ⟨79707514059115120037044565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53138342706076746691363043 79707514059115120037044565)
                ·
                  refine ⟨233518107595063828233529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 79707514059115120037044565 233518107595063828233529)
                  ·
                    rfl

theorem cell23_4092974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_4092974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092974 prefixEnd_4092974 := by exact prefixLift 4092974
  have htrace : WordTrace (prefixWord ++ tailWord_4092974) baseStart_4092974 baseEnd_4092974 := by
    simpa [prefixWord, tailWord_4092974, baseEnd_4092974] using wordTrace_append hprefix tailTrace_4092974
  have hstable : (prefixWord ++ tailWord_4092974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092974).length < 2 ^ (prefixWord ++ tailWord_4092974).sum := by decide
  have hdescent : baseEnd_4092974 < baseStart_4092974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093001 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 3, 1, 3]
def baseStart_4093001 : Nat := 118140960795 + 4093001 * 2 ^ 59
def prefixEnd_4093001 : Nat := 4983230072969 + 3 ^ 40 * 4093001 * 2
def baseEnd_4093001 : Nat := 2101676832333245848464137

theorem tailTrace_4093001 : CollatzResearch.WordTrace tailWord_4093001 prefixEnd_4093001 2101676832333245848464137 := by
  unfold tailWord_4093001
  simp only [CollatzResearch.WordTrace]
  refine ⟨149284010644763880763374857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99522673763175920508916571 149284010644763880763374857)
  ·
    refine ⟨111963007983572910572531143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149284010644763880763374857 111963007983572910572531143)
    ·
      refine ⟨167944511975359365858796715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111963007983572910572531143 167944511975359365858796715)
      ·
        refine ⟨251916767963039048788195073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167944511975359365858796715 251916767963039048788195073)
        ·
          refine ⟨188937575972279286591146305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251916767963039048788195073 188937575972279286591146305)
          ·
            refine ⟨141703181979209464943359729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188937575972279286591146305 141703181979209464943359729)
            ·
              refine ⟨106277386484407098707519797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141703181979209464943359729 106277386484407098707519797)
              ·
                refine ⟨9963504982913165503829981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106277386484407098707519797 9963504982913165503829981)
                ·
                  refine ⟨3736314368592437063936243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9963504982913165503829981 3736314368592437063936243)
                  ·
                    refine ⟨5604471552888655595904365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3736314368592437063936243 5604471552888655595904365)
                    ·
                      refine ⟨2101676832333245848464137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5604471552888655595904365 2101676832333245848464137)
                      ·
                        rfl

theorem cell23_4093001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 1, 3].length) (baseStart_4093001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093001 prefixEnd_4093001 := by exact prefixLift 4093001
  have htrace : WordTrace (prefixWord ++ tailWord_4093001) baseStart_4093001 baseEnd_4093001 := by
    simpa [prefixWord, tailWord_4093001, baseEnd_4093001] using wordTrace_append hprefix tailTrace_4093001
  have hstable : (prefixWord ++ tailWord_4093001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093001).length < 2 ^ (prefixWord ++ tailWord_4093001).sum := by decide
  have hdescent : baseEnd_4093001 < baseStart_4093001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093004 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 3, 5]
def baseStart_4093004 : Nat := 118140960795 + 4093004 * 2 ^ 59
def prefixEnd_4093004 : Nat := 4983230072969 + 3 ^ 40 * 4093004 * 2
def baseEnd_4093004 : Nat := 700559457591736445575541

theorem tailTrace_4093004 : CollatzResearch.WordTrace tailWord_4093004 prefixEnd_4093004 700559457591736445575541 := by
  unfold tailWord_4093004
  simp only [CollatzResearch.WordTrace]
  refine ⟨74642060031876506137867033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99522746709168674850489377 74642060031876506137867033)
  ·
    refine ⟨55981545023907379603400275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74642060031876506137867033 55981545023907379603400275)
    ·
      refine ⟨83972317535861069405100413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55981545023907379603400275 83972317535861069405100413)
      ·
        refine ⟨31489619075947901026912655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83972317535861069405100413 31489619075947901026912655)
        ·
          refine ⟨47234428613921851540368983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31489619075947901026912655 47234428613921851540368983)
          ·
            refine ⟨70851642920882777310553475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47234428613921851540368983 70851642920882777310553475)
            ·
              refine ⟨106277464381324165965830213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70851642920882777310553475 106277464381324165965830213)
              ·
                refine ⟨19927024571498281118593165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106277464381324165965830213 19927024571498281118593165)
                ·
                  refine ⟨7472634214311855419472437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19927024571498281118593165 7472634214311855419472437)
                  ·
                    refine ⟨700559457591736445575541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7472634214311855419472437 700559457591736445575541)
                    ·
                      rfl

theorem cell23_4093004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_4093004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093004 prefixEnd_4093004 := by exact prefixLift 4093004
  have htrace : WordTrace (prefixWord ++ tailWord_4093004) baseStart_4093004 baseEnd_4093004 := by
    simpa [prefixWord, tailWord_4093004, baseEnd_4093004] using wordTrace_append hprefix tailTrace_4093004
  have hstable : (prefixWord ++ tailWord_4093004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093004).length < 2 ^ (prefixWord ++ tailWord_4093004).sum := by decide
  have hdescent : baseEnd_4093004 < baseStart_4093004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093022 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_4093022 : Nat := 118140960795 + 4093022 * 2 ^ 59
def prefixEnd_4093022 : Nat := 4983230072969 + 3 ^ 40 * 4093022 * 2
def baseEnd_4093022 : Nat := 2101687615426990266301541

theorem tailTrace_4093022 : CollatzResearch.WordTrace tailWord_4093022 prefixEnd_4093022 2101687615426990266301541 := by
  unfold tailWord_4093022
  simp only [CollatzResearch.WordTrace]
  refine ⟨18660597072210975168736165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99523184385125200899926213 18660597072210975168736165)
  ·
    refine ⟨3498861951039557844138031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18660597072210975168736165 3498861951039557844138031)
    ·
      refine ⟨5248292926559336766207047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3498861951039557844138031 5248292926559336766207047)
      ·
        refine ⟨7872439389839005149310571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5248292926559336766207047 7872439389839005149310571)
        ·
          refine ⟨11808659084758507723965857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7872439389839005149310571 11808659084758507723965857)
          ·
            refine ⟨8856494313568880792974393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11808659084758507723965857 8856494313568880792974393)
            ·
              refine ⟨6642370735176660594730795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8856494313568880792974393 6642370735176660594730795)
              ·
                refine ⟨9963556102764990892096193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6642370735176660594730795 9963556102764990892096193)
                ·
                  refine ⟨7472667077073743169072145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9963556102764990892096193 7472667077073743169072145)
                  ·
                    refine ⟨5604500307805307376804109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7472667077073743169072145 5604500307805307376804109)
                    ·
                      refine ⟨2101687615426990266301541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5604500307805307376804109 2101687615426990266301541)
                      ·
                        rfl

theorem cell23_4093022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_4093022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093022 prefixEnd_4093022 := by exact prefixLift 4093022
  have htrace : WordTrace (prefixWord ++ tailWord_4093022) baseStart_4093022 baseEnd_4093022 := by
    simpa [prefixWord, tailWord_4093022, baseEnd_4093022] using wordTrace_append hprefix tailTrace_4093022
  have hstable : (prefixWord ++ tailWord_4093022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093022).length < 2 ^ (prefixWord ++ tailWord_4093022).sum := by decide
  have hdescent : baseEnd_4093022 < baseStart_4093022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093092 : List Nat := [2, 3, 1, 2, 3, 1, 1, 5, 1, 2, 2]
def baseStart_4093092 : Nat := 118140960795 + 4093092 * 2 ^ 59
def prefixEnd_4093092 : Nat := 4983230072969 + 3 ^ 40 * 4093092 * 2
def baseEnd_4093092 : Nat := 2101723559072804992426219

theorem tailTrace_4093092 : CollatzResearch.WordTrace tailWord_4093092 prefixEnd_4093092 2101723559072804992426219 := by
  unfold tailWord_4093092
  simp only [CollatzResearch.WordTrace]
  refine ⟨74643664843717101652468765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99524886458289468869958353 74643664843717101652468765)
  ·
    refine ⟨27991374316393913119675787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74643664843717101652468765 27991374316393913119675787)
    ·
      refine ⟨41987061474590869679513681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27991374316393913119675787 41987061474590869679513681)
      ·
        refine ⟨31490296105943152259635261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41987061474590869679513681 31490296105943152259635261)
        ·
          refine ⟨11808861039728682097363223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31490296105943152259635261 11808861039728682097363223)
          ·
            refine ⟨17713291559593023146044835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11808861039728682097363223 17713291559593023146044835)
            ·
              refine ⟨26569937339389534719067253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17713291559593023146044835 26569937339389534719067253)
              ·
                refine ⟨2490931625567768879912555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26569937339389534719067253 2490931625567768879912555)
                ·
                  refine ⟨3736397438351653319868833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2490931625567768879912555 3736397438351653319868833)
                  ·
                    refine ⟨2802298078763739989901625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3736397438351653319868833 2802298078763739989901625)
                    ·
                      refine ⟨2101723559072804992426219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2802298078763739989901625 2101723559072804992426219)
                      ·
                        rfl

theorem cell23_4093092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_4093092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093092 prefixEnd_4093092 := by exact prefixLift 4093092
  have htrace : WordTrace (prefixWord ++ tailWord_4093092) baseStart_4093092 baseEnd_4093092 := by
    simpa [prefixWord, tailWord_4093092, baseEnd_4093092] using wordTrace_append hprefix tailTrace_4093092
  have hstable : (prefixWord ++ tailWord_4093092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093092).length < 2 ^ (prefixWord ++ tailWord_4093092).sum := by decide
  have hdescent : baseEnd_4093092 < baseStart_4093092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093095 : List Nat := [1, 1, 6, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_4093095 : Nat := 118140960795 + 4093095 * 2 ^ 59
def prefixEnd_4093095 : Nat := 4983230072969 + 3 ^ 40 * 4093095 * 2
def baseEnd_4093095 : Nat := 2101725099514768480688705

theorem tailTrace_4093095 : CollatzResearch.WordTrace tailWord_4093095 prefixEnd_4093095 2101725099514768480688705 := by
  unfold tailWord_4093095
  simp only [CollatzResearch.WordTrace]
  refine ⟨149287439106423334817296739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99524959404282223211531159 149287439106423334817296739)
  ·
    refine ⟨223931158659635002225945109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149287439106423334817296739 223931158659635002225945109)
    ·
      refine ⟨10496773062170390729341177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 223931158659635002225945109 10496773062170390729341177)
      ·
        refine ⟨7872579796627793047005883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10496773062170390729341177 7872579796627793047005883)
        ·
          refine ⟨11808869694941689570508825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7872579796627793047005883 11808869694941689570508825)
          ·
            refine ⟨8856652271206267177881619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11808869694941689570508825 8856652271206267177881619)
            ·
              refine ⟨13284978406809400766822429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8856652271206267177881619 13284978406809400766822429)
              ·
                refine ⟨4981866902553525287558411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13284978406809400766822429 4981866902553525287558411)
                ·
                  refine ⟨7472800353830287931337617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4981866902553525287558411 7472800353830287931337617)
                  ·
                    refine ⟨5604600265372715948503213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7472800353830287931337617 5604600265372715948503213)
                    ·
                      refine ⟨2101725099514768480688705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5604600265372715948503213 2101725099514768480688705)
                      ·
                        rfl

theorem cell23_4093095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_4093095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093095 prefixEnd_4093095 := by exact prefixLift 4093095
  have htrace : WordTrace (prefixWord ++ tailWord_4093095) baseStart_4093095 baseEnd_4093095 := by
    simpa [prefixWord, tailWord_4093095, baseEnd_4093095] using wordTrace_append hprefix tailTrace_4093095
  have hstable : (prefixWord ++ tailWord_4093095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093095).length < 2 ^ (prefixWord ++ tailWord_4093095).sum := by decide
  have hdescent : baseEnd_4093095 < baseStart_4093095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093104 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 5]
def baseStart_4093104 : Nat := 118140960795 + 4093104 * 2 ^ 59
def prefixEnd_4093104 : Nat := 4983230072969 + 3 ^ 40 * 4093104 * 2
def baseEnd_4093104 : Nat := 2101729720840658945476163

theorem tailTrace_4093104 : CollatzResearch.WordTrace tailWord_4093104 prefixEnd_4093104 2101729720840658945476163 := by
  unfold tailWord_4093104
  simp only [CollatzResearch.WordTrace]
  refine ⟨74643883681695364677187183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99525178242260486236249577 74643883681695364677187183)
  ·
    refine ⟨111965825522543047015780775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74643883681695364677187183 111965825522543047015780775)
    ·
      refine ⟨167948738283814570523671163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111965825522543047015780775 167948738283814570523671163)
      ·
        refine ⟨251923107425721855785506745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167948738283814570523671163 251923107425721855785506745)
        ·
          refine ⟨188942330569291391839130059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251923107425721855785506745 188942330569291391839130059)
          ·
            refine ⟨283413495853937087758695089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188942330569291391839130059 283413495853937087758695089)
            ·
              refine ⟨212560121890452815819021317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283413495853937087758695089 212560121890452815819021317)
              ·
                refine ⟨39855022854459902966066497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212560121890452815819021317 39855022854459902966066497)
                ·
                  refine ⟨29891267140844927224549873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39855022854459902966066497 29891267140844927224549873)
                  ·
                    refine ⟨22418450355633695418412405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29891267140844927224549873 22418450355633695418412405)
                    ·
                      refine ⟨2101729720840658945476163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22418450355633695418412405 2101729720840658945476163)
                      ·
                        rfl

theorem cell23_4093104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_4093104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093104 prefixEnd_4093104 := by exact prefixLift 4093104
  have htrace : WordTrace (prefixWord ++ tailWord_4093104) baseStart_4093104 baseEnd_4093104 := by
    simpa [prefixWord, tailWord_4093104, baseEnd_4093104] using wordTrace_append hprefix tailTrace_4093104
  have hstable : (prefixWord ++ tailWord_4093104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093104).length < 2 ^ (prefixWord ++ tailWord_4093104).sum := by decide
  have hdescent : baseEnd_4093104 < baseStart_4093104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093171 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 7]
def baseStart_4093171 : Nat := 118140960795 + 4093171 * 2 ^ 59
def prefixEnd_4093171 : Nat := 4983230072969 + 3 ^ 40 * 4093171 * 2
def baseEnd_4093171 : Nat := 233529347116056687037595

theorem tailTrace_4093171 : CollatzResearch.WordTrace tailWord_4093171 prefixEnd_4093171 233529347116056687037595 := by
  unfold tailWord_4093171
  simp only [CollatzResearch.WordTrace]
  refine ⟨149290211054147999797063367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99526807369431999864708911 149290211054147999797063367)
  ·
    refine ⟨223935316581221999695595051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149290211054147999797063367 223935316581221999695595051)
    ·
      refine ⟨335902974871832999543392577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223935316581221999695595051 335902974871832999543392577)
      ·
        refine ⟨251927231153874749657544433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335902974871832999543392577 251927231153874749657544433)
        ·
          refine ⟨188945423365406062243158325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251927231153874749657544433 188945423365406062243158325)
          ·
            refine ⟨17713633440506818335296093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188945423365406062243158325 17713633440506818335296093)
            ·
              refine ⟨6642612540190056875736035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17713633440506818335296093 6642612540190056875736035)
              ·
                refine ⟨9963918810285085313604053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6642612540190056875736035 9963918810285085313604053)
                ·
                  refine ⟨233529347116056687037595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9963918810285085313604053 233529347116056687037595)
                  ·
                    rfl

theorem cell23_4093171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 7].length) (baseStart_4093171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093171 prefixEnd_4093171 := by exact prefixLift 4093171
  have htrace : WordTrace (prefixWord ++ tailWord_4093171) baseStart_4093171 baseEnd_4093171 := by
    simpa [prefixWord, tailWord_4093171, baseEnd_4093171] using wordTrace_append hprefix tailTrace_4093171
  have hstable : (prefixWord ++ tailWord_4093171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093171).length < 2 ^ (prefixWord ++ tailWord_4093171).sum := by decide
  have hdescent : baseEnd_4093171 < baseStart_4093171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093186 : List Nat := [3, 4, 1, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_4093186 : Nat := 118140960795 + 4093186 * 2 ^ 59
def prefixEnd_4093186 : Nat := 4983230072969 + 3 ^ 40 * 4093186 * 2
def baseEnd_4093186 : Nat := 2101771826254327624650787

theorem tailTrace_4093186 : CollatzResearch.WordTrace tailWord_4093186 prefixEnd_4093186 2101771826254327624650787 := by
  unfold tailWord_4093186
  simp only [CollatzResearch.WordTrace]
  refine ⟨37322689537273414339714853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99527172099395771572572941 37322689537273414339714853)
  ·
    refine ⟨6998004288238765188696535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37322689537273414339714853 6998004288238765188696535)
    ·
      refine ⟨10497006432358147783044803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6998004288238765188696535 10497006432358147783044803)
      ·
        refine ⟨15745509648537221674567205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10497006432358147783044803 15745509648537221674567205)
        ·
          refine ⟨2952283059100729063981351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15745509648537221674567205 2952283059100729063981351)
          ·
            refine ⟨4428424588651093595972027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2952283059100729063981351 4428424588651093595972027)
            ·
              refine ⟨6642636882976640393958041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4428424588651093595972027 6642636882976640393958041)
              ·
                refine ⟨4981977662232480295468531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6642636882976640393958041 4981977662232480295468531)
                ·
                  refine ⟨7472966493348720443202797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4981977662232480295468531 7472966493348720443202797)
                  ·
                    refine ⟨2802362435005770166201049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7472966493348720443202797 2802362435005770166201049)
                    ·
                      refine ⟨2101771826254327624650787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2802362435005770166201049 2101771826254327624650787)
                      ·
                        rfl

theorem cell23_4093186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_4093186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093186 prefixEnd_4093186 := by exact prefixLift 4093186
  have htrace : WordTrace (prefixWord ++ tailWord_4093186) baseStart_4093186 baseEnd_4093186 := by
    simpa [prefixWord, tailWord_4093186, baseEnd_4093186] using wordTrace_append hprefix tailTrace_4093186
  have hstable : (prefixWord ++ tailWord_4093186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093186).length < 2 ^ (prefixWord ++ tailWord_4093186).sum := by decide
  have hdescent : baseEnd_4093186 < baseStart_4093186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093248 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 3, 4]
def baseStart_4093248 : Nat := 118140960795 + 4093248 * 2 ^ 59
def prefixEnd_4093248 : Nat := 4983230072969 + 3 ^ 40 * 4093248 * 2
def baseEnd_4093248 : Nat := 700601220684968794025167

theorem tailTrace_4093248 : CollatzResearch.WordTrace tailWord_4093248 prefixEnd_4093248 700601220684968794025167 := by
  unfold tailWord_4093248
  simp only [CollatzResearch.WordTrace]
  refine ⟨74646509737434520973808199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99528679649912694631744265 74646509737434520973808199)
  ·
    refine ⟨111969764606151781460712299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74646509737434520973808199 111969764606151781460712299)
    ·
      refine ⟨167954646909227672191068449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111969764606151781460712299 167954646909227672191068449)
      ·
        refine ⟨125965985181920754143301337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167954646909227672191068449 125965985181920754143301337)
        ·
          refine ⟨94474488886440565607476003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125965985181920754143301337 94474488886440565607476003)
          ·
            refine ⟨141711733329660848411214005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94474488886440565607476003 141711733329660848411214005)
            ·
              refine ⟨13285474999655704538551313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141711733329660848411214005 13285474999655704538551313)
              ·
                refine ⟨9964106249741778403913485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13285474999655704538551313 9964106249741778403913485)
                ·
                  refine ⟨3736539843653166901467557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9964106249741778403913485 3736539843653166901467557)
                  ·
                    refine ⟨700601220684968794025167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3736539843653166901467557 700601220684968794025167)
                    ·
                      rfl

theorem cell23_4093248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 3, 4].length) (baseStart_4093248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093248 prefixEnd_4093248 := by exact prefixLift 4093248
  have htrace : WordTrace (prefixWord ++ tailWord_4093248) baseStart_4093248 baseEnd_4093248 := by
    simpa [prefixWord, tailWord_4093248, baseEnd_4093248] using wordTrace_append hprefix tailTrace_4093248
  have hstable : (prefixWord ++ tailWord_4093248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093248).length < 2 ^ (prefixWord ++ tailWord_4093248).sum := by decide
  have hdescent : baseEnd_4093248 < baseStart_4093248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093252 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 2, 5]
def baseStart_4093252 : Nat := 118140960795 + 4093252 * 2 ^ 59
def prefixEnd_4093252 : Nat := 4983230072969 + 3 ^ 40 * 4093252 * 2
def baseEnd_4093252 : Nat := 700601905325841455475161

theorem tailTrace_4093252 : CollatzResearch.WordTrace tailWord_4093252 prefixEnd_4093252 700601905325841455475161 := by
  unfold tailWord_4093252
  simp only [CollatzResearch.WordTrace]
  refine ⟨74646582683427275315381005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99528776911236367087174673 74646582683427275315381005)
  ·
    refine ⟨27992468506285228243267877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74646582683427275315381005 27992468506285228243267877)
    ·
      refine ⟨5248587844928480295612727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27992468506285228243267877 5248587844928480295612727)
      ·
        refine ⟨7872881767392720443419091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5248587844928480295612727 7872881767392720443419091)
        ·
          refine ⟨11809322651089080665128637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7872881767392720443419091 11809322651089080665128637)
          ·
            refine ⟨4428495994158405249423239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11809322651089080665128637 4428495994158405249423239)
            ·
              refine ⟨6642743991237607874134859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4428495994158405249423239 6642743991237607874134859)
              ·
                refine ⟨9964115986856411811202289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6642743991237607874134859 9964115986856411811202289)
                ·
                  refine ⟨7473086990142308858401717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9964115986856411811202289 7473086990142308858401717)
                  ·
                    refine ⟨700601905325841455475161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7473086990142308858401717 700601905325841455475161)
                    ·
                      rfl

theorem cell23_4093252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_4093252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093252 prefixEnd_4093252 := by exact prefixLift 4093252
  have htrace : WordTrace (prefixWord ++ tailWord_4093252) baseStart_4093252 baseEnd_4093252 := by
    simpa [prefixWord, tailWord_4093252, baseEnd_4093252] using wordTrace_append hprefix tailTrace_4093252
  have hstable : (prefixWord ++ tailWord_4093252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093252).length < 2 ^ (prefixWord ++ tailWord_4093252).sum := by decide
  have hdescent : baseEnd_4093252 < baseStart_4093252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093255 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 2, 1, 4]
def baseStart_4093255 : Nat := 118140960795 + 4093255 * 2 ^ 59
def prefixEnd_4093255 : Nat := 4983230072969 + 3 ^ 40 * 4093255 * 2
def baseEnd_4093255 : Nat := 2101807256419487854687969

theorem tailTrace_4093255 : CollatzResearch.WordTrace tailWord_4093255 prefixEnd_4093255 2101807256419487854687969 := by
  unfold tailWord_4093255
  simp only [CollatzResearch.WordTrace]
  refine ⟨149293274785843682143121219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99528849857229121428747479 149293274785843682143121219)
  ·
    refine ⟨223939912178765523214681829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149293274785843682143121219 223939912178765523214681829)
    ·
      refine ⟨41988733533518535602752843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223939912178765523214681829 41988733533518535602752843)
      ·
        refine ⟨62983100300277803404129265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41988733533518535602752843 62983100300277803404129265)
        ·
          refine ⟨47237325225208352553096949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62983100300277803404129265 47237325225208352553096949)
          ·
            refine ⟨4428499239863283051852839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47237325225208352553096949 4428499239863283051852839)
            ·
              refine ⟨6642748859794924577779259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4428499239863283051852839 6642748859794924577779259)
              ·
                refine ⟨9964123289692386866668889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6642748859794924577779259 9964123289692386866668889)
                ·
                  refine ⟨7473092467269290150001667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9964123289692386866668889 7473092467269290150001667)
                  ·
                    refine ⟨11209638700903935225002501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7473092467269290150001667 11209638700903935225002501)
                    ·
                      refine ⟨2101807256419487854687969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11209638700903935225002501 2101807256419487854687969)
                      ·
                        rfl

theorem cell23_4093255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_4093255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093255 prefixEnd_4093255 := by exact prefixLift 4093255
  have htrace : WordTrace (prefixWord ++ tailWord_4093255) baseStart_4093255 baseEnd_4093255 := by
    simpa [prefixWord, tailWord_4093255, baseEnd_4093255] using wordTrace_append hprefix tailTrace_4093255
  have hstable : (prefixWord ++ tailWord_4093255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093255).length < 2 ^ (prefixWord ++ tailWord_4093255).sum := by decide
  have hdescent : baseEnd_4093255 < baseStart_4093255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093282 : List Nat := [3, 3, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_4093282 : Nat := 118140960795 + 4093282 * 2 ^ 59
def prefixEnd_4093282 : Nat := 4983230072969 + 3 ^ 40 * 4093282 * 2
def baseEnd_4093282 : Nat := 700607040132386416350115

theorem tailTrace_4093282 : CollatzResearch.WordTrace tailWord_4093282 prefixEnd_4093282 700607040132386416350115 := by
  unfold tailWord_4093282
  simp only [CollatzResearch.WordTrace]
  refine ⟨37323564889186466438588525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99529506371163910502902733 37323564889186466438588525)
  ·
    refine ⟨13996336833444924914470697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37323564889186466438588525 13996336833444924914470697)
    ·
      refine ⟨10497252625083693685853023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13996336833444924914470697 10497252625083693685853023)
      ·
        refine ⟨15745878937625540528779535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10497252625083693685853023 15745878937625540528779535)
        ·
          refine ⟨23618818406438310793169303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15745878937625540528779535 23618818406438310793169303)
          ·
            refine ⟨35428227609657466189753955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23618818406438310793169303 35428227609657466189753955)
            ·
              refine ⟨53142341414486199284630933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35428227609657466189753955 53142341414486199284630933)
              ·
                refine ⟨2491047253804040591467075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53142341414486199284630933 2491047253804040591467075)
                ·
                  refine ⟨3736570880706060887200613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491047253804040591467075 3736570880706060887200613)
                  ·
                    refine ⟨700607040132386416350115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3736570880706060887200613 700607040132386416350115)
                    ·
                      rfl

theorem cell23_4093282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_4093282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093282 prefixEnd_4093282 := by exact prefixLift 4093282
  have htrace : WordTrace (prefixWord ++ tailWord_4093282) baseStart_4093282 baseEnd_4093282 := by
    simpa [prefixWord, tailWord_4093282, baseEnd_4093282] using wordTrace_append hprefix tailTrace_4093282
  have hstable : (prefixWord ++ tailWord_4093282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093282).length < 2 ^ (prefixWord ++ tailWord_4093282).sum := by decide
  have hdescent : baseEnd_4093282 < baseStart_4093282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093305 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 3, 1, 3]
def baseStart_4093305 : Nat := 118140960795 + 4093305 * 2 ^ 59
def prefixEnd_4093305 : Nat := 4983230072969 + 3 ^ 40 * 4093305 * 2
def baseEnd_4093305 : Nat := 2101832930452212659062739

theorem tailTrace_4093305 : CollatzResearch.WordTrace tailWord_4093305 prefixEnd_4093305 2101832930452212659062739 := by
  unfold tailWord_4093305
  simp only [CollatzResearch.WordTrace]
  refine ⟨149295098435662540682441369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99530065623775027121627579 149295098435662540682441369)
  ·
    refine ⟨111971323826746905511831027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149295098435662540682441369 111971323826746905511831027)
    ·
      refine ⟨167956985740120358267746541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111971323826746905511831027 167956985740120358267746541)
      ·
        refine ⟨62983869652545134350404953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167956985740120358267746541 62983869652545134350404953)
        ·
          refine ⟨47237902239408850762803715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62983869652545134350404953 47237902239408850762803715)
          ·
            refine ⟨70856853359113276144205573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47237902239408850762803715 70856853359113276144205573)
            ·
              refine ⟨13285660004833739277038545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70856853359113276144205573 13285660004833739277038545)
              ·
                refine ⟨9964245003625304457778909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13285660004833739277038545 9964245003625304457778909)
                ·
                  refine ⟨3736591876359489171667091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9964245003625304457778909 3736591876359489171667091)
                  ·
                    refine ⟨5604887814539233757500637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3736591876359489171667091 5604887814539233757500637)
                    ·
                      refine ⟨2101832930452212659062739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5604887814539233757500637 2101832930452212659062739)
                      ·
                        rfl

theorem cell23_4093305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_4093305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093305 prefixEnd_4093305 := by exact prefixLift 4093305
  have htrace : WordTrace (prefixWord ++ tailWord_4093305) baseStart_4093305 baseEnd_4093305 := by
    simpa [prefixWord, tailWord_4093305, baseEnd_4093305] using wordTrace_append hprefix tailTrace_4093305
  have hstable : (prefixWord ++ tailWord_4093305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093305).length < 2 ^ (prefixWord ++ tailWord_4093305).sum := by decide
  have hdescent : baseEnd_4093305 < baseStart_4093305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093315 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 1, 5, 2]
def baseStart_4093315 : Nat := 118140960795 + 4093315 * 2 ^ 59
def prefixEnd_4093315 : Nat := 4983230072969 + 3 ^ 40 * 4093315 * 2
def baseEnd_4093315 : Nat := 2101838065258757619937693

theorem tailTrace_4093315 : CollatzResearch.WordTrace tailWord_4093315 prefixEnd_4093315 2101838065258757619937693 := by
  unfold tailWord_4093315
  simp only [CollatzResearch.WordTrace]
  refine ⟨149295463165626312390305399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99530308777084208260203599 149295463165626312390305399)
  ·
    refine ⟨223943194748439468585458099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149295463165626312390305399 223943194748439468585458099)
    ·
      refine ⟨335914792122659202878187149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223943194748439468585458099 335914792122659202878187149)
      ·
        refine ⟨125968047045997201079320181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335914792122659202878187149 125968047045997201079320181)
        ·
          refine ⟨11809504410562237601186267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125968047045997201079320181 11809504410562237601186267)
          ·
            refine ⟨17714256615843356401779401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11809504410562237601186267 17714256615843356401779401)
            ·
              refine ⟨13285692461882517301334551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17714256615843356401779401 13285692461882517301334551)
              ·
                refine ⟨19928538692823775952001827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13285692461882517301334551 19928538692823775952001827)
                ·
                  refine ⟨29892808039235663928002741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19928538692823775952001827 29892808039235663928002741)
                  ·
                    refine ⟨2802450753678343493250257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29892808039235663928002741 2802450753678343493250257)
                    ·
                      refine ⟨2101838065258757619937693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2802450753678343493250257 2101838065258757619937693)
                      ·
                        rfl

theorem cell23_4093315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 5, 2].length) (baseStart_4093315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093315 prefixEnd_4093315 := by exact prefixLift 4093315
  have htrace : WordTrace (prefixWord ++ tailWord_4093315) baseStart_4093315 baseEnd_4093315 := by
    simpa [prefixWord, tailWord_4093315, baseEnd_4093315] using wordTrace_append hprefix tailTrace_4093315
  have hstable : (prefixWord ++ tailWord_4093315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093315).length < 2 ^ (prefixWord ++ tailWord_4093315).sum := by decide
  have hdescent : baseEnd_4093315 < baseStart_4093315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093332 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_4093332 : Nat := 118140960795 + 4093332 * 2 ^ 59
def prefixEnd_4093332 : Nat := 4983230072969 + 3 ^ 40 * 4093332 * 2
def baseEnd_4093332 : Nat := 2101846794429884053425115

theorem tailTrace_4093332 : CollatzResearch.WordTrace tailWord_4093332 prefixEnd_4093332 2101846794429884053425115 := by
  unfold tailWord_4093332
  simp only [CollatzResearch.WordTrace]
  refine ⟨74648041603282362146837125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99530722137709816195782833 74648041603282362146837125)
  ·
    refine ⟨13996507800615442902531961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74648041603282362146837125 13996507800615442902531961)
    ·
      refine ⟨10497380850461582176898971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13996507800615442902531961 10497380850461582176898971)
      ·
        refine ⟨15746071275692373265348457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10497380850461582176898971 15746071275692373265348457)
        ·
          refine ⟨11809553456769279949011343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15746071275692373265348457 11809553456769279949011343)
          ·
            refine ⟨17714330185153919923517015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11809553456769279949011343 17714330185153919923517015)
            ·
              refine ⟨26571495277730879885275523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17714330185153919923517015 26571495277730879885275523)
              ·
                refine ⟨39857242916596319827913285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26571495277730879885275523 39857242916596319827913285)
                ·
                  refine ⟨7473233046861809967733741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39857242916596319827913285 7473233046861809967733741)
                  ·
                    refine ⟨2802462392573178737900153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7473233046861809967733741 2802462392573178737900153)
                    ·
                      refine ⟨2101846794429884053425115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2802462392573178737900153 2101846794429884053425115)
                      ·
                        rfl

theorem cell23_4093332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_4093332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093332 prefixEnd_4093332 := by exact prefixLift 4093332
  have htrace : WordTrace (prefixWord ++ tailWord_4093332) baseStart_4093332 baseEnd_4093332 := by
    simpa [prefixWord, tailWord_4093332, baseEnd_4093332] using wordTrace_append hprefix tailTrace_4093332
  have hstable : (prefixWord ++ tailWord_4093332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093332).length < 2 ^ (prefixWord ++ tailWord_4093332).sum := by decide
  have hdescent : baseEnd_4093332 < baseStart_4093332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093348 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 2, 6, 3]
def baseStart_4093348 : Nat := 118140960795 + 4093348 * 2 ^ 59
def prefixEnd_4093348 : Nat := 4983230072969 + 3 ^ 40 * 4093348 * 2
def baseEnd_4093348 : Nat := 2101855010120355990825041

theorem tailTrace_4093348 : CollatzResearch.WordTrace tailWord_4093348 prefixEnd_4093348 2101855010120355990825041 := by
  unfold tailWord_4093348
  simp only [CollatzResearch.WordTrace]
  refine ⟨74648333387253379513128349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99531111183004506017504465 74648333387253379513128349)
  ·
    refine ⟨27993125020220017317423131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74648333387253379513128349 27993125020220017317423131)
    ·
      refine ⟨41989687530330025976134697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27993125020220017317423131 41989687530330025976134697)
      ·
        refine ⟨31492265647747519482101023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41989687530330025976134697 31492265647747519482101023)
        ·
          refine ⟨47238398471621279223151535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31492265647747519482101023 47238398471621279223151535)
          ·
            refine ⟨70857597707431918834727303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47238398471621279223151535 70857597707431918834727303)
            ·
              refine ⟨106286396561147878252090955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70857597707431918834727303 106286396561147878252090955)
              ·
                refine ⟨159429594841721817378136433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106286396561147878252090955 159429594841721817378136433)
                ·
                  refine ⟨119572196131291363033602325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159429594841721817378136433 119572196131291363033602325)
                  ·
                    refine ⟨5604946693654282642200109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119572196131291363033602325 5604946693654282642200109)
                    ·
                      refine ⟨2101855010120355990825041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5604946693654282642200109 2101855010120355990825041)
                      ·
                        rfl

theorem cell23_4093348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_4093348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093348 prefixEnd_4093348 := by exact prefixLift 4093348
  have htrace : WordTrace (prefixWord ++ tailWord_4093348) baseStart_4093348 baseEnd_4093348 := by
    simpa [prefixWord, tailWord_4093348, baseEnd_4093348] using wordTrace_append hprefix tailTrace_4093348
  have hstable : (prefixWord ++ tailWord_4093348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093348).length < 2 ^ (prefixWord ++ tailWord_4093348).sum := by decide
  have hdescent : baseEnd_4093348 < baseStart_4093348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093422 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 3, 3, 2]
def baseStart_4093422 : Nat := 118140960795 + 4093422 * 2 ^ 59
def prefixEnd_4093422 : Nat := 4983230072969 + 3 ^ 40 * 4093422 * 2
def baseEnd_4093422 : Nat := 2101893007688788701299701

theorem tailTrace_4093422 : CollatzResearch.WordTrace tailWord_4093422 prefixEnd_4093422 2101893007688788701299701 := by
  unfold tailWord_4093422
  simp only [CollatzResearch.WordTrace]
  refine ⟨18662420722029833708056315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99532910517492446442967013 18662420722029833708056315)
  ·
    refine ⟨27993631083044750562084473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18662420722029833708056315 27993631083044750562084473)
    ·
      refine ⟨20995223312283562921563355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27993631083044750562084473 20995223312283562921563355)
      ·
        refine ⟨31492834968425344382345033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20995223312283562921563355 31492834968425344382345033)
        ·
          refine ⟨23619626226319008286758775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31492834968425344382345033 23619626226319008286758775)
          ·
            refine ⟨35429439339478512430138163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23619626226319008286758775 35429439339478512430138163)
            ·
              refine ⟨53144159009217768645207245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35429439339478512430138163 53144159009217768645207245)
              ·
                refine ⟨19929059628456663241952717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53144159009217768645207245 19929059628456663241952717)
                ·
                  refine ⟨7473397360671248715732269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19929059628456663241952717 7473397360671248715732269)
                  ·
                    refine ⟨2802524010251718268399601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7473397360671248715732269 2802524010251718268399601)
                    ·
                      refine ⟨2101893007688788701299701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2802524010251718268399601 2101893007688788701299701)
                      ·
                        rfl

theorem cell23_4093422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_4093422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093422 prefixEnd_4093422 := by exact prefixLift 4093422
  have htrace : WordTrace (prefixWord ++ tailWord_4093422) baseStart_4093422 baseEnd_4093422 := by
    simpa [prefixWord, tailWord_4093422, baseEnd_4093422] using wordTrace_append hprefix tailTrace_4093422
  have hstable : (prefixWord ++ tailWord_4093422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093422).length < 2 ^ (prefixWord ++ tailWord_4093422).sum := by decide
  have hdescent : baseEnd_4093422 < baseStart_4093422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093525 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_4093525 : Nat := 118140960795 + 4093525 * 2 ^ 59
def prefixEnd_4093525 : Nat := 4983230072969 + 3 ^ 40 * 4093525 * 2
def baseEnd_4093525 : Nat := 2101945896196201798311727

theorem tailTrace_4093525 : CollatzResearch.WordTrace tailWord_4093525 prefixEnd_4093525 2101945896196201798311727 := by
  unfold tailWord_4093525
  simp only [CollatzResearch.WordTrace]
  refine ⟨149303122494865518255450029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99535414996577012170300019 149303122494865518255450029)
  ·
    refine ⟨55988670935574569345793761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149303122494865518255450029 55988670935574569345793761)
    ·
      refine ⟨41991503201680927009345321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55988670935574569345793761 41991503201680927009345321)
      ·
        refine ⟨31493627401260695257008991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41991503201680927009345321 31493627401260695257008991)
        ·
          refine ⟨47240441101891042885513487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31493627401260695257008991 47240441101891042885513487)
          ·
            refine ⟨70860661652836564328270231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47240441101891042885513487 70860661652836564328270231)
            ·
              refine ⟨106290992479254846492405347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70860661652836564328270231 106290992479254846492405347)
              ·
                refine ⟨159436488718882269738608021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106290992479254846492405347 159436488718882269738608021)
                ·
                  refine ⟨7473585408697606393997251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159436488718882269738608021 7473585408697606393997251)
                  ·
                    refine ⟨11210378113046409590995877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7473585408697606393997251 11210378113046409590995877)
                    ·
                      refine ⟨2101945896196201798311727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11210378113046409590995877 2101945896196201798311727)
                      ·
                        rfl

theorem cell23_4093525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_4093525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093525 prefixEnd_4093525 := by exact prefixLift 4093525
  have htrace : WordTrace (prefixWord ++ tailWord_4093525) baseStart_4093525 baseEnd_4093525 := by
    simpa [prefixWord, tailWord_4093525, baseEnd_4093525] using wordTrace_append hprefix tailTrace_4093525
  have hstable : (prefixWord ++ tailWord_4093525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093525).length < 2 ^ (prefixWord ++ tailWord_4093525).sum := by decide
  have hdescent : baseEnd_4093525 < baseStart_4093525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093545 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 1, 4, 3]
def baseStart_4093545 : Nat := 118140960795 + 4093545 * 2 ^ 59
def prefixEnd_4093545 : Nat := 4983230072969 + 3 ^ 40 * 4093545 * 2
def baseEnd_4093545 : Nat := 2101956165809291720061635

theorem tailTrace_4093545 : CollatzResearch.WordTrace tailWord_4093545 prefixEnd_4093545 2101956165809291720061635 := by
  unfold tailWord_4093545
  simp only [CollatzResearch.WordTrace]
  refine ⟨149303851954793061671178089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99535901303195374447452059 149303851954793061671178089)
  ·
    refine ⟨111977888966094796253383567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149303851954793061671178089 111977888966094796253383567)
    ·
      refine ⟨167966833449142194380075351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111977888966094796253383567 167966833449142194380075351)
      ·
        refine ⟨251950250173713291570113027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167966833449142194380075351 251950250173713291570113027)
        ·
          refine ⟨377925375260569937355169541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251950250173713291570113027 377925375260569937355169541)
          ·
            refine ⟨70861007861356863254094289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 377925375260569937355169541 70861007861356863254094289)
            ·
              refine ⟨53145755896017647440570717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70861007861356863254094289 53145755896017647440570717)
              ·
                refine ⟨19929658461006617790214019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53145755896017647440570717 19929658461006617790214019)
                ·
                  refine ⟨29894487691509926685321029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19929658461006617790214019 29894487691509926685321029)
                  ·
                    refine ⟨5605216442158111253497693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29894487691509926685321029 5605216442158111253497693)
                    ·
                      refine ⟨2101956165809291720061635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5605216442158111253497693 2101956165809291720061635)
                      ·
                        rfl

theorem cell23_4093545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 4, 3].length) (baseStart_4093545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093545 prefixEnd_4093545 := by exact prefixLift 4093545
  have htrace : WordTrace (prefixWord ++ tailWord_4093545) baseStart_4093545 baseEnd_4093545 := by
    simpa [prefixWord, tailWord_4093545, baseEnd_4093545] using wordTrace_append hprefix tailTrace_4093545
  have hstable : (prefixWord ++ tailWord_4093545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093545).length < 2 ^ (prefixWord ++ tailWord_4093545).sum := by decide
  have hdescent : baseEnd_4093545 < baseStart_4093545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093576 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 2, 4, 2]
def baseStart_4093576 : Nat := 118140960795 + 4093576 * 2 ^ 59
def prefixEnd_4093576 : Nat := 4983230072969 + 3 ^ 40 * 4093576 * 2
def baseEnd_4093576 : Nat := 2101972083709581098773993

theorem tailTrace_4093576 : CollatzResearch.WordTrace tailWord_4093576 prefixEnd_4093576 2101972083709581098773993 := by
  unfold tailWord_4093576
  simp only [CollatzResearch.WordTrace]
  refine ⟨74652491308840376982778291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99536655078453835977037721 74652491308840376982778291)
  ·
    refine ⟨111978736963260565474167437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74652491308840376982778291 111978736963260565474167437)
    ·
      refine ⟨41992026361222712052812789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111978736963260565474167437 41992026361222712052812789)
      ·
        refine ⟨3936752471364629254951199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41992026361222712052812789 3936752471364629254951199)
        ·
          refine ⟨5905128707046943882426799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936752471364629254951199 5905128707046943882426799)
          ·
            refine ⟨8857693060570415823640199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5905128707046943882426799 8857693060570415823640199)
            ·
              refine ⟨13286539590855623735460299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8857693060570415823640199 13286539590855623735460299)
              ·
                refine ⟨19929809386283435603190449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13286539590855623735460299 19929809386283435603190449)
                ·
                  refine ⟨14947357039712576702392837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19929809386283435603190449 14947357039712576702392837)
                  ·
                    refine ⟨2802629444946108131698657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14947357039712576702392837 2802629444946108131698657)
                    ·
                      refine ⟨2101972083709581098773993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2802629444946108131698657 2101972083709581098773993)
                      ·
                        rfl

theorem cell23_4093576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_4093576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093576 prefixEnd_4093576 := by exact prefixLift 4093576
  have htrace : WordTrace (prefixWord ++ tailWord_4093576) baseStart_4093576 baseEnd_4093576 := by
    simpa [prefixWord, tailWord_4093576, baseEnd_4093576] using wordTrace_append hprefix tailTrace_4093576
  have hstable : (prefixWord ++ tailWord_4093576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093576).length < 2 ^ (prefixWord ++ tailWord_4093576).sum := by decide
  have hdescent : baseEnd_4093576 < baseStart_4093576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093582 : List Nat := [4, 1, 1, 3, 1, 2, 2, 3, 6]
def baseStart_4093582 : Nat := 118140960795 + 4093582 * 2 ^ 59
def prefixEnd_4093582 : Nat := 4983230072969 + 3 ^ 40 * 4093582 * 2
def baseEnd_4093582 : Nat := 233552796065945341699885

theorem tailTrace_4093582 : CollatzResearch.WordTrace tailWord_4093582 prefixEnd_4093582 233552796065945341699885 := by
  unfold tailWord_4093582
  simp only [CollatzResearch.WordTrace]
  refine ⟨18663150181957377123784375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99536800970439344660183333 18663150181957377123784375)
  ·
    refine ⟨27994725272936065685676563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18663150181957377123784375 27994725272936065685676563)
    ·
      refine ⟨41992087909404098528514845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27994725272936065685676563 41992087909404098528514845)
      ·
        refine ⟨15747032966026536948193067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41992087909404098528514845 15747032966026536948193067)
        ·
          refine ⟨23620549449039805422289601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15747032966026536948193067 23620549449039805422289601)
          ·
            refine ⟨17715412086779854066717201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23620549449039805422289601 17715412086779854066717201)
            ·
              refine ⟨13286559065084890550037901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17715412086779854066717201 13286559065084890550037901)
              ·
                refine ⟨4982459649406833956264213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13286559065084890550037901 4982459649406833956264213)
                ·
                  refine ⟨233552796065945341699885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4982459649406833956264213 233552796065945341699885)
                  ·
                    rfl

theorem cell23_4093582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_4093582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093582 prefixEnd_4093582 := by exact prefixLift 4093582
  have htrace : WordTrace (prefixWord ++ tailWord_4093582) baseStart_4093582 baseEnd_4093582 := by
    simpa [prefixWord, tailWord_4093582, baseEnd_4093582] using wordTrace_append hprefix tailTrace_4093582
  have hstable : (prefixWord ++ tailWord_4093582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093582).length < 2 ^ (prefixWord ++ tailWord_4093582).sum := by decide
  have hdescent : baseEnd_4093582 < baseStart_4093582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093596 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_4093596 : Nat := 118140960795 + 4093596 * 2 ^ 59
def prefixEnd_4093596 : Nat := 4983230072969 + 3 ^ 40 * 4093596 * 2
def baseEnd_4093596 : Nat := 2101982353322671020523901

theorem tailTrace_4093596 : CollatzResearch.WordTrace tailWord_4093596 prefixEnd_4093596 2101982353322671020523901 := by
  unfold tailWord_4093596
  simp only [CollatzResearch.WordTrace]
  refine ⟨74652856038804148690642321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99537141385072198254189761 74652856038804148690642321)
  ·
    refine ⟨55989642029103111517981741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74652856038804148690642321 55989642029103111517981741)
    ·
      refine ⟨20996115760913666819243153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55989642029103111517981741 20996115760913666819243153)
      ·
        refine ⟨15747086820685250114432365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20996115760913666819243153 15747086820685250114432365)
        ·
          refine ⟨5905157557756968792912137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15747086820685250114432365 5905157557756968792912137)
          ·
            refine ⟨4428868168317726594684103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5905157557756968792912137 4428868168317726594684103)
            ·
              refine ⟨6643302252476589892026155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4428868168317726594684103 6643302252476589892026155)
              ·
                refine ⟨9964953378714884838039233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6643302252476589892026155 9964953378714884838039233)
                ·
                  refine ⟨7473715034036163628529425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9964953378714884838039233 7473715034036163628529425)
                  ·
                    refine ⟨5605286275527122721397069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7473715034036163628529425 5605286275527122721397069)
                    ·
                      refine ⟨2101982353322671020523901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5605286275527122721397069 2101982353322671020523901)
                      ·
                        rfl

theorem cell23_4093596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_4093596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093596 prefixEnd_4093596 := by exact prefixLift 4093596
  have htrace : WordTrace (prefixWord ++ tailWord_4093596) baseStart_4093596 baseEnd_4093596 := by
    simpa [prefixWord, tailWord_4093596, baseEnd_4093596] using wordTrace_append hprefix tailTrace_4093596
  have hstable : (prefixWord ++ tailWord_4093596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093596).length < 2 ^ (prefixWord ++ tailWord_4093596).sum := by decide
  have hdescent : baseEnd_4093596 < baseStart_4093596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093625 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 3, 6]
def baseStart_4093625 : Nat := 118140960795 + 4093625 * 2 ^ 59
def prefixEnd_4093625 : Nat := 4983230072969 + 3 ^ 40 * 4093625 * 2
def baseEnd_4093625 : Nat := 700665748087217135687089

theorem tailTrace_4093625 : CollatzResearch.WordTrace tailWord_4093625 prefixEnd_4093625 700665748087217135687089 := by
  unfold tailWord_4093625
  simp only [CollatzResearch.WordTrace]
  refine ⟨149306769794503235334090329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99537846529668823556060219 149306769794503235334090329)
  ·
    refine ⟨111980077345877426500567747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149306769794503235334090329 111980077345877426500567747)
    ·
      refine ⟨167970116018816139750851621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111980077345877426500567747 167970116018816139750851621)
      ·
        refine ⟨31494396753528026203284679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167970116018816139750851621 31494396753528026203284679)
        ·
          refine ⟨47241595130292039304927019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31494396753528026203284679 47241595130292039304927019)
          ·
            refine ⟨70862392695438058957390529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47241595130292039304927019 70862392695438058957390529)
            ·
              refine ⟨53146794521578544218042897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70862392695438058957390529 53146794521578544218042897)
              ·
                refine ⟨39860095891183908163532173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53146794521578544218042897 39860095891183908163532173)
                ·
                  refine ⟨14947535959193965561324565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39860095891183908163532173 14947535959193965561324565)
                  ·
                    refine ⟨700665748087217135687089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14947535959193965561324565 700665748087217135687089)
                    ·
                      rfl

theorem cell23_4093625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 6].length) (baseStart_4093625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093625 prefixEnd_4093625 := by exact prefixLift 4093625
  have htrace : WordTrace (prefixWord ++ tailWord_4093625) baseStart_4093625 baseEnd_4093625 := by
    simpa [prefixWord, tailWord_4093625, baseEnd_4093625] using wordTrace_append hprefix tailTrace_4093625
  have hstable : (prefixWord ++ tailWord_4093625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093625).length < 2 ^ (prefixWord ++ tailWord_4093625).sum := by decide
  have hdescent : baseEnd_4093625 < baseStart_4093625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093626 : List Nat := [3, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3]
def baseStart_4093626 : Nat := 118140960795 + 4093626 * 2 ^ 59
def prefixEnd_4093626 : Nat := 4983230072969 + 3 ^ 40 * 4093626 * 2
def baseEnd_4093626 : Nat := 2101997757742305903148763

theorem tailTrace_4093626 : CollatzResearch.WordTrace tailWord_4093626 prefixEnd_4093626 2101997757742305903148763 := by
  unfold tailWord_4093626
  simp only [CollatzResearch.WordTrace]
  refine ⟨37326701566874903126219183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99537870844999741669917821 37326701566874903126219183)
  ·
    refine ⟨55990052350312354689328775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37326701566874903126219183 55990052350312354689328775)
    ·
      refine ⟨83985078525468532033993163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55990052350312354689328775 83985078525468532033993163)
      ·
        refine ⟨125977617788202798050989745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83985078525468532033993163 125977617788202798050989745)
        ·
          refine ⟨94483213341152098538242309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125977617788202798050989745 94483213341152098538242309)
          ·
            refine ⟨17715602501466018475920433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94483213341152098538242309 17715602501466018475920433)
            ·
              refine ⟨13286701876099513856940325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17715602501466018475920433 13286701876099513856940325)
              ·
                refine ⟨2491256601768658848176311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13286701876099513856940325 2491256601768658848176311)
                ·
                  refine ⟨3736884902652988272264467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491256601768658848176311 3736884902652988272264467)
                  ·
                    refine ⟨5605327353979482408396701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3736884902652988272264467 5605327353979482408396701)
                    ·
                      refine ⟨2101997757742305903148763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5605327353979482408396701 2101997757742305903148763)
                      ·
                        rfl

theorem cell23_4093626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3].length) (baseStart_4093626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093626 prefixEnd_4093626 := by exact prefixLift 4093626
  have htrace : WordTrace (prefixWord ++ tailWord_4093626) baseStart_4093626 baseEnd_4093626 := by
    simpa [prefixWord, tailWord_4093626, baseEnd_4093626] using wordTrace_append hprefix tailTrace_4093626
  have hstable : (prefixWord ++ tailWord_4093626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093626).length < 2 ^ (prefixWord ++ tailWord_4093626).sum := by decide
  have hdescent : baseEnd_4093626 < baseStart_4093626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093649 : List Nat := [1, 2, 2, 1, 2, 5, 2, 2, 1, 1, 4]
def baseStart_4093649 : Nat := 118140960795 + 4093649 * 2 ^ 59
def prefixEnd_4093649 : Nat := 4983230072969 + 3 ^ 40 * 4093649 * 2
def baseEnd_4093649 : Nat := 2102009567797359313161157

theorem tailTrace_4093649 : CollatzResearch.WordTrace tailWord_4093649 prefixEnd_4093649 2102009567797359313161157 := by
  unfold tailWord_4093649
  simp only [CollatzResearch.WordTrace]
  refine ⟨149307645146416287432964001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99538430097610858288642667 149307645146416287432964001)
  ·
    refine ⟨111980733859812215574723001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149307645146416287432964001 111980733859812215574723001)
    ·
      refine ⟨83985550394859161681042251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111980733859812215574723001 83985550394859161681042251)
      ·
        refine ⟨125978325592288742521563377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83985550394859161681042251 125978325592288742521563377)
        ·
          refine ⟨94483744194216556891172533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125978325592288742521563377 94483744194216556891172533)
          ·
            refine ⟨8857851018207802208547425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94483744194216556891172533 8857851018207802208547425)
            ·
              refine ⟨6643388263655851656410569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8857851018207802208547425 6643388263655851656410569)
              ·
                refine ⟨4982541197741888742307927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6643388263655851656410569 4982541197741888742307927)
                ·
                  refine ⟨7473811796612833113461891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4982541197741888742307927 7473811796612833113461891)
                  ·
                    refine ⟨11210717694919249670192837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7473811796612833113461891 11210717694919249670192837)
                    ·
                      refine ⟨2102009567797359313161157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11210717694919249670192837 2102009567797359313161157)
                      ·
                        rfl

theorem cell23_4093649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_4093649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093649 prefixEnd_4093649 := by exact prefixLift 4093649
  have htrace : WordTrace (prefixWord ++ tailWord_4093649) baseStart_4093649 baseEnd_4093649 := by
    simpa [prefixWord, tailWord_4093649, baseEnd_4093649] using wordTrace_append hprefix tailTrace_4093649
  have hstable : (prefixWord ++ tailWord_4093649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093649).length < 2 ^ (prefixWord ++ tailWord_4093649).sum := by decide
  have hdescent : baseEnd_4093649 < baseStart_4093649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093655 : List Nat := [1, 1, 3, 2, 1, 3, 3, 9]
def baseStart_4093655 : Nat := 118140960795 + 4093655 * 2 ^ 59
def prefixEnd_4093655 : Nat := 4983230072969 + 3 ^ 40 * 4093655 * 2
def baseEnd_4093655 : Nat := 77852320321529121840227

theorem tailTrace_4093655 : CollatzResearch.WordTrace tailWord_4093655 prefixEnd_4093655 77852320321529121840227 := by
  unfold tailWord_4093655
  simp only [CollatzResearch.WordTrace]
  refine ⟨149307863984394550457682419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99538575989596366971788279 149307863984394550457682419)
  ·
    refine ⟨223961795976591825686523629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149307863984394550457682419 223961795976591825686523629)
    ·
      refine ⟨83985673491221934632446361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223961795976591825686523629 83985673491221934632446361)
      ·
        refine ⟨62989255118416450974334771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83985673491221934632446361 62989255118416450974334771)
        ·
          refine ⟨94483882677624676461502157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62989255118416450974334771 94483882677624676461502157)
          ·
            refine ⟨35431456004109253673063309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94483882677624676461502157 35431456004109253673063309)
            ·
              refine ⟨13286796001540970127398741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35431456004109253673063309 13286796001540970127398741)
              ·
                refine ⟨77852320321529121840227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13286796001540970127398741 77852320321529121840227)
                ·
                  rfl

theorem cell23_4093655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 9].length) (baseStart_4093655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093655 prefixEnd_4093655 := by exact prefixLift 4093655
  have htrace : WordTrace (prefixWord ++ tailWord_4093655) baseStart_4093655 baseEnd_4093655 := by
    simpa [prefixWord, tailWord_4093655, baseEnd_4093655] using wordTrace_append hprefix tailTrace_4093655
  have hstable : (prefixWord ++ tailWord_4093655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093655).length < 2 ^ (prefixWord ++ tailWord_4093655).sum := by decide
  have hdescent : baseEnd_4093655 < baseStart_4093655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093669 : List Nat := [1, 3, 1, 4, 1, 1, 1, 5, 1, 2, 3]
def baseStart_4093669 : Nat := 118140960795 + 4093669 * 2 ^ 59
def prefixEnd_4093669 : Nat := 4983230072969 + 3 ^ 40 * 4093669 * 2
def baseEnd_4093669 : Nat := 2102019837410449234911065

theorem tailTrace_4093669 : CollatzResearch.WordTrace tailWord_4093669 prefixEnd_4093669 2102019837410449234911065 := by
  unfold tailWord_4093669
  simp only [CollatzResearch.WordTrace]
  refine ⟨149308374606343830848692061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99538916404229220565794707 149308374606343830848692061)
  ·
    refine ⟨55990640477378936568259523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149308374606343830848692061 55990640477378936568259523)
    ·
      refine ⟨83985960716068404852389285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55990640477378936568259523 83985960716068404852389285)
      ·
        refine ⟨15747367634262825909822991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83985960716068404852389285 15747367634262825909822991)
        ·
          refine ⟨23621051451394238864734487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15747367634262825909822991 23621051451394238864734487)
          ·
            refine ⟨35431577177091358297101731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23621051451394238864734487 35431577177091358297101731)
            ·
              refine ⟨53147365765637037445652597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35431577177091358297101731 53147365765637037445652597)
              ·
                refine ⟨4982565540528472260529931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53147365765637037445652597 4982565540528472260529931)
                ·
                  refine ⟨7473848310792708390794897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4982565540528472260529931 7473848310792708390794897)
                  ·
                    refine ⟨5605386233094531293096173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7473848310792708390794897 5605386233094531293096173)
                    ·
                      refine ⟨2102019837410449234911065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5605386233094531293096173 2102019837410449234911065)
                      ·
                        rfl

theorem cell23_4093669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_4093669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093669 prefixEnd_4093669 := by exact prefixLift 4093669
  have htrace : WordTrace (prefixWord ++ tailWord_4093669) baseStart_4093669 baseEnd_4093669 := by
    simpa [prefixWord, tailWord_4093669, baseEnd_4093669] using wordTrace_append hprefix tailTrace_4093669
  have hstable : (prefixWord ++ tailWord_4093669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093669).length < 2 ^ (prefixWord ++ tailWord_4093669).sum := by decide
  have hdescent : baseEnd_4093669 < baseStart_4093669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093672 : List Nat := [2, 1, 4, 1, 3, 3, 9]
def baseStart_4093672 : Nat := 118140960795 + 4093672 * 2 ^ 59
def prefixEnd_4093672 : Nat := 4983230072969 + 3 ^ 40 * 4093672 * 2
def baseEnd_4093672 : Nat := 25950881208054478063871

theorem tailTrace_4093672 : CollatzResearch.WordTrace tailWord_4093672 prefixEnd_4093672 25950881208054478063871 := by
  unfold tailWord_4093672
  simp only [CollatzResearch.WordTrace]
  refine ⟨74654242012666481180525635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99538989350221974907367513 74654242012666481180525635)
  ·
    refine ⟨111981363018999721770788453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74654242012666481180525635 111981363018999721770788453)
    ·
      refine ⟨20996505566062447832022835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111981363018999721770788453 20996505566062447832022835)
      ·
        refine ⟨31494758349093671748034253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20996505566062447832022835 31494758349093671748034253)
        ·
          refine ⟨11810534380910126905512845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31494758349093671748034253 11810534380910126905512845)
          ·
            refine ⟨4428950392841297589567317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11810534380910126905512845 4428950392841297589567317)
            ·
              refine ⟨25950881208054478063871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4428950392841297589567317 25950881208054478063871)
              ·
                rfl

theorem cell23_4093672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 9].length) (baseStart_4093672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093672 prefixEnd_4093672 := by exact prefixLift 4093672
  have htrace : WordTrace (prefixWord ++ tailWord_4093672) baseStart_4093672 baseEnd_4093672 := by
    simpa [prefixWord, tailWord_4093672, baseEnd_4093672] using wordTrace_append hprefix tailTrace_4093672
  have hstable : (prefixWord ++ tailWord_4093672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093672).length < 2 ^ (prefixWord ++ tailWord_4093672).sum := by decide
  have hdescent : baseEnd_4093672 < baseStart_4093672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093703 : List Nat := [1, 1, 4, 4, 2, 2, 1, 2, 1, 2, 3]
def baseStart_4093703 : Nat := 118140960795 + 4093703 * 2 ^ 59
def prefixEnd_4093703 : Nat := 4983230072969 + 3 ^ 40 * 4093703 * 2
def baseEnd_4093703 : Nat := 2102037295752702101885909

theorem tailTrace_4093703 : CollatzResearch.WordTrace tailWord_4093703 prefixEnd_4093703 2102037295752702101885909 := by
  unfold tailWord_4093703
  simp only [CollatzResearch.WordTrace]
  refine ⟨149309614688220654655429763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99539743125480436436953175 149309614688220654655429763)
  ·
    refine ⟨223964422032330981983144645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149309614688220654655429763 223964422032330981983144645)
    ·
      refine ⟨41993329131062059121839621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223964422032330981983144645 41993329131062059121839621)
      ·
        refine ⟨7873749212074136085344929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41993329131062059121839621 7873749212074136085344929)
        ·
          refine ⟨5905311909055602064008697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7873749212074136085344929 5905311909055602064008697)
          ·
            refine ⟨4428983931791701548006523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5905311909055602064008697 4428983931791701548006523)
            ·
              refine ⟨6643475897687552322009785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4428983931791701548006523 6643475897687552322009785)
              ·
                refine ⟨4982606923265664241507339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6643475897687552322009785 4982606923265664241507339)
                ·
                  refine ⟨7473910384898496362261009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4982606923265664241507339 7473910384898496362261009)
                  ·
                    refine ⟨5605432788673872271695757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7473910384898496362261009 5605432788673872271695757)
                    ·
                      refine ⟨2102037295752702101885909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5605432788673872271695757 2102037295752702101885909)
                      ·
                        rfl

theorem cell23_4093703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_4093703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093703 prefixEnd_4093703 := by exact prefixLift 4093703
  have htrace : WordTrace (prefixWord ++ tailWord_4093703) baseStart_4093703 baseEnd_4093703 := by
    simpa [prefixWord, tailWord_4093703, baseEnd_4093703] using wordTrace_append hprefix tailTrace_4093703
  have hstable : (prefixWord ++ tailWord_4093703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093703).length < 2 ^ (prefixWord ++ tailWord_4093703).sum := by decide
  have hdescent : baseEnd_4093703 < baseStart_4093703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093705 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 8]
def baseStart_4093705 : Nat := 118140960795 + 4093705 * 2 ^ 59
def prefixEnd_4093705 : Nat := 4983230072969 + 3 ^ 40 * 4093705 * 2
def baseEnd_4093705 : Nat := 2102038322714011094060899

theorem tailTrace_4093705 : CollatzResearch.WordTrace tailWord_4093705 prefixEnd_4093705 2102038322714011094060899 := by
  unfold tailWord_4093705
  simp only [CollatzResearch.WordTrace]
  refine ⟨149309687634213408997002569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99539791756142272664668379 149309687634213408997002569)
  ·
    refine ⟨111982265725660056747751927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149309687634213408997002569 111982265725660056747751927)
    ·
      refine ⟨167973398588490085121627891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111982265725660056747751927 167973398588490085121627891)
      ·
        refine ⟨251960097882735127682441837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167973398588490085121627891 251960097882735127682441837)
        ·
          refine ⟨94485036706025672880915689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251960097882735127682441837 94485036706025672880915689)
          ·
            refine ⟨70863777529519254660686767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94485036706025672880915689 70863777529519254660686767)
            ·
              refine ⟨106295666294278881991030151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70863777529519254660686767 106295666294278881991030151)
              ·
                refine ⟨159443499441418322986545227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106295666294278881991030151 159443499441418322986545227)
                ·
                  refine ⟨239165249162127484479817841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159443499441418322986545227 239165249162127484479817841)
                  ·
                    refine ⟨179373936871595613359863381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 239165249162127484479817841 179373936871595613359863381)
                    ·
                      refine ⟨2102038322714011094060899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 179373936871595613359863381 2102038322714011094060899)
                      ·
                        rfl

theorem cell23_4093705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_4093705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093705 prefixEnd_4093705 := by exact prefixLift 4093705
  have htrace : WordTrace (prefixWord ++ tailWord_4093705) baseStart_4093705 baseEnd_4093705 := by
    simpa [prefixWord, tailWord_4093705, baseEnd_4093705] using wordTrace_append hprefix tailTrace_4093705
  have hstable : (prefixWord ++ tailWord_4093705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093705).length < 2 ^ (prefixWord ++ tailWord_4093705).sum := by decide
  have hdescent : baseEnd_4093705 < baseStart_4093705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093715 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 3, 8]
def baseStart_4093715 : Nat := 118140960795 + 4093715 * 2 ^ 59
def prefixEnd_4093715 : Nat := 4983230072969 + 3 ^ 40 * 4093715 * 2
def baseEnd_4093715 : Nat := 700681152506852018311951

theorem tailTrace_4093715 : CollatzResearch.WordTrace tailWord_4093715 prefixEnd_4093715 700681152506852018311951 := by
  unfold tailWord_4093715
  simp only [CollatzResearch.WordTrace]
  refine ⟨149310052364177180704866599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99540034909451453803244399 149310052364177180704866599)
  ·
    refine ⟨223965078546265771057299899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149310052364177180704866599 223965078546265771057299899)
    ·
      refine ⟨335947617819398656585949849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223965078546265771057299899 335947617819398656585949849)
      ·
        refine ⟨251960713364548992439462387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335947617819398656585949849 251960713364548992439462387)
        ·
          refine ⟨377941070046823488659193581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251960713364548992439462387 377941070046823488659193581)
          ·
            refine ⟨141727901267558808247197593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377941070046823488659193581 141727901267558808247197593)
            ·
              refine ⟨106295925950669106185398195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141727901267558808247197593 106295925950669106185398195)
              ·
                refine ⟨159443888926003659278097293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106295925950669106185398195 159443888926003659278097293)
                ·
                  refine ⟨59791458347251372229286485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159443888926003659278097293 59791458347251372229286485)
                  ·
                    refine ⟨700681152506852018311951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59791458347251372229286485 700681152506852018311951)
                    ·
                      rfl

theorem cell23_4093715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 8].length) (baseStart_4093715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093715 prefixEnd_4093715 := by exact prefixLift 4093715
  have htrace : WordTrace (prefixWord ++ tailWord_4093715) baseStart_4093715 baseEnd_4093715 := by
    simpa [prefixWord, tailWord_4093715, baseEnd_4093715] using wordTrace_append hprefix tailTrace_4093715
  have hstable : (prefixWord ++ tailWord_4093715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093715).length < 2 ^ (prefixWord ++ tailWord_4093715).sum := by decide
  have hdescent : baseEnd_4093715 < baseStart_4093715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093749 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 2, 6]
def baseStart_4093749 : Nat := 118140960795 + 4093749 * 2 ^ 59
def prefixEnd_4093749 : Nat := 4983230072969 + 3 ^ 40 * 4093749 * 2
def baseEnd_4093749 : Nat := 700686971954269640636899

theorem tailTrace_4093749 : CollatzResearch.WordTrace tailWord_4093749 prefixEnd_4093749 700686971954269640636899 := by
  unfold tailWord_4093749
  simp only [CollatzResearch.WordTrace]
  refine ⟨149311292446054004511604301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99540861630702669674402867 149311292446054004511604301)
  ·
    refine ⟨55991734667270251691851613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149311292446054004511604301 55991734667270251691851613)
    ·
      refine ⟨20996900500226344384444355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55991734667270251691851613 20996900500226344384444355)
      ·
        refine ⟨31495350750339516576666533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20996900500226344384444355 31495350750339516576666533)
        ·
          refine ⟨5905378265688659358124975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31495350750339516576666533 5905378265688659358124975)
          ·
            refine ⟨8858067398532989037187463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5905378265688659358124975 8858067398532989037187463)
            ·
              refine ⟨13287101097799483555781195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8858067398532989037187463 13287101097799483555781195)
              ·
                refine ⟨19930651646699225333671793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13287101097799483555781195 19930651646699225333671793)
                ·
                  refine ⟨14947988735024419000253845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19930651646699225333671793 14947988735024419000253845)
                  ·
                    refine ⟨700686971954269640636899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14947988735024419000253845 700686971954269640636899)
                    ·
                      rfl

theorem cell23_4093749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_4093749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093749 prefixEnd_4093749 := by exact prefixLift 4093749
  have htrace : WordTrace (prefixWord ++ tailWord_4093749) baseStart_4093749 baseEnd_4093749 := by
    simpa [prefixWord, tailWord_4093749, baseEnd_4093749] using wordTrace_append hprefix tailTrace_4093749
  have hstable : (prefixWord ++ tailWord_4093749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093749).length < 2 ^ (prefixWord ++ tailWord_4093749).sum := by decide
  have hdescent : baseEnd_4093749 < baseStart_4093749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093752 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 1, 4, 4]
def baseStart_4093752 : Nat := 118140960795 + 4093752 * 2 ^ 59
def prefixEnd_4093752 : Nat := 4983230072969 + 3 ^ 40 * 4093752 * 2
def baseEnd_4093752 : Nat := 2102062456304772410173183

theorem tailTrace_4093752 : CollatzResearch.WordTrace tailWord_4093752 prefixEnd_4093752 2102062456304772410173183 := by
  unfold tailWord_4093752
  simp only [CollatzResearch.WordTrace]
  refine ⟨74655700932521568011981755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99540934576695424015975673 74655700932521568011981755)
  ·
    refine ⟨111983551398782352017972633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74655700932521568011981755 111983551398782352017972633)
    ·
      refine ⟨83987663549086764013479475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111983551398782352017972633 83987663549086764013479475)
      ·
        refine ⟨125981495323630146020219213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83987663549086764013479475 125981495323630146020219213)
        ·
          refine ⟨47243060746361304757582205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125981495323630146020219213 47243060746361304757582205)
          ·
            refine ⟨17716147779885489284093327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47243060746361304757582205 17716147779885489284093327)
            ·
              refine ⟨26574221669828233926139991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17716147779885489284093327 26574221669828233926139991)
              ·
                refine ⟨39861332504742350889209987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26574221669828233926139991 39861332504742350889209987)
                ·
                  refine ⟨59791998757113526333814981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39861332504742350889209987 59791998757113526333814981)
                  ·
                    refine ⟨11210999766958786187590309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59791998757113526333814981 11210999766958786187590309)
                    ·
                      refine ⟨2102062456304772410173183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11210999766958786187590309 2102062456304772410173183)
                      ·
                        rfl

theorem cell23_4093752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_4093752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093752 prefixEnd_4093752 := by exact prefixLift 4093752
  have htrace : WordTrace (prefixWord ++ tailWord_4093752) baseStart_4093752 baseEnd_4093752 := by
    simpa [prefixWord, tailWord_4093752, baseEnd_4093752] using wordTrace_append hprefix tailTrace_4093752
  have hstable : (prefixWord ++ tailWord_4093752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093752).length < 2 ^ (prefixWord ++ tailWord_4093752).sum := by decide
  have hdescent : baseEnd_4093752 < baseStart_4093752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093773 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_4093773 : Nat := 118140960795 + 4093773 * 2 ^ 59
def prefixEnd_4093773 : Nat := 4983230072969 + 3 ^ 40 * 4093773 * 2
def baseEnd_4093773 : Nat := 2102073239398516828010587

theorem tailTrace_4093773 : CollatzResearch.WordTrace tailWord_4093773 prefixEnd_4093773 2102073239398516828010587 := by
  unfold tailWord_4093773
  simp only [CollatzResearch.WordTrace]
  refine ⟨149312167797967056610477973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99541445198644704406985315 149312167797967056610477973)
  ·
    refine ⟨6999007865529705778616155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 149312167797967056610477973 6999007865529705778616155)
    ·
      refine ⟨10498511798294558667924233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6999007865529705778616155 10498511798294558667924233)
      ·
        refine ⟨7873883848720919000943175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10498511798294558667924233 7873883848720919000943175)
        ·
          refine ⟨11810825773081378501414763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7873883848720919000943175 11810825773081378501414763)
          ·
            refine ⟨17716238659622067752122145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11810825773081378501414763 17716238659622067752122145)
            ·
              refine ⟨13287178994716550814091609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17716238659622067752122145 13287178994716550814091609)
              ·
                refine ⟨9965384246037413110568707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13287178994716550814091609 9965384246037413110568707)
                ·
                  refine ⟨14948076369056119665853061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9965384246037413110568707 14948076369056119665853061)
                  ·
                    refine ⟨2802764319198022437347449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14948076369056119665853061 2802764319198022437347449)
                    ·
                      refine ⟨2102073239398516828010587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2802764319198022437347449 2102073239398516828010587)
                      ·
                        rfl

theorem cell23_4093773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_4093773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093773 prefixEnd_4093773 := by exact prefixLift 4093773
  have htrace : WordTrace (prefixWord ++ tailWord_4093773) baseStart_4093773 baseEnd_4093773 := by
    simpa [prefixWord, tailWord_4093773, baseEnd_4093773] using wordTrace_append hprefix tailTrace_4093773
  have hstable : (prefixWord ++ tailWord_4093773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093773).length < 2 ^ (prefixWord ++ tailWord_4093773).sum := by decide
  have hdescent : baseEnd_4093773 < baseStart_4093773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093806 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_4093806 : Nat := 118140960795 + 4093806 * 2 ^ 59
def prefixEnd_4093806 : Nat := 4983230072969 + 3 ^ 40 * 4093806 * 2
def baseEnd_4093806 : Nat := 2102090184260115198897935

theorem tailTrace_4093806 : CollatzResearch.WordTrace tailWord_4093806 prefixEnd_4093806 2102090184260115198897935 := by
  unfold tailWord_4093806
  simp only [CollatzResearch.WordTrace]
  refine ⟨18664171425855937905803659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99542247604565002164286181 18664171425855937905803659)
  ·
    refine ⟨27996257138783906858705489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18664171425855937905803659 27996257138783906858705489)
    ·
      refine ⟨20997192854087930144029117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27996257138783906858705489 20997192854087930144029117)
      ·
        refine ⟨7873947320282973804010919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20997192854087930144029117 7873947320282973804010919)
        ·
          refine ⟨11810920980424460706016379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7873947320282973804010919 11810920980424460706016379)
          ·
            refine ⟨17716381470636691059024569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11810920980424460706016379 17716381470636691059024569)
            ·
              refine ⟨13287286102977518294268427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17716381470636691059024569 13287286102977518294268427)
              ·
                refine ⟨19930929154466277441402641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13287286102977518294268427 19930929154466277441402641)
                ·
                  refine ⟨14948196865849708081051981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19930929154466277441402641 14948196865849708081051981)
                  ·
                    refine ⟨5605573824693640530394493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14948196865849708081051981 5605573824693640530394493)
                    ·
                      refine ⟨2102090184260115198897935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5605573824693640530394493 2102090184260115198897935)
                      ·
                        rfl

theorem cell23_4093806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_4093806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093806 prefixEnd_4093806 := by exact prefixLift 4093806
  have htrace : WordTrace (prefixWord ++ tailWord_4093806) baseStart_4093806 baseEnd_4093806 := by
    simpa [prefixWord, tailWord_4093806, baseEnd_4093806] using wordTrace_append hprefix tailTrace_4093806
  have hstable : (prefixWord ++ tailWord_4093806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093806).length < 2 ^ (prefixWord ++ tailWord_4093806).sum := by decide
  have hdescent : baseEnd_4093806 < baseStart_4093806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093829 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 2, 1, 4]
def baseStart_4093829 : Nat := 118140960795 + 4093829 * 2 ^ 59
def prefixEnd_4093829 : Nat := 4983230072969 + 3 ^ 40 * 4093829 * 2
def baseEnd_4093829 : Nat := 2102101994315168608910329

theorem tailTrace_4093829 : CollatzResearch.WordTrace tailWord_4093829 prefixEnd_4093829 2102101994315168608910329 := by
  unfold tailWord_4093829
  simp only [CollatzResearch.WordTrace]
  refine ⟨149314210285764178174516541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99542806857176118783011027 149314210285764178174516541)
  ·
    refine ⟨55992828857161566815443703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149314210285764178174516541 55992828857161566815443703)
    ·
      refine ⟨83989243285742350223165555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55992828857161566815443703 83989243285742350223165555)
      ·
        refine ⟨125983864928613525334748333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83989243285742350223165555 125983864928613525334748333)
        ·
          refine ⟨47243949348230072000530625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125983864928613525334748333 47243949348230072000530625)
          ·
            refine ⟨35432962011172554000397969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47243949348230072000530625 35432962011172554000397969)
            ·
              refine ⟨26574721508379415500298477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35432962011172554000397969 26574721508379415500298477)
              ·
                refine ⟨9965520565642280812611929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26574721508379415500298477 9965520565642280812611929)
                ·
                  refine ⟨7474140424231710609458947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9965520565642280812611929 7474140424231710609458947)
                  ·
                    refine ⟨11211210636347565914188421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7474140424231710609458947 11211210636347565914188421)
                    ·
                      refine ⟨2102101994315168608910329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11211210636347565914188421 2102101994315168608910329)
                      ·
                        rfl

theorem cell23_4093829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_4093829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093829 prefixEnd_4093829 := by exact prefixLift 4093829
  have htrace : WordTrace (prefixWord ++ tailWord_4093829) baseStart_4093829 baseEnd_4093829 := by
    simpa [prefixWord, tailWord_4093829, baseEnd_4093829] using wordTrace_append hprefix tailTrace_4093829
  have hstable : (prefixWord ++ tailWord_4093829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093829).length < 2 ^ (prefixWord ++ tailWord_4093829).sum := by decide
  have hdescent : baseEnd_4093829 < baseStart_4093829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093849 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 4, 2, 3]
def baseStart_4093849 : Nat := 118140960795 + 4093849 * 2 ^ 59
def prefixEnd_4093849 : Nat := 4983230072969 + 3 ^ 40 * 4093849 * 2
def baseEnd_4093849 : Nat := 2102112263928258530660237

theorem tailTrace_4093849 : CollatzResearch.WordTrace tailWord_4093849 prefixEnd_4093849 2102112263928258530660237 := by
  unfold tailWord_4093849
  simp only [CollatzResearch.WordTrace]
  refine ⟨149314939745691721590244601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99543293163794481060163067 149314939745691721590244601)
  ·
    refine ⟨111986204809268791192683451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149314939745691721590244601 111986204809268791192683451)
    ·
      refine ⟨167979307213903186789025177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111986204809268791192683451 167979307213903186789025177)
      ·
        refine ⟨125984480410427390091768883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167979307213903186789025177 125984480410427390091768883)
        ·
          refine ⟨188976720615641085137653325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125984480410427390091768883 188976720615641085137653325)
          ·
            refine ⟨70866270230865406926619997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188976720615641085137653325 70866270230865406926619997)
            ·
              refine ⟨26574851336574527597482499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70866270230865406926619997 26574851336574527597482499)
              ·
                refine ⟨39862277004861791396223749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26574851336574527597482499 39862277004861791396223749)
                ·
                  refine ⟨7474176938411585886791953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39862277004861791396223749 7474176938411585886791953)
                  ·
                    refine ⟨5605632703808689415093965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7474176938411585886791953 5605632703808689415093965)
                    ·
                      refine ⟨2102112263928258530660237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5605632703808689415093965 2102112263928258530660237)
                      ·
                        rfl

theorem cell23_4093849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_4093849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093849 prefixEnd_4093849 := by exact prefixLift 4093849
  have htrace : WordTrace (prefixWord ++ tailWord_4093849) baseStart_4093849 baseEnd_4093849 := by
    simpa [prefixWord, tailWord_4093849, baseEnd_4093849] using wordTrace_append hprefix tailTrace_4093849
  have hstable : (prefixWord ++ tailWord_4093849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093849).length < 2 ^ (prefixWord ++ tailWord_4093849).sum := by decide
  have hdescent : baseEnd_4093849 < baseStart_4093849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093950 : List Nat := [4, 2, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_4093950 : Nat := 118140960795 + 4093950 * 2 ^ 59
def prefixEnd_4093950 : Nat := 4983230072969 + 3 ^ 40 * 4093950 * 2
def baseEnd_4093950 : Nat := 700721375158120878499091

theorem tailTrace_4093950 : CollatzResearch.WordTrace tailWord_4093950 prefixEnd_4093950 700721375158120878499091 := by
  unfold tailWord_4093950
  simp only [CollatzResearch.WordTrace]
  refine ⟨18664827939790726979958913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99545749012217210559780869 18664827939790726979958913)
  ·
    refine ⟨13998620954843045234969185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18664827939790726979958913 13998620954843045234969185)
    ·
      refine ⟨10498965716132283926226889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13998620954843045234969185 10498965716132283926226889)
      ·
        refine ⟨7874224287099212944670167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10498965716132283926226889 7874224287099212944670167)
        ·
          refine ⟨11811336430648819417005251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7874224287099212944670167 11811336430648819417005251)
          ·
            refine ⟨17717004645973229125507877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11811336430648819417005251 17717004645973229125507877)
            ·
              refine ⟨3321938371119980461032727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17717004645973229125507877 3321938371119980461032727)
              ·
                refine ⟨4982907556679970691549091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3321938371119980461032727 4982907556679970691549091)
                ·
                  refine ⟨7474361335019956037323637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4982907556679970691549091 7474361335019956037323637)
                  ·
                    refine ⟨700721375158120878499091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7474361335019956037323637 700721375158120878499091)
                    ·
                      rfl

theorem cell23_4093950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_4093950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093950 prefixEnd_4093950 := by exact prefixLift 4093950
  have htrace : WordTrace (prefixWord ++ tailWord_4093950) baseStart_4093950 baseEnd_4093950 := by
    simpa [prefixWord, tailWord_4093950, baseEnd_4093950] using wordTrace_append hprefix tailTrace_4093950
  have hstable : (prefixWord ++ tailWord_4093950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093950).length < 2 ^ (prefixWord ++ tailWord_4093950).sum := by decide
  have hdescent : baseEnd_4093950 < baseStart_4093950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093953 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 5, 2, 2]
def baseStart_4093953 : Nat := 118140960795 + 4093953 * 2 ^ 59
def prefixEnd_4093953 : Nat := 4983230072969 + 3 ^ 40 * 4093953 * 2
def baseEnd_4093953 : Nat := 2102165665916326123759759

theorem tailTrace_4093953 : CollatzResearch.WordTrace tailWord_4093953 prefixEnd_4093953 2102165665916326123759759 := by
  unfold tailWord_4093953
  simp only [CollatzResearch.WordTrace]
  refine ⟨149318732937314947352030513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99545821958209964901353675 149318732937314947352030513)
  ·
    refine ⟨111989049702986210514022885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149318732937314947352030513 111989049702986210514022885)
    ·
      refine ⟨20997946819309914471379291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111989049702986210514022885 20997946819309914471379291)
      ·
        refine ⟨31496920228964871707068937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20997946819309914471379291 31496920228964871707068937)
        ·
          refine ⟨23622690171723653780301703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31496920228964871707068937 23622690171723653780301703)
          ·
            refine ⟨35434035257585480670452555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23622690171723653780301703 35434035257585480670452555)
            ·
              refine ⟨53151052886378221005678833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35434035257585480670452555 53151052886378221005678833)
              ·
                refine ⟨39863289664783665754259125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53151052886378221005678833 39863289664783665754259125)
                ·
                  refine ⟨3737183406073468664461793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39863289664783665754259125 3737183406073468664461793)
                  ·
                    refine ⟨2802887554555101498346345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3737183406073468664461793 2802887554555101498346345)
                    ·
                      refine ⟨2102165665916326123759759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2802887554555101498346345 2102165665916326123759759)
                      ·
                        rfl

theorem cell23_4093953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_4093953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093953 prefixEnd_4093953 := by exact prefixLift 4093953
  have htrace : WordTrace (prefixWord ++ tailWord_4093953) baseStart_4093953 baseEnd_4093953 := by
    simpa [prefixWord, tailWord_4093953, baseEnd_4093953] using wordTrace_append hprefix tailTrace_4093953
  have hstable : (prefixWord ++ tailWord_4093953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093953).length < 2 ^ (prefixWord ++ tailWord_4093953).sum := by decide
  have hdescent : baseEnd_4093953 < baseStart_4093953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093959 : List Nat := [1, 1, 4, 3, 1, 3, 10]
def baseStart_4093959 : Nat := 118140960795 + 4093959 * 2 ^ 59
def prefixEnd_4093959 : Nat := 4983230072969 + 3 ^ 40 * 4093959 * 2
def baseEnd_4093959 : Nat := 25952700577780902472651

theorem tailTrace_4093959 : CollatzResearch.WordTrace tailWord_4093959 prefixEnd_4093959 25952700577780902472651 := by
  unfold tailWord_4093959
  simp only [CollatzResearch.WordTrace]
  refine ⟨149318951775293210376748931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99545967850195473584499287 149318951775293210376748931)
  ·
    refine ⟨223978427662939815565123397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149318951775293210376748931 223978427662939815565123397)
    ·
      refine ⟨41995955186801215418460637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223978427662939815565123397 41995955186801215418460637)
      ·
        refine ⟨15748483195050455781922739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41995955186801215418460637 15748483195050455781922739)
        ·
          refine ⟨23622724792575683672884109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15748483195050455781922739 23622724792575683672884109)
          ·
            refine ⟨8858521797215881377331541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23622724792575683672884109 8858521797215881377331541)
            ·
              refine ⟨25952700577780902472651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8858521797215881377331541 25952700577780902472651)
              ·
                rfl

theorem cell23_4093959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 10].length) (baseStart_4093959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093959 prefixEnd_4093959 := by exact prefixLift 4093959
  have htrace : WordTrace (prefixWord ++ tailWord_4093959) baseStart_4093959 baseEnd_4093959 := by
    simpa [prefixWord, tailWord_4093959, baseEnd_4093959] using wordTrace_append hprefix tailTrace_4093959
  have hstable : (prefixWord ++ tailWord_4093959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093959).length < 2 ^ (prefixWord ++ tailWord_4093959).sum := by decide
  have hdescent : baseEnd_4093959 < baseStart_4093959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093969 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 3]
def baseStart_4093969 : Nat := 118140960795 + 4093969 * 2 ^ 59
def prefixEnd_4093969 : Nat := 4983230072969 + 3 ^ 40 * 4093969 * 2
def baseEnd_4093969 : Nat := 2102173881606798061159685

theorem tailTrace_4093969 : CollatzResearch.WordTrace tailWord_4093969 prefixEnd_4093969 2102173881606798061159685 := by
  unfold tailWord_4093969
  simp only [CollatzResearch.WordTrace]
  refine ⟨149319316505256982084612961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99546211003504654723075307 149319316505256982084612961)
  ·
    refine ⟨111989487378942736563459721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149319316505256982084612961 111989487378942736563459721)
    ·
      refine ⟨83992115534207052422594791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111989487378942736563459721 83992115534207052422594791)
      ·
        refine ⟨125988173301310578633892187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83992115534207052422594791 125988173301310578633892187)
        ·
          refine ⟨188982259951965867950838281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125988173301310578633892187 188982259951965867950838281)
          ·
            refine ⟨141736694963974400963128711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188982259951965867950838281 141736694963974400963128711)
            ·
              refine ⟨212605042445961601444693067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141736694963974400963128711 212605042445961601444693067)
              ·
                refine ⟨318907563668942402167039601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212605042445961601444693067 318907563668942402167039601)
                ·
                  refine ⟨239180672751706801625279701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318907563668942402167039601 239180672751706801625279701)
                  ·
                    refine ⟨5605797017618128163092493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 239180672751706801625279701 5605797017618128163092493)
                    ·
                      refine ⟨2102173881606798061159685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5605797017618128163092493 2102173881606798061159685)
                      ·
                        rfl

theorem cell23_4093969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_4093969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093969 prefixEnd_4093969 := by exact prefixLift 4093969
  have htrace : WordTrace (prefixWord ++ tailWord_4093969) baseStart_4093969 baseEnd_4093969 := by
    simpa [prefixWord, tailWord_4093969, baseEnd_4093969] using wordTrace_append hprefix tailTrace_4093969
  have hstable : (prefixWord ++ tailWord_4093969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093969).length < 2 ^ (prefixWord ++ tailWord_4093969).sum := by decide
  have hdescent : baseEnd_4093969 < baseStart_4093969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4093980 : List Nat := [2, 2, 3, 1, 3, 2, 3, 1, 2, 4]
def baseStart_4093980 : Nat := 118140960795 + 4093980 * 2 ^ 59
def prefixEnd_4093980 : Nat := 4983230072969 + 3 ^ 40 * 4093980 * 2
def baseEnd_4093980 : Nat := 700726509964665839374045

theorem tailTrace_4093980 : CollatzResearch.WordTrace tailWord_4093980 prefixEnd_4093980 700726509964665839374045 := by
  unfold tailWord_4093980
  simp only [CollatzResearch.WordTrace]
  refine ⟨74659858854108565481631697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99546478472144753975508929 74659858854108565481631697)
  ·
    refine ⟨55994894140581424111223773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74659858854108565481631697 55994894140581424111223773)
    ·
      refine ⟨20998085302718034041708915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55994894140581424111223773 20998085302718034041708915)
      ·
        refine ⟨31497127954077051062563373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20998085302718034041708915 31497127954077051062563373)
        ·
          refine ⟨11811422982778894148461265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31497127954077051062563373 11811422982778894148461265)
          ·
            refine ⟨8858567237084170611345949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11811422982778894148461265 8858567237084170611345949)
            ·
              refine ⟨3321962713906563979254731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8858567237084170611345949 3321962713906563979254731)
              ·
                refine ⟨4982944070859845968882097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3321962713906563979254731 4982944070859845968882097)
                ·
                  refine ⟨3737208053144884476661573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4982944070859845968882097 3737208053144884476661573)
                  ·
                    refine ⟨700726509964665839374045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3737208053144884476661573 700726509964665839374045)
                    ·
                      rfl

theorem cell23_4093980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_4093980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4093980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4093980 prefixEnd_4093980 := by exact prefixLift 4093980
  have htrace : WordTrace (prefixWord ++ tailWord_4093980) baseStart_4093980 baseEnd_4093980 := by
    simpa [prefixWord, tailWord_4093980, baseEnd_4093980] using wordTrace_append hprefix tailTrace_4093980
  have hstable : (prefixWord ++ tailWord_4093980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4093980).length < 2 ^ (prefixWord ++ tailWord_4093980).sum := by decide
  have hdescent : baseEnd_4093980 < baseStart_4093980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4093980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094019 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 2, 6]
def baseStart_4094019 : Nat := 118140960795 + 4094019 * 2 ^ 59
def prefixEnd_4094019 : Nat := 4983230072969 + 3 ^ 40 * 4094019 * 2
def baseEnd_4094019 : Nat := 700733185213174288511485

theorem tailTrace_4094019 : CollatzResearch.WordTrace tailWord_4094019 prefixEnd_4094019 700733185213174288511485 := by
  unfold tailWord_4094019
  simp only [CollatzResearch.WordTrace]
  refine ⟨149321140155075840623933111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99547426770050560415955407 149321140155075840623933111)
  ·
    refine ⟨223981710232613760935899667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149321140155075840623933111 223981710232613760935899667)
    ·
      refine ⟨335972565348920641403849501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223981710232613760935899667 335972565348920641403849501)
      ·
        refine ⟨125989712005845240526443563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335972565348920641403849501 125989712005845240526443563)
        ·
          refine ⟨188984568008767860789665345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125989712005845240526443563 188984568008767860789665345)
          ·
            refine ⟨141738426006575895592249009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188984568008767860789665345 141738426006575895592249009)
            ·
              refine ⟨106303819504931921694186757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141738426006575895592249009 106303819504931921694186757)
              ·
                refine ⟨19931966157174735317660017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106303819504931921694186757 19931966157174735317660017)
                ·
                  refine ⟨14948974617881051488245013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19931966157174735317660017 14948974617881051488245013)
                  ·
                    refine ⟨700733185213174288511485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14948974617881051488245013 700733185213174288511485)
                    ·
                      rfl

theorem cell23_4094019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 6].length) (baseStart_4094019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094019 prefixEnd_4094019 := by exact prefixLift 4094019
  have htrace : WordTrace (prefixWord ++ tailWord_4094019) baseStart_4094019 baseEnd_4094019 := by
    simpa [prefixWord, tailWord_4094019, baseEnd_4094019] using wordTrace_append hprefix tailTrace_4094019
  have hstable : (prefixWord ++ tailWord_4094019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094019).length < 2 ^ (prefixWord ++ tailWord_4094019).sum := by decide
  have hdescent : baseEnd_4094019 < baseStart_4094019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094037 : List Nat := [1, 3, 2, 2, 1, 5, 2, 1, 2, 1, 3]
def baseStart_4094037 : Nat := 118140960795 + 4094037 * 2 ^ 59
def prefixEnd_4094037 : Nat := 4983230072969 + 3 ^ 40 * 4094037 * 2
def baseEnd_4094037 : Nat := 2102208798291303795109373

theorem tailTrace_4094037 : CollatzResearch.WordTrace tailWord_4094037 prefixEnd_4094037 2102208798291303795109373 := by
  unfold tailWord_4094037
  simp only [CollatzResearch.WordTrace]
  refine ⟨149321796669010629698088365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99547864446007086465392243 149321796669010629698088365)
  ·
    refine ⟨55995673750878986136783137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149321796669010629698088365 55995673750878986136783137)
    ·
      refine ⟨41996755313159239602587353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55995673750878986136783137 41996755313159239602587353)
      ·
        refine ⟨31497566484869429701940515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41996755313159239602587353 31497566484869429701940515)
        ·
          refine ⟨47246349727304144552910773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31497566484869429701940515 47246349727304144552910773)
          ·
            refine ⟨4429345286934763551835385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47246349727304144552910773 4429345286934763551835385)
            ·
              refine ⟨3322008965201072663876539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4429345286934763551835385 3322008965201072663876539)
              ·
                refine ⟨4983013447801608995814809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3322008965201072663876539 4983013447801608995814809)
                ·
                  refine ⟨3737260085851206746861107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4983013447801608995814809 3737260085851206746861107)
                  ·
                    refine ⟨5605890128776810120291661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3737260085851206746861107 5605890128776810120291661)
                    ·
                      refine ⟨2102208798291303795109373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5605890128776810120291661 2102208798291303795109373)
                      ·
                        rfl

theorem cell23_4094037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_4094037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094037 prefixEnd_4094037 := by exact prefixLift 4094037
  have htrace : WordTrace (prefixWord ++ tailWord_4094037) baseStart_4094037 baseEnd_4094037 := by
    simpa [prefixWord, tailWord_4094037, baseEnd_4094037] using wordTrace_append hprefix tailTrace_4094037
  have hstable : (prefixWord ++ tailWord_4094037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094037).length < 2 ^ (prefixWord ++ tailWord_4094037).sum := by decide
  have hdescent : baseEnd_4094037 < baseStart_4094037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094049 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 9]
def baseStart_4094049 : Nat := 118140960795 + 4094049 * 2 ^ 59
def prefixEnd_4094049 : Nat := 4983230072969 + 3 ^ 40 * 4094049 * 2
def baseEnd_4094049 : Nat := 233579440006573083128813

theorem tailTrace_4094049 : CollatzResearch.WordTrace tailWord_4094049 prefixEnd_4094049 233579440006573083128813 := by
  unfold tailWord_4094049
  simp only [CollatzResearch.WordTrace]
  refine ⟨149322234344967155747525201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99548156229978103831683467 149322234344967155747525201)
  ·
    refine ⟨111991675758725366810643901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149322234344967155747525201 111991675758725366810643901)
    ·
      refine ⟨41996878409522012553991463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111991675758725366810643901 41996878409522012553991463)
      ·
        refine ⟨62995317614283018830987195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41996878409522012553991463 62995317614283018830987195)
        ·
          refine ⟨94492976421424528246480793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62995317614283018830987195 94492976421424528246480793)
          ·
            refine ⟨70869732316068396184860595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94492976421424528246480793 70869732316068396184860595)
            ·
              refine ⟨106304598474102594277290893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70869732316068396184860595 106304598474102594277290893)
              ·
                refine ⟨39864224427788472853984085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106304598474102594277290893 39864224427788472853984085)
                ·
                  refine ⟨233579440006573083128813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39864224427788472853984085 233579440006573083128813)
                  ·
                    rfl

theorem cell23_4094049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 9].length) (baseStart_4094049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094049 prefixEnd_4094049 := by exact prefixLift 4094049
  have htrace : WordTrace (prefixWord ++ tailWord_4094049) baseStart_4094049 baseEnd_4094049 := by
    simpa [prefixWord, tailWord_4094049, baseEnd_4094049] using wordTrace_append hprefix tailTrace_4094049
  have hstable : (prefixWord ++ tailWord_4094049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094049).length < 2 ^ (prefixWord ++ tailWord_4094049).sum := by decide
  have hdescent : baseEnd_4094049 < baseStart_4094049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094077 : List Nat := [1, 4, 1, 1, 3, 3, 2, 2, 2, 2, 2]
def baseStart_4094077 : Nat := 118140960795 + 4094077 * 2 ^ 59
def prefixEnd_4094077 : Nat := 4983230072969 + 3 ^ 40 * 4094077 * 2
def baseEnd_4094077 : Nat := 2102229337517483638609189

theorem tailTrace_4094077 : CollatzResearch.WordTrace tailWord_4094077 prefixEnd_4094077 2102229337517483638609189 := by
  unfold tailWord_4094077
  simp only [CollatzResearch.WordTrace]
  refine ⟨149323255588865716529544485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99548837059243811019696323 149323255588865716529544485)
  ·
    refine ⟨27998110422912321849289591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149323255588865716529544485 27998110422912321849289591)
    ·
      refine ⟨41997165634368482773934387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27998110422912321849289591 41997165634368482773934387)
      ·
        refine ⟨62995748451552724160901581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41997165634368482773934387 62995748451552724160901581)
        ·
          refine ⟨23623405669332271560338093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62995748451552724160901581 23623405669332271560338093)
          ·
            refine ⟨8858777125999601835126785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23623405669332271560338093 8858777125999601835126785)
            ·
              refine ⟨6644082844499701376345089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8858777125999601835126785 6644082844499701376345089)
              ·
                refine ⟨4983062133374776032258817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6644082844499701376345089 4983062133374776032258817)
                ·
                  refine ⟨3737296600031082024194113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4983062133374776032258817 3737296600031082024194113)
                  ·
                    refine ⟨2802972450023311518145585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3737296600031082024194113 2802972450023311518145585)
                    ·
                      refine ⟨2102229337517483638609189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2802972450023311518145585 2102229337517483638609189)
                      ·
                        rfl

theorem cell23_4094077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_4094077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094077 prefixEnd_4094077 := by exact prefixLift 4094077
  have htrace : WordTrace (prefixWord ++ tailWord_4094077) baseStart_4094077 baseEnd_4094077 := by
    simpa [prefixWord, tailWord_4094077, baseEnd_4094077] using wordTrace_append hprefix tailTrace_4094077
  have hstable : (prefixWord ++ tailWord_4094077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094077).length < 2 ^ (prefixWord ++ tailWord_4094077).sum := by decide
  have hdescent : baseEnd_4094077 < baseStart_4094077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094083 : List Nat := [1, 1, 1, 3, 3, 4, 1, 4, 5]
def baseStart_4094083 : Nat := 118140960795 + 4094083 * 2 ^ 59
def prefixEnd_4094083 : Nat := 4983230072969 + 3 ^ 40 * 4094083 * 2
def baseEnd_4094083 : Nat := 233581379822378957237129

theorem tailTrace_4094083 : CollatzResearch.WordTrace tailWord_4094083 prefixEnd_4094083 233581379822378957237129 := by
  unfold tailWord_4094083
  simp only [CollatzResearch.WordTrace]
  refine ⟨149323474426843979554262903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99548982951229319702841935 149323474426843979554262903)
  ·
    refine ⟨223985211640265969331394355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149323474426843979554262903 223985211640265969331394355)
    ·
      refine ⟨335977817460398953997091533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223985211640265969331394355 335977817460398953997091533)
      ·
        refine ⟨125991681547649607748909325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335977817460398953997091533 125991681547649607748909325)
        ·
          refine ⟨47246880580368602905840997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125991681547649607748909325 47246880580368602905840997)
          ·
            refine ⟨8858790108819113044845187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47246880580368602905840997 8858790108819113044845187)
            ·
              refine ⟨13288185163228669567267781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8858790108819113044845187 13288185163228669567267781)
              ·
                refine ⟨2491534718105375543862709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13288185163228669567267781 2491534718105375543862709)
                ·
                  refine ⟨233581379822378957237129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2491534718105375543862709 233581379822378957237129)
                  ·
                    rfl

theorem cell23_4094083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 5].length) (baseStart_4094083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094083 prefixEnd_4094083 := by exact prefixLift 4094083
  have htrace : WordTrace (prefixWord ++ tailWord_4094083) baseStart_4094083 baseEnd_4094083 := by
    simpa [prefixWord, tailWord_4094083, baseEnd_4094083] using wordTrace_append hprefix tailTrace_4094083
  have hstable : (prefixWord ++ tailWord_4094083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094083).length < 2 ^ (prefixWord ++ tailWord_4094083).sum := by decide
  have hdescent : baseEnd_4094083 < baseStart_4094083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094100 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 7]
def baseStart_4094100 : Nat := 118140960795 + 4094100 * 2 ^ 59
def prefixEnd_4094100 : Nat := 4983230072969 + 3 ^ 40 * 4094100 * 2
def baseEnd_4094100 : Nat := 233582349730281894291287

theorem tailTrace_4094100 : CollatzResearch.WordTrace tailWord_4094100 prefixEnd_4094100 233582349730281894291287 := by
  unfold tailWord_4094100
  simp only [CollatzResearch.WordTrace]
  refine ⟨74662047233891195728815877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99549396311854927638421169 74662047233891195728815877)
  ·
    refine ⟨13999133856354599199152977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74662047233891195728815877 13999133856354599199152977)
    ·
      refine ⟨10499350392265949399364733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13999133856354599199152977 10499350392265949399364733)
      ·
        refine ⟨3937256397099731024761775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10499350392265949399364733 3937256397099731024761775)
        ·
          refine ⟨5905884595649596537142663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3937256397099731024761775 5905884595649596537142663)
          ·
            refine ⟨8858826893474394805713995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5905884595649596537142663 8858826893474394805713995)
            ·
              refine ⟨13288240340211592208570993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8858826893474394805713995 13288240340211592208570993)
              ·
                refine ⟨9966180255158694156428245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13288240340211592208570993 9966180255158694156428245)
                ·
                  refine ⟨233582349730281894291287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9966180255158694156428245 233582349730281894291287)
                  ·
                    rfl

theorem cell23_4094100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_4094100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094100 prefixEnd_4094100 := by exact prefixLift 4094100
  have htrace : WordTrace (prefixWord ++ tailWord_4094100) baseStart_4094100 baseEnd_4094100 := by
    simpa [prefixWord, tailWord_4094100, baseEnd_4094100] using wordTrace_append hprefix tailTrace_4094100
  have hstable : (prefixWord ++ tailWord_4094100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094100).length < 2 ^ (prefixWord ++ tailWord_4094100).sum := by decide
  have hdescent : baseEnd_4094100 < baseStart_4094100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094113 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 2, 5]
def baseStart_4094113 : Nat := 118140960795 + 4094113 * 2 ^ 59
def prefixEnd_4094113 : Nat := 4983230072969 + 3 ^ 40 * 4094113 * 2
def baseEnd_4094113 : Nat := 700749274273681832586341

theorem tailTrace_4094113 : CollatzResearch.WordTrace tailWord_4094113 prefixEnd_4094113 700749274273681832586341 := by
  unfold tailWord_4094113
  simp only [CollatzResearch.WordTrace]
  refine ⟨149324568616735294677854993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99549712411156863118569995 149324568616735294677854993)
  ·
    refine ⟨111993426462551471008391245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149324568616735294677854993 111993426462551471008391245)
    ·
      refine ⟨41997534923456801628146717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111993426462551471008391245 41997534923456801628146717)
      ·
        refine ⟨15749075596296300610555019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41997534923456801628146717 15749075596296300610555019)
        ·
          refine ⟨23623613394444450915832529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15749075596296300610555019 23623613394444450915832529)
          ·
            refine ⟨17717710045833338186874397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23623613394444450915832529 17717710045833338186874397)
            ·
              refine ⟨6644141267187501820077899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17717710045833338186874397 6644141267187501820077899)
              ·
                refine ⟨9966211900781252730116849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6644141267187501820077899 9966211900781252730116849)
                ·
                  refine ⟨7474658925585939547587637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9966211900781252730116849 7474658925585939547587637)
                  ·
                    refine ⟨700749274273681832586341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7474658925585939547587637 700749274273681832586341)
                    ·
                      rfl

theorem cell23_4094113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_4094113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094113 prefixEnd_4094113 := by exact prefixLift 4094113
  have htrace : WordTrace (prefixWord ++ tailWord_4094113) baseStart_4094113 baseEnd_4094113 := by
    simpa [prefixWord, tailWord_4094113, baseEnd_4094113] using wordTrace_append hprefix tailTrace_4094113
  have hstable : (prefixWord ++ tailWord_4094113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094113).length < 2 ^ (prefixWord ++ tailWord_4094113).sum := by decide
  have hdescent : baseEnd_4094113 < baseStart_4094113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094173 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 8]
def baseStart_4094173 : Nat := 118140960795 + 4094173 * 2 ^ 59
def prefixEnd_4094173 : Nat := 4983230072969 + 3 ^ 40 * 4094173 * 2
def baseEnd_4094173 : Nat := 233586514628923918112083

theorem tailTrace_4094173 : CollatzResearch.WordTrace tailWord_4094173 prefixEnd_4094173 233586514628923918112083 := by
  unfold tailWord_4094173
  simp only [CollatzResearch.WordTrace]
  refine ⟨149326756996517924925039173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99551171331011949950026115 149326756996517924925039173)
  ·
    refine ⟨27998766936847110923444845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149326756996517924925039173 27998766936847110923444845)
    ·
      refine ⟨10499537601317666596291817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27998766936847110923444845 10499537601317666596291817)
      ·
        refine ⟨7874653200988249947218863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10499537601317666596291817 7874653200988249947218863)
        ·
          refine ⟨11811979801482374920828295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7874653200988249947218863 11811979801482374920828295)
          ·
            refine ⟨17717969702223562381242443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11811979801482374920828295 17717969702223562381242443)
            ·
              refine ⟨26576954553335343571863665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17717969702223562381242443 26576954553335343571863665)
              ·
                refine ⟨19932715915001507678897749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26576954553335343571863665 19932715915001507678897749)
                ·
                  refine ⟨233586514628923918112083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19932715915001507678897749 233586514628923918112083)
                  ·
                    rfl

theorem cell23_4094173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_4094173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094173 prefixEnd_4094173 := by exact prefixLift 4094173
  have htrace : WordTrace (prefixWord ++ tailWord_4094173) baseStart_4094173 baseEnd_4094173 := by
    simpa [prefixWord, tailWord_4094173, baseEnd_4094173] using wordTrace_append hprefix tailTrace_4094173
  have hstable : (prefixWord ++ tailWord_4094173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094173).length < 2 ^ (prefixWord ++ tailWord_4094173).sum := by decide
  have hdescent : baseEnd_4094173 < baseStart_4094173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094194 : List Nat := [3, 2, 1, 3, 2, 2, 3, 2, 1, 4]
def baseStart_4094194 : Nat := 118140960795 + 4094194 * 2 ^ 59
def prefixEnd_4094194 : Nat := 4983230072969 + 3 ^ 40 * 4094194 * 2
def baseEnd_4094194 : Nat := 700763138251353226948717

theorem tailTrace_4094194 : CollatzResearch.WordTrace tailWord_4094194 prefixEnd_4094194 700763138251353226948717 := by
  unfold tailWord_4094194
  simp only [CollatzResearch.WordTrace]
  refine ⟨37331880732360461377888409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99551681952961230341035757 37331880732360461377888409)
  ·
    refine ⟨27998910549270346033416307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37331880732360461377888409 27998910549270346033416307)
    ·
      refine ⟨41998365823905519050124461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27998910549270346033416307 41998365823905519050124461)
      ·
        refine ⟨15749387183964569643796673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41998365823905519050124461 15749387183964569643796673)
        ·
          refine ⟨11812040387973427232847505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15749387183964569643796673 11812040387973427232847505)
          ·
            refine ⟨8859030290980070424635629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11812040387973427232847505 8859030290980070424635629)
            ·
              refine ⟨3322136359117526409238361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8859030290980070424635629 3322136359117526409238361)
              ·
                refine ⟨2491602269338144806928771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3322136359117526409238361 2491602269338144806928771)
                ·
                  refine ⟨3737403404007217210393157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491602269338144806928771 3737403404007217210393157)
                  ·
                    refine ⟨700763138251353226948717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3737403404007217210393157 700763138251353226948717)
                    ·
                      rfl

theorem cell23_4094194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_4094194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094194 prefixEnd_4094194 := by exact prefixLift 4094194
  have htrace : WordTrace (prefixWord ++ tailWord_4094194) baseStart_4094194 baseEnd_4094194 := by
    simpa [prefixWord, tailWord_4094194, baseEnd_4094194] using wordTrace_append hprefix tailTrace_4094194
  have hstable : (prefixWord ++ tailWord_4094194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094194).length < 2 ^ (prefixWord ++ tailWord_4094194).sum := by decide
  have hdescent : baseEnd_4094194 < baseStart_4094194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094223 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 2, 6, 2]
def baseStart_4094223 : Nat := 118140960795 + 4094223 * 2 ^ 59
def prefixEnd_4094223 : Nat := 4983230072969 + 3 ^ 40 * 4094223 * 2
def baseEnd_4094223 : Nat := 2102304305693040067383517

theorem tailTrace_4094223 : CollatzResearch.WordTrace tailWord_4094223 prefixEnd_4094223 2102304305693040067383517 := by
  unfold tailWord_4094223
  simp only [CollatzResearch.WordTrace]
  refine ⟨149328580646336783464359323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99552387097557855642906215 149328580646336783464359323)
  ·
    refine ⟨223992870969505175196538985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149328580646336783464359323 223992870969505175196538985)
    ·
      refine ⟨167994653227128881397404239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223992870969505175196538985 167994653227128881397404239)
      ·
        refine ⟨251991979840693322096106359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167994653227128881397404239 251991979840693322096106359)
        ·
          refine ⟨377987969761039983144159539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251991979840693322096106359 377987969761039983144159539)
          ·
            refine ⟨566981954641559974716239309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377987969761039983144159539 566981954641559974716239309)
            ·
              refine ⟨212618232990584990518589741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 566981954641559974716239309 212618232990584990518589741)
              ·
                refine ⟨79731837371469371444471153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212618232990584990518589741 79731837371469371444471153)
                ·
                  refine ⟨59798878028602028583353365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79731837371469371444471153 59798878028602028583353365)
                  ·
                    refine ⟨2803072407590720089844689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59798878028602028583353365 2803072407590720089844689)
                    ·
                      refine ⟨2102304305693040067383517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2803072407590720089844689 2102304305693040067383517)
                      ·
                        rfl

theorem cell23_4094223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 6, 2].length) (baseStart_4094223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094223 prefixEnd_4094223 := by exact prefixLift 4094223
  have htrace : WordTrace (prefixWord ++ tailWord_4094223) baseStart_4094223 baseEnd_4094223 := by
    simpa [prefixWord, tailWord_4094223, baseEnd_4094223] using wordTrace_append hprefix tailTrace_4094223
  have hstable : (prefixWord ++ tailWord_4094223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094223).length < 2 ^ (prefixWord ++ tailWord_4094223).sum := by decide
  have hdescent : baseEnd_4094223 < baseStart_4094223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094256 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 7]
def baseStart_4094256 : Nat := 118140960795 + 4094256 * 2 ^ 59
def prefixEnd_4094256 : Nat := 4983230072969 + 3 ^ 40 * 4094256 * 2
def baseEnd_4094256 : Nat := 2102321250554638438270865

theorem tailTrace_4094256 : CollatzResearch.WordTrace tailWord_4094256 prefixEnd_4094256 2102321250554638438270865 := by
  unfold tailWord_4094256
  simp only [CollatzResearch.WordTrace]
  refine ⟨74664892127608615050155311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99553189503478153400207081 74664892127608615050155311)
  ·
    refine ⟨111997338191412922575232967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74664892127608615050155311 111997338191412922575232967)
    ·
      refine ⟨167996007287119383862849451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111997338191412922575232967 167996007287119383862849451)
      ·
        refine ⟨251994010930679075794274177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167996007287119383862849451 251994010930679075794274177)
        ·
          refine ⟨188995508198009306845705633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251994010930679075794274177 188995508198009306845705633)
          ·
            refine ⟨141746631148506980134279225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188995508198009306845705633 141746631148506980134279225)
            ·
              refine ⟨106309973361380235100709419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141746631148506980134279225 106309973361380235100709419)
              ·
                refine ⟨159464960042070352651064129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106309973361380235100709419 159464960042070352651064129)
                ·
                  refine ⟨119598720031552764488298097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159464960042070352651064129 119598720031552764488298097)
                  ·
                    refine ⟨89699040023664573366223573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119598720031552764488298097 89699040023664573366223573)
                    ·
                      refine ⟨2102321250554638438270865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89699040023664573366223573 2102321250554638438270865)
                      ·
                        rfl

theorem cell23_4094256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_4094256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094256 prefixEnd_4094256 := by exact prefixLift 4094256
  have htrace : WordTrace (prefixWord ++ tailWord_4094256) baseStart_4094256 baseEnd_4094256 := by
    simpa [prefixWord, tailWord_4094256, baseEnd_4094256] using wordTrace_append hprefix tailTrace_4094256
  have hstable : (prefixWord ++ tailWord_4094256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094256).length < 2 ^ (prefixWord ++ tailWord_4094256).sum := by decide
  have hdescent : baseEnd_4094256 < baseStart_4094256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094270 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_4094270 : Nat := 118140960795 + 4094270 * 2 ^ 59
def prefixEnd_4094270 : Nat := 4983230072969 + 3 ^ 40 * 4094270 * 2
def baseEnd_4094270 : Nat := 2102328439283801383495801

theorem tailTrace_4094270 : CollatzResearch.WordTrace tailWord_4094270 prefixEnd_4094270 2102328439283801383495801 := by
  unfold tailWord_4094270
  simp only [CollatzResearch.WordTrace]
  refine ⟨18666286859645813811415033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99553529918111006994213509 18666286859645813811415033)
  ·
    refine ⟨13999715144734360358561275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18666286859645813811415033 13999715144734360358561275)
    ·
      refine ⟨20999572717101540537841913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13999715144734360358561275 20999572717101540537841913)
      ·
        refine ⟨15749679537826155403381435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20999572717101540537841913 15749679537826155403381435)
        ·
          refine ⟨23624519306739233105072153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15749679537826155403381435 23624519306739233105072153)
          ·
            refine ⟨17718389480054424828804115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23624519306739233105072153 17718389480054424828804115)
            ·
              refine ⟨26577584220081637243206173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17718389480054424828804115 26577584220081637243206173)
              ·
                refine ⟨9966594082530613966202315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26577584220081637243206173 9966594082530613966202315)
                ·
                  refine ⟨14949891123795920949303473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9966594082530613966202315 14949891123795920949303473)
                  ·
                    refine ⟨11212418342846940711977605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14949891123795920949303473 11212418342846940711977605)
                    ·
                      refine ⟨2102328439283801383495801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11212418342846940711977605 2102328439283801383495801)
                      ·
                        rfl

theorem cell23_4094270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_4094270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094270 prefixEnd_4094270 := by exact prefixLift 4094270
  have htrace : WordTrace (prefixWord ++ tailWord_4094270) baseStart_4094270 baseEnd_4094270 := by
    simpa [prefixWord, tailWord_4094270, baseEnd_4094270] using wordTrace_append hprefix tailTrace_4094270
  have hstable : (prefixWord ++ tailWord_4094270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094270).length < 2 ^ (prefixWord ++ tailWord_4094270).sum := by decide
  have hdescent : baseEnd_4094270 < baseStart_4094270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094290 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_4094290 : Nat := 118140960795 + 4094290 * 2 ^ 59
def prefixEnd_4094290 : Nat := 4983230072969 + 3 ^ 40 * 4094290 * 2
def baseEnd_4094290 : Nat := 2102338708896891305245709

theorem tailTrace_4094290 : CollatzResearch.WordTrace tailWord_4094290 prefixEnd_4094290 2102338708896891305245709 := by
  unfold tailWord_4094290
  simp only [CollatzResearch.WordTrace]
  refine ⟨37332756084273513476762081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99554016224729369271365549 37332756084273513476762081)
  ·
    refine ⟨27999567063205135107571561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37332756084273513476762081 27999567063205135107571561)
    ·
      refine ⟨20999675297403851330678671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27999567063205135107571561 20999675297403851330678671)
      ·
        refine ⟨31499512946105776996018007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20999675297403851330678671 31499512946105776996018007)
        ·
          refine ⟨47249269419158665494027011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31499512946105776996018007 47249269419158665494027011)
          ·
            refine ⟨70873904128737998241040517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47249269419158665494027011 70873904128737998241040517)
            ·
              refine ⟨13288857024138374670195097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70873904128737998241040517 13288857024138374670195097)
              ·
                refine ⟨9966642768103781002646323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13288857024138374670195097 9966642768103781002646323)
                ·
                  refine ⟨14949964152155671503969485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9966642768103781002646323 14949964152155671503969485)
                  ·
                    refine ⟨5606236557058376813988557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14949964152155671503969485 5606236557058376813988557)
                    ·
                      refine ⟨2102338708896891305245709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5606236557058376813988557 2102338708896891305245709)
                      ·
                        rfl

theorem cell23_4094290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_4094290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094290 prefixEnd_4094290 := by exact prefixLift 4094290
  have htrace : WordTrace (prefixWord ++ tailWord_4094290) baseStart_4094290 baseEnd_4094290 := by
    simpa [prefixWord, tailWord_4094290, baseEnd_4094290] using wordTrace_append hprefix tailTrace_4094290
  have hstable : (prefixWord ++ tailWord_4094290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094290).length < 2 ^ (prefixWord ++ tailWord_4094290).sum := by decide
  have hdescent : baseEnd_4094290 < baseStart_4094290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094347 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 4, 2, 2]
def baseStart_4094347 : Nat := 118140960795 + 4094347 * 2 ^ 59
def prefixEnd_4094347 : Nat := 4983230072969 + 3 ^ 40 * 4094347 * 2
def baseEnd_4094347 : Nat := 2102367977294197582232947

theorem tailTrace_4094347 : CollatzResearch.WordTrace tailWord_4094347 prefixEnd_4094347 2102367977294197582232947 := by
  unfold tailWord_4094347
  simp only [CollatzResearch.WordTrace]
  refine ⟨149333103297887552641873295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99555402198591701761248863 149333103297887552641873295)
  ·
    refine ⟨223999654946831328962809943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149333103297887552641873295 223999654946831328962809943)
    ·
      refine ⟨335999482420246993444214915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223999654946831328962809943 335999482420246993444214915)
      ·
        refine ⟨503999223630370490166322373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335999482420246993444214915 503999223630370490166322373)
        ·
          refine ⟨94499854430694466906185445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 503999223630370490166322373 94499854430694466906185445)
          ·
            refine ⟨17718722705755212544909771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94499854430694466906185445 17718722705755212544909771)
            ·
              refine ⟨26578084058632818817364657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17718722705755212544909771 26578084058632818817364657)
              ·
                refine ⟨19933563043974614113023493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26578084058632818817364657 19933563043974614113023493)
                ·
                  refine ⟨3737543070745240146191905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19933563043974614113023493 3737543070745240146191905)
                  ·
                    refine ⟨2803157303058930109643929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3737543070745240146191905 2803157303058930109643929)
                    ·
                      refine ⟨2102367977294197582232947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2803157303058930109643929 2102367977294197582232947)
                      ·
                        rfl

theorem cell23_4094347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 2, 2].length) (baseStart_4094347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094347 prefixEnd_4094347 := by exact prefixLift 4094347
  have htrace : WordTrace (prefixWord ++ tailWord_4094347) baseStart_4094347 baseEnd_4094347 := by
    simpa [prefixWord, tailWord_4094347, baseEnd_4094347] using wordTrace_append hprefix tailTrace_4094347
  have hstable : (prefixWord ++ tailWord_4094347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094347).length < 2 ^ (prefixWord ++ tailWord_4094347).sum := by decide
  have hdescent : baseEnd_4094347 < baseStart_4094347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094350 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_4094350 : Nat := 118140960795 + 4094350 * 2 ^ 59
def prefixEnd_4094350 : Nat := 4983230072969 + 3 ^ 40 * 4094350 * 2
def baseEnd_4094350 : Nat := 2102369517736161070495433

theorem tailTrace_4094350 : CollatzResearch.WordTrace tailWord_4094350 prefixEnd_4094350 2102369517736161070495433 := by
  unfold tailWord_4094350
  simp only [CollatzResearch.WordTrace]
  refine ⟨18666651589609585519279063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99555475144584456102821669 18666651589609585519279063)
  ·
    refine ⟨27999977384414378278918595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18666651589609585519279063 27999977384414378278918595)
    ·
      refine ⟨41999966076621567418377893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27999977384414378278918595 41999966076621567418377893)
      ·
        refine ⟨7874993639366543890945855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41999966076621567418377893 7874993639366543890945855)
        ·
          refine ⟨11812490459049815836418783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7874993639366543890945855 11812490459049815836418783)
          ·
            refine ⟨17718735688574723754628175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11812490459049815836418783 17718735688574723754628175)
            ·
              refine ⟨26578103532862085631942263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17718735688574723754628175 26578103532862085631942263)
              ·
                refine ⟨39867155299293128447913395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26578103532862085631942263 39867155299293128447913395)
                ·
                  refine ⟨59800732948939692671870093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39867155299293128447913395 59800732948939692671870093)
                  ·
                    refine ⟨22425274855852384751951285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59800732948939692671870093 22425274855852384751951285)
                    ·
                      refine ⟨2102369517736161070495433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22425274855852384751951285 2102369517736161070495433)
                      ·
                        rfl

theorem cell23_4094350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_4094350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094350 prefixEnd_4094350 := by exact prefixLift 4094350
  have htrace : WordTrace (prefixWord ++ tailWord_4094350) baseStart_4094350 baseEnd_4094350 := by
    simpa [prefixWord, tailWord_4094350, baseEnd_4094350] using wordTrace_append hprefix tailTrace_4094350
  have hstable : (prefixWord ++ tailWord_4094350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094350).length < 2 ^ (prefixWord ++ tailWord_4094350).sum := by decide
  have hdescent : baseEnd_4094350 < baseStart_4094350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094363 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 3]
def baseStart_4094363 : Nat := 118140960795 + 4094363 * 2 ^ 59
def prefixEnd_4094363 : Nat := 4983230072969 + 3 ^ 40 * 4094363 * 2
def baseEnd_4094363 : Nat := 2102376192984669519632873

theorem tailTrace_4094363 : CollatzResearch.WordTrace tailWord_4094363 prefixEnd_4094363 2102376192984669519632873 := by
  unfold tailWord_4094363
  simp only [CollatzResearch.WordTrace]
  refine ⟨149333686865829587374455743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99555791243886391582970495 149333686865829587374455743)
  ·
    refine ⟨224000530298744381061683615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149333686865829587374455743 224000530298744381061683615)
    ·
      refine ⟨336000795448116571592525423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224000530298744381061683615 336000795448116571592525423)
      ·
        refine ⟨504001193172174857388788135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336000795448116571592525423 504001193172174857388788135)
        ·
          refine ⟨756001789758262286083182203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504001193172174857388788135 756001789758262286083182203)
          ·
            refine ⟨1134002684637393429124773305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756001789758262286083182203 1134002684637393429124773305)
            ·
              refine ⟨850502013478045071843579979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1134002684637393429124773305 850502013478045071843579979)
              ·
                refine ⟨1275753020217067607765369969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850502013478045071843579979 1275753020217067607765369969)
                ·
                  refine ⟨956814765162800705824027477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1275753020217067607765369969 956814765162800705824027477)
                  ·
                    refine ⟨5606336514625785385687661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 956814765162800705824027477 5606336514625785385687661)
                    ·
                      refine ⟨2102376192984669519632873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5606336514625785385687661 2102376192984669519632873)
                      ·
                        rfl

theorem cell23_4094363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 3].length) (baseStart_4094363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094363 prefixEnd_4094363 := by exact prefixLift 4094363
  have htrace : WordTrace (prefixWord ++ tailWord_4094363) baseStart_4094363 baseEnd_4094363 := by
    simpa [prefixWord, tailWord_4094363, baseEnd_4094363] using wordTrace_append hprefix tailTrace_4094363
  have hstable : (prefixWord ++ tailWord_4094363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094363).length < 2 ^ (prefixWord ++ tailWord_4094363).sum := by decide
  have hdescent : baseEnd_4094363 < baseStart_4094363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094457 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 2, 2, 3]
def baseStart_4094457 : Nat := 118140960795 + 4094457 * 2 ^ 59
def prefixEnd_4094457 : Nat := 4983230072969 + 3 ^ 40 * 4094457 * 2
def baseEnd_4094457 : Nat := 2102424460166192151857441

theorem tailTrace_4094457 : CollatzResearch.WordTrace tailWord_4094457 prefixEnd_4094457 2102424460166192151857441 := by
  unfold tailWord_4094457
  simp only [CollatzResearch.WordTrace]
  refine ⟨149337115327489041428377625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99558076884992694285585083 149337115327489041428377625)
  ·
    refine ⟨112002836495616781071283219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149337115327489041428377625 112002836495616781071283219)
    ·
      refine ⟨168004254743425171606924829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112002836495616781071283219 168004254743425171606924829)
      ·
        refine ⟨63001595528784439352596811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168004254743425171606924829 63001595528784439352596811)
        ·
          refine ⟨94502393293176659028895217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63001595528784439352596811 94502393293176659028895217)
          ·
            refine ⟨70876794969882494271671413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94502393293176659028895217 70876794969882494271671413)
            ·
              refine ⟨6644699528426483837969195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70876794969882494271671413 6644699528426483837969195)
              ·
                refine ⟨9967049292639725756953793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6644699528426483837969195 9967049292639725756953793)
                ·
                  refine ⟨7475286969479794317715345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9967049292639725756953793 7475286969479794317715345)
                  ·
                    refine ⟨5606465227109845738286509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7475286969479794317715345 5606465227109845738286509)
                    ·
                      refine ⟨2102424460166192151857441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5606465227109845738286509 2102424460166192151857441)
                      ·
                        rfl

theorem cell23_4094457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_4094457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094457 prefixEnd_4094457 := by exact prefixLift 4094457
  have htrace : WordTrace (prefixWord ++ tailWord_4094457) baseStart_4094457 baseEnd_4094457 := by
    simpa [prefixWord, tailWord_4094457, baseEnd_4094457] using wordTrace_append hprefix tailTrace_4094457
  have hstable : (prefixWord ++ tailWord_4094457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094457).length < 2 ^ (prefixWord ++ tailWord_4094457).sum := by decide
  have hdescent : baseEnd_4094457 < baseStart_4094457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094490 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 5, 5]
def baseStart_4094490 : Nat := 118140960795 + 4094490 * 2 ^ 59
def prefixEnd_4094490 : Nat := 4983230072969 + 3 ^ 40 * 4094490 * 2
def baseEnd_4094490 : Nat := 700813801675930174248263

theorem tailTrace_4094490 : CollatzResearch.WordTrace tailWord_4094490 prefixEnd_4094490 700813801675930174248263 := by
  unfold tailWord_4094490
  simp only [CollatzResearch.WordTrace]
  refine ⟨37334579734092372016082231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99558879290912992042885949 37334579734092372016082231)
  ·
    refine ⟨56001869601138558024123347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37334579734092372016082231 56001869601138558024123347)
    ·
      refine ⟨84002804401707837036185021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56001869601138558024123347 84002804401707837036185021)
      ·
        refine ⟨31501051650640438888569383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84002804401707837036185021 31501051650640438888569383)
        ·
          refine ⟨47251577475960658332854075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31501051650640438888569383 47251577475960658332854075)
          ·
            refine ⟨70877366213940987499281113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47251577475960658332854075 70877366213940987499281113)
            ·
              refine ⟨53158024660455740624460835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70877366213940987499281113 53158024660455740624460835)
              ·
                refine ⟨79737036990683610936691253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53158024660455740624460835 79737036990683610936691253)
                ·
                  refine ⟨7475347217876588525314805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79737036990683610936691253 7475347217876588525314805)
                  ·
                    refine ⟨700813801675930174248263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7475347217876588525314805 700813801675930174248263)
                    ·
                      rfl

theorem cell23_4094490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_4094490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094490 prefixEnd_4094490 := by exact prefixLift 4094490
  have htrace : WordTrace (prefixWord ++ tailWord_4094490) baseStart_4094490 baseEnd_4094490 := by
    simpa [prefixWord, tailWord_4094490, baseEnd_4094490] using wordTrace_append hprefix tailTrace_4094490
  have hstable : (prefixWord ++ tailWord_4094490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094490).length < 2 ^ (prefixWord ++ tailWord_4094490).sum := by decide
  have hdescent : baseEnd_4094490 < baseStart_4094490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094497 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 3, 5, 2]
def baseStart_4094497 : Nat := 118140960795 + 4094497 * 2 ^ 59
def prefixEnd_4094497 : Nat := 4983230072969 + 3 ^ 40 * 4094497 * 2
def baseEnd_4094497 : Nat := 2102444999392371995357257

theorem tailTrace_4094497 : CollatzResearch.WordTrace tailWord_4094497 prefixEnd_4094497 2102444999392371995357257 := by
  unfold tailWord_4094497
  simp only [CollatzResearch.WordTrace]
  refine ⟨149338574247344128259833745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99559049498229418839889163 149338574247344128259833745)
  ·
    refine ⟨112003930685508096194875309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149338574247344128259833745 112003930685508096194875309)
    ·
      refine ⟨42001474007065536073078241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112003930685508096194875309 42001474007065536073078241)
      ·
        refine ⟨31501105505299152054808681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42001474007065536073078241 31501105505299152054808681)
        ·
          refine ⟨23625829128974364041106511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31501105505299152054808681 23625829128974364041106511)
          ·
            refine ⟨35438743693461546061659767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23625829128974364041106511 35438743693461546061659767)
            ·
              refine ⟨53158115540192319092489651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35438743693461546061659767 53158115540192319092489651)
              ·
                refine ⟨79737173310288478638734477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53158115540192319092489651 79737173310288478638734477)
                ·
                  refine ⟨29901439991358179489525429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79737173310288478638734477 29901439991358179489525429)
                  ·
                    refine ⟨2803259999189829327143009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29901439991358179489525429 2803259999189829327143009)
                    ·
                      refine ⟨2102444999392371995357257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2803259999189829327143009 2102444999392371995357257)
                      ·
                        rfl

theorem cell23_4094497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_4094497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094497 prefixEnd_4094497 := by exact prefixLift 4094497
  have htrace : WordTrace (prefixWord ++ tailWord_4094497) baseStart_4094497 baseEnd_4094497 := by
    simpa [prefixWord, tailWord_4094497, baseEnd_4094497] using wordTrace_append hprefix tailTrace_4094497
  have hstable : (prefixWord ++ tailWord_4094497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094497).length < 2 ^ (prefixWord ++ tailWord_4094497).sum := by decide
  have hdescent : baseEnd_4094497 < baseStart_4094497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094520 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 3, 6]
def baseStart_4094520 : Nat := 118140960795 + 4094520 * 2 ^ 59
def prefixEnd_4094520 : Nat := 4983230072969 + 3 ^ 40 * 4094520 * 2
def baseEnd_4094520 : Nat := 700818936482475135123217

theorem tailTrace_4094520 : CollatzResearch.WordTrace tailWord_4094520 prefixEnd_4094520 700818936482475135123217 := by
  unfold tailWord_4094520
  simp only [CollatzResearch.WordTrace]
  refine ⟨74669706563130401593960507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99559608750840535458614009 74669706563130401593960507)
  ·
    refine ⟨112004559844695602390940761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74669706563130401593960507 112004559844695602390940761)
    ·
      refine ⟨84003419883521701793205571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112004559844695602390940761 84003419883521701793205571)
      ·
        refine ⟨126005129825282552689808357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84003419883521701793205571 126005129825282552689808357)
        ·
          refine ⟨23625961842240478629339067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126005129825282552689808357 23625961842240478629339067)
          ·
            refine ⟨35438942763360717944008601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23625961842240478629339067 35438942763360717944008601)
            ·
              refine ⟨26579207072520538458006451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35438942763360717944008601 26579207072520538458006451)
              ·
                refine ⟨39868810608780807687009677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26579207072520538458006451 39868810608780807687009677)
                ·
                  refine ⟨14950803978292802882628629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39868810608780807687009677 14950803978292802882628629)
                  ·
                    refine ⟨700818936482475135123217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14950803978292802882628629 700818936482475135123217)
                    ·
                      rfl

theorem cell23_4094520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_4094520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094520 prefixEnd_4094520 := by exact prefixLift 4094520
  have htrace : WordTrace (prefixWord ++ tailWord_4094520) baseStart_4094520 baseEnd_4094520 := by
    simpa [prefixWord, tailWord_4094520, baseEnd_4094520] using wordTrace_append hprefix tailTrace_4094520
  have hstable : (prefixWord ++ tailWord_4094520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094520).length < 2 ^ (prefixWord ++ tailWord_4094520).sum := by decide
  have hdescent : baseEnd_4094520 < baseStart_4094520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094527 : List Nat := [1, 1, 2, 2, 3, 2, 1, 5, 1, 1, 4]
def baseStart_4094527 : Nat := 118140960795 + 4094527 * 2 ^ 59
def prefixEnd_4094527 : Nat := 4983230072969 + 3 ^ 40 * 4094527 * 2
def baseEnd_4094527 : Nat := 2102460403812006877982119

theorem tailTrace_4094527 : CollatzResearch.WordTrace tailWord_4094527 prefixEnd_4094527 2102460403812006877982119 := by
  unfold tailWord_4094527
  simp only [CollatzResearch.WordTrace]
  refine ⟨149339668437235443383425835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99559778958156962255617223 149339668437235443383425835)
  ·
    refine ⟨224009502655853165075138753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149339668437235443383425835 224009502655853165075138753)
    ·
      refine ⟨168007126991889873806354065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224009502655853165075138753 168007126991889873806354065)
      ·
        refine ⟨126005345243917405354765549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168007126991889873806354065 126005345243917405354765549)
        ·
          refine ⟨47252004466469027008037081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126005345243917405354765549 47252004466469027008037081)
          ·
            refine ⟨35439003349851770256027811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47252004466469027008037081 35439003349851770256027811)
            ·
              refine ⟨53158505024777655384041717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35439003349851770256027811 53158505024777655384041717)
              ·
                refine ⟨4983609846072905192253911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53158505024777655384041717 4983609846072905192253911)
                ·
                  refine ⟨7475414769109357788380867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4983609846072905192253911 7475414769109357788380867)
                  ·
                    refine ⟨11213122153664036682571301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7475414769109357788380867 11213122153664036682571301)
                    ·
                      refine ⟨2102460403812006877982119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11213122153664036682571301 2102460403812006877982119)
                      ·
                        rfl

theorem cell23_4094527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_4094527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094527 prefixEnd_4094527 := by exact prefixLift 4094527
  have htrace : WordTrace (prefixWord ++ tailWord_4094527) baseStart_4094527 baseEnd_4094527 := by
    simpa [prefixWord, tailWord_4094527, baseEnd_4094527] using wordTrace_append hprefix tailTrace_4094527
  have hstable : (prefixWord ++ tailWord_4094527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094527).length < 2 ^ (prefixWord ++ tailWord_4094527).sum := by decide
  have hdescent : baseEnd_4094527 < baseStart_4094527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094532 : List Nat := [2, 3, 5, 1, 1, 1, 3, 2, 1, 4]
def baseStart_4094532 : Nat := 118140960795 + 4094532 * 2 ^ 59
def prefixEnd_4094532 : Nat := 4983230072969 + 3 ^ 40 * 4094532 * 2
def baseEnd_4094532 : Nat := 700820990405093119473199

theorem tailTrace_4094532 : CollatzResearch.WordTrace tailWord_4094532 prefixEnd_4094532 700820990405093119473199 := by
  unfold tailWord_4094532
  simp only [CollatzResearch.WordTrace]
  refine ⟨74669925401108664618678925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99559900534811552824905233 74669925401108664618678925)
  ·
    refine ⟨28001222025415749232004597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74669925401108664618678925 28001222025415749232004597)
    ·
      refine ⟨2625114564882726490500431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28001222025415749232004597 2625114564882726490500431)
      ·
        refine ⟨3937671847324089735750647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2625114564882726490500431 3937671847324089735750647)
        ·
          refine ⟨5906507770986134603625971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3937671847324089735750647 5906507770986134603625971)
          ·
            refine ⟨8859761656479201905438957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5906507770986134603625971 8859761656479201905438957)
            ·
              refine ⟨3322410621179700714539609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8859761656479201905438957 3322410621179700714539609)
              ·
                refine ⟨2491807965884775535904707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3322410621179700714539609 2491807965884775535904707)
                ·
                  refine ⟨3737711948827163303857061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491807965884775535904707 3737711948827163303857061)
                  ·
                    refine ⟨700820990405093119473199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3737711948827163303857061 700820990405093119473199)
                    ·
                      rfl

theorem cell23_4094532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_4094532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094532 prefixEnd_4094532 := by exact prefixLift 4094532
  have htrace : WordTrace (prefixWord ++ tailWord_4094532) baseStart_4094532 baseEnd_4094532 := by
    simpa [prefixWord, tailWord_4094532, baseEnd_4094532] using wordTrace_append hprefix tailTrace_4094532
  have hstable : (prefixWord ++ tailWord_4094532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094532).length < 2 ^ (prefixWord ++ tailWord_4094532).sum := by decide
  have hdescent : baseEnd_4094532 < baseStart_4094532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094538 : List Nat := [3, 1, 2, 1, 1, 5, 3, 2, 1, 1, 3]
def baseStart_4094538 : Nat := 118140960795 + 4094538 * 2 ^ 59
def prefixEnd_4094538 : Nat := 4983230072969 + 3 ^ 40 * 4094538 * 2
def baseEnd_4094538 : Nat := 2102466052099206334944569

theorem tailTrace_4094538 : CollatzResearch.WordTrace tailWord_4094538 prefixEnd_4094538 2102466052099206334944569 := by
  unfold tailWord_4094538
  simp only [CollatzResearch.WordTrace]
  refine ⟨37335017410048898065519067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99560046426797061508050845 37335017410048898065519067)
  ·
    refine ⟨56002526115073347098278601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37335017410048898065519067 56002526115073347098278601)
    ·
      refine ⟨42001894586305010323708951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56002526115073347098278601 42001894586305010323708951)
      ·
        refine ⟨63002841879457515485563427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42001894586305010323708951 63002841879457515485563427)
        ·
          refine ⟨94504262819186273228345141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63002841879457515485563427 94504262819186273228345141)
          ·
            refine ⟨8859774639298713115157357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94504262819186273228345141 8859774639298713115157357)
            ·
              refine ⟨3322415489737017418184009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8859774639298713115157357 3322415489737017418184009)
              ·
                refine ⟨2491811617302763063638007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3322415489737017418184009 2491811617302763063638007)
                ·
                  refine ⟨3737717425954144595457011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491811617302763063638007 3737717425954144595457011)
                  ·
                    refine ⟨5606576138931216893185517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3737717425954144595457011 5606576138931216893185517)
                    ·
                      refine ⟨2102466052099206334944569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5606576138931216893185517 2102466052099206334944569)
                      ·
                        rfl

theorem cell23_4094538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_4094538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094538 prefixEnd_4094538 := by exact prefixLift 4094538
  have htrace : WordTrace (prefixWord ++ tailWord_4094538) baseStart_4094538 baseEnd_4094538 := by
    simpa [prefixWord, tailWord_4094538, baseEnd_4094538] using wordTrace_append hprefix tailTrace_4094538
  have hstable : (prefixWord ++ tailWord_4094538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094538).length < 2 ^ (prefixWord ++ tailWord_4094538).sum := by decide
  have hdescent : baseEnd_4094538 < baseStart_4094538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094540 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 3, 1, 6]
def baseStart_4094540 : Nat := 118140960795 + 4094540 * 2 ^ 59
def prefixEnd_4094540 : Nat := 4983230072969 + 3 ^ 40 * 4094540 * 2
def baseEnd_4094540 : Nat := 2102467079060515327119559

theorem tailTrace_4094540 : CollatzResearch.WordTrace tailWord_4094540 prefixEnd_4094540 2102467079060515327119559 := by
  unfold tailWord_4094540
  simp only [CollatzResearch.WordTrace]
  refine ⟨74670071293094173301824537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99560095057458897735766049 74670071293094173301824537)
  ·
    refine ⟨56002553469820629976368403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74670071293094173301824537 56002553469820629976368403)
    ·
      refine ⟨84003830204730944964552605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56002553469820629976368403 84003830204730944964552605)
      ·
        refine ⟨31501436326774104361707227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84003830204730944964552605 31501436326774104361707227)
        ·
          refine ⟨47252154490161156542560841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31501436326774104361707227 47252154490161156542560841)
          ·
            refine ⟨35439115867620867406920631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47252154490161156542560841 35439115867620867406920631)
            ·
              refine ⟨53158673801431301110380947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35439115867620867406920631 53158673801431301110380947)
              ·
                refine ⟨79738010702146951665571421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53158673801431301110380947 79738010702146951665571421)
                ·
                  refine ⟨29901754013305106874589283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79738010702146951665571421 29901754013305106874589283)
                  ·
                    refine ⟨44852631019957660311883925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29901754013305106874589283 44852631019957660311883925)
                    ·
                      refine ⟨2102467079060515327119559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44852631019957660311883925 2102467079060515327119559)
                      ·
                        rfl

theorem cell23_4094540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_4094540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094540 prefixEnd_4094540 := by exact prefixLift 4094540
  have htrace : WordTrace (prefixWord ++ tailWord_4094540) baseStart_4094540 baseEnd_4094540 := by
    simpa [prefixWord, tailWord_4094540, baseEnd_4094540] using wordTrace_append hprefix tailTrace_4094540
  have hstable : (prefixWord ++ tailWord_4094540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094540).length < 2 ^ (prefixWord ++ tailWord_4094540).sum := by decide
  have hdescent : baseEnd_4094540 < baseStart_4094540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094544 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 3, 2, 2]
def baseStart_4094544 : Nat := 118140960795 + 4094544 * 2 ^ 59
def prefixEnd_4094544 : Nat := 4983230072969 + 3 ^ 40 * 4094544 * 2
def baseEnd_4094544 : Nat := 2102469132983133311469541

theorem tailTrace_4094544 : CollatzResearch.WordTrace tailWord_4094544 prefixEnd_4094544 2102469132983133311469541 := by
  unfold tailWord_4094544
  simp only [CollatzResearch.WordTrace]
  refine ⟨74670144239086927643397343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99560192318782570191196457 74670144239086927643397343)
  ·
    refine ⟨112005216358630391465096015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74670144239086927643397343 112005216358630391465096015)
    ·
      refine ⟨168007824537945587197644023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112005216358630391465096015 168007824537945587197644023)
      ·
        refine ⟨252011736806918380796466035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168007824537945587197644023 252011736806918380796466035)
        ·
          refine ⟨378017605210377571194699053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252011736806918380796466035 378017605210377571194699053)
          ·
            refine ⟨141756601953891589198012145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378017605210377571194699053 141756601953891589198012145)
            ·
              refine ⟨106317451465418691898509109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141756601953891589198012145 106317451465418691898509109)
              ·
                refine ⟨9967261074883002365485229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106317451465418691898509109 9967261074883002365485229)
                ·
                  refine ⟨3737722903081125887056961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9967261074883002365485229 3737722903081125887056961)
                  ·
                    refine ⟨2803292177310844415292721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3737722903081125887056961 2803292177310844415292721)
                    ·
                      refine ⟨2102469132983133311469541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2803292177310844415292721 2102469132983133311469541)
                      ·
                        rfl

theorem cell23_4094544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 3, 2, 2].length) (baseStart_4094544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094544 prefixEnd_4094544 := by exact prefixLift 4094544
  have htrace : WordTrace (prefixWord ++ tailWord_4094544) baseStart_4094544 baseEnd_4094544 := by
    simpa [prefixWord, tailWord_4094544, baseEnd_4094544] using wordTrace_append hprefix tailTrace_4094544
  have hstable : (prefixWord ++ tailWord_4094544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094544).length < 2 ^ (prefixWord ++ tailWord_4094544).sum := by decide
  have hdescent : baseEnd_4094544 < baseStart_4094544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094558 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_4094558 : Nat := 118140960795 + 4094558 * 2 ^ 59
def prefixEnd_4094558 : Nat := 4983230072969 + 3 ^ 40 * 4094558 * 2
def baseEnd_4094558 : Nat := 700825440570765418898159

theorem tailTrace_4094558 : CollatzResearch.WordTrace tailWord_4094558 prefixEnd_4094558 700825440570765418898159 := by
  unfold tailWord_4094558
  simp only [CollatzResearch.WordTrace]
  refine ⟨18667599887515391959725541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99560532733415423785202885 18667599887515391959725541)
  ·
    refine ⟨3500174978909135992448539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18667599887515391959725541 3500174978909135992448539)
    ·
      refine ⟨5250262468363703988672809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3500174978909135992448539 5250262468363703988672809)
      ·
        refine ⟨3937696851272777991504607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5250262468363703988672809 3937696851272777991504607)
        ·
          refine ⟨5906545276909166987256911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3937696851272777991504607 5906545276909166987256911)
          ·
            refine ⟨8859817915363750480885367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5906545276909166987256911 8859817915363750480885367)
            ·
              refine ⟨13289726873045625721328051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8859817915363750480885367 13289726873045625721328051)
              ·
                refine ⟨19934590309568438581992077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13289726873045625721328051 19934590309568438581992077)
                ·
                  refine ⟨7475471366088164468247029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19934590309568438581992077 7475471366088164468247029)
                  ·
                    refine ⟨700825440570765418898159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7475471366088164468247029 700825440570765418898159)
                    ·
                      rfl

theorem cell23_4094558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_4094558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094558 prefixEnd_4094558 := by exact prefixLift 4094558
  have htrace : WordTrace (prefixWord ++ tailWord_4094558) baseStart_4094558 baseEnd_4094558 := by
    simpa [prefixWord, tailWord_4094558, baseEnd_4094558] using wordTrace_append hprefix tailTrace_4094558
  have hstable : (prefixWord ++ tailWord_4094558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094558).length < 2 ^ (prefixWord ++ tailWord_4094558).sum := by decide
  have hdescent : baseEnd_4094558 < baseStart_4094558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094574 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_4094574 : Nat := 118140960795 + 4094574 * 2 ^ 59
def prefixEnd_4094574 : Nat := 4983230072969 + 3 ^ 40 * 4094574 * 2
def baseEnd_4094574 : Nat := 2102484537402768194094403

theorem tailTrace_4094574 : CollatzResearch.WordTrace tailWord_4094574 prefixEnd_4094574 2102484537402768194094403 := by
  unfold tailWord_4094574
  simp only [CollatzResearch.WordTrace]
  refine ⟨18667672833508146301298347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99560921778710113606924517 18667672833508146301298347)
  ·
    refine ⟨28001509250262219451947521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18667672833508146301298347 28001509250262219451947521)
    ·
      refine ⟨21001131937696664588960641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28001509250262219451947521 21001131937696664588960641)
      ·
        refine ⟨15750848953272498441720481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21001131937696664588960641 15750848953272498441720481)
        ·
          refine ⟨11813136714954373831290361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15750848953272498441720481 11813136714954373831290361)
          ·
            refine ⟨8859852536215780373467771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11813136714954373831290361 8859852536215780373467771)
            ·
              refine ⟨13289778804323670560201657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8859852536215780373467771 13289778804323670560201657)
              ·
                refine ⟨9967334103242752920151243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13289778804323670560201657 9967334103242752920151243)
                ·
                  refine ⟨14951001154864129380226865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9967334103242752920151243 14951001154864129380226865)
                  ·
                    refine ⟨11213250866148097035170149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14951001154864129380226865 11213250866148097035170149)
                    ·
                      refine ⟨2102484537402768194094403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11213250866148097035170149 2102484537402768194094403)
                      ·
                        rfl

theorem cell23_4094574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_4094574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094574 prefixEnd_4094574 := by exact prefixLift 4094574
  have htrace : WordTrace (prefixWord ++ tailWord_4094574) baseStart_4094574 baseEnd_4094574 := by
    simpa [prefixWord, tailWord_4094574, baseEnd_4094574] using wordTrace_append hprefix tailTrace_4094574
  have hstable : (prefixWord ++ tailWord_4094574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094574).length < 2 ^ (prefixWord ++ tailWord_4094574).sum := by decide
  have hdescent : baseEnd_4094574 < baseStart_4094574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094581 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_4094581 : Nat := 118140960795 + 4094581 * 2 ^ 59
def prefixEnd_4094581 : Nat := 4983230072969 + 3 ^ 40 * 4094581 * 2
def baseEnd_4094581 : Nat := 2102488131767349666706871

theorem tailTrace_4094581 : CollatzResearch.WordTrace tailWord_4094581 prefixEnd_4094581 2102488131767349666706871 := by
  unfold tailWord_4094581
  simp only [CollatzResearch.WordTrace]
  refine ⟨149341637979039810605891597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99561091986026540403927731 149341637979039810605891597)
  ·
    refine ⟨56003114242139928977209349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149341637979039810605891597 56003114242139928977209349)
    ·
      refine ⟨10500583920401236683226753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56003114242139928977209349 10500583920401236683226753)
      ·
        refine ⟨7875437940300927512420065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10500583920401236683226753 7875437940300927512420065)
        ·
          refine ⟨5906578455225695634315049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7875437940300927512420065 5906578455225695634315049)
          ·
            refine ⟨4429933841419271725736287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5906578455225695634315049 4429933841419271725736287)
            ·
              refine ⟨6644900762128907588604431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4429933841419271725736287 6644900762128907588604431)
              ·
                refine ⟨9967351143193361382906647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6644900762128907588604431 9967351143193361382906647)
                ·
                  refine ⟨14951026714790042074359971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9967351143193361382906647 14951026714790042074359971)
                  ·
                    refine ⟨22426540072185063111539957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14951026714790042074359971 22426540072185063111539957)
                    ·
                      refine ⟨2102488131767349666706871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22426540072185063111539957 2102488131767349666706871)
                      ·
                        rfl

theorem cell23_4094581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_4094581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094581 prefixEnd_4094581 := by exact prefixLift 4094581
  have htrace : WordTrace (prefixWord ++ tailWord_4094581) baseStart_4094581 baseEnd_4094581 := by
    simpa [prefixWord, tailWord_4094581, baseEnd_4094581] using wordTrace_append hprefix tailTrace_4094581
  have hstable : (prefixWord ++ tailWord_4094581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094581).length < 2 ^ (prefixWord ++ tailWord_4094581).sum := by decide
  have hdescent : baseEnd_4094581 < baseStart_4094581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094640 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 11]
def baseStart_4094640 : Nat := 118140960795 + 4094640 * 2 ^ 59
def prefixEnd_4094640 : Nat := 4983230072969 + 3 ^ 40 * 4094640 * 2
def baseEnd_4094640 : Nat := 233613158569551659541011

theorem tailTrace_4094640 : CollatzResearch.WordTrace tailWord_4094640 prefixEnd_4094640 233613158569551659541011 := by
  unfold tailWord_4094640
  simp only [CollatzResearch.WordTrace]
  refine ⟨74671894942913031841144687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99562526590550709121526249 74671894942913031841144687)
  ·
    refine ⟨112007842414369547761717031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74671894942913031841144687 112007842414369547761717031)
    ·
      refine ⟨168011763621554321642575547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112007842414369547761717031 168011763621554321642575547)
      ·
        refine ⟨252017645432331482463863321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168011763621554321642575547 252017645432331482463863321)
        ·
          refine ⟨189013234074248611847897491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252017645432331482463863321 189013234074248611847897491)
          ·
            refine ⟨283519851111372917771846237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189013234074248611847897491 283519851111372917771846237)
            ·
              refine ⟨106319944166764844164442339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283519851111372917771846237 106319944166764844164442339)
              ·
                refine ⟨159479916250147266246663509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106319944166764844164442339 159479916250147266246663509)
                ·
                  refine ⟨233613158569551659541011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 159479916250147266246663509 233613158569551659541011)
                  ·
                    rfl

theorem cell23_4094640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 11].length) (baseStart_4094640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094640 prefixEnd_4094640 := by exact prefixLift 4094640
  have htrace : WordTrace (prefixWord ++ tailWord_4094640) baseStart_4094640 baseEnd_4094640 := by
    simpa [prefixWord, tailWord_4094640, baseEnd_4094640] using wordTrace_append hprefix tailTrace_4094640
  have hstable : (prefixWord ++ tailWord_4094640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094640).length < 2 ^ (prefixWord ++ tailWord_4094640).sum := by decide
  have hdescent : baseEnd_4094640 < baseStart_4094640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094662 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_4094662 : Nat := 118140960795 + 4094662 * 2 ^ 59
def prefixEnd_4094662 : Nat := 4983230072969 + 3 ^ 40 * 4094662 * 2
def baseEnd_4094662 : Nat := 2102529723700363849793999

theorem tailTrace_4094662 : CollatzResearch.WordTrace tailWord_4094662 prefixEnd_4094662 2102529723700363849793999 := by
  unfold tailWord_4094662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4667018509117073794987195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99563061527830907626393493 4667018509117073794987195)
  ·
    refine ⟨7000527763675610692480793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4667018509117073794987195 7000527763675610692480793)
    ·
      refine ⟨5250395822756708019360595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7000527763675610692480793 5250395822756708019360595)
      ·
        refine ⟨7875593734135062029040893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5250395822756708019360595 7875593734135062029040893)
        ·
          refine ⟨2953347650300648260890335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7875593734135062029040893 2953347650300648260890335)
          ·
            refine ⟨4430021475450972391335503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2953347650300648260890335 4430021475450972391335503)
            ·
              refine ⟨6645032213176458587003255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4430021475450972391335503 6645032213176458587003255)
              ·
                refine ⟨9967548319764687880504883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6645032213176458587003255 9967548319764687880504883)
                ·
                  refine ⟨14951322479647031820757325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9967548319764687880504883 14951322479647031820757325)
                  ·
                    refine ⟨5606745929867636932783997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14951322479647031820757325 5606745929867636932783997)
                    ·
                      refine ⟨2102529723700363849793999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5606745929867636932783997 2102529723700363849793999)
                      ·
                        rfl

theorem cell23_4094662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_4094662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094662 prefixEnd_4094662 := by exact prefixLift 4094662
  have htrace : WordTrace (prefixWord ++ tailWord_4094662) baseStart_4094662 baseEnd_4094662 := by
    simpa [prefixWord, tailWord_4094662, baseEnd_4094662] using wordTrace_append hprefix tailTrace_4094662
  have hstable : (prefixWord ++ tailWord_4094662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094662).length < 2 ^ (prefixWord ++ tailWord_4094662).sum := by decide
  have hdescent : baseEnd_4094662 < baseStart_4094662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094668 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 1, 4, 2]
def baseStart_4094668 : Nat := 118140960795 + 4094668 * 2 ^ 59
def prefixEnd_4094668 : Nat := 4983230072969 + 3 ^ 40 * 4094668 * 2
def baseEnd_4094668 : Nat := 2102532804584290826318971

theorem tailTrace_4094668 : CollatzResearch.WordTrace tailWord_4094668 prefixEnd_4094668 2102532804584290826318971 := by
  unfold tailWord_4094668
  simp only [CollatzResearch.WordTrace]
  refine ⟨74672405564862312232154329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99563207419816416309539105 74672405564862312232154329)
  ·
    refine ⟨56004304173646734174115747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74672405564862312232154329 56004304173646734174115747)
    ·
      refine ⟨84006456260470101261173621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56004304173646734174115747 84006456260470101261173621)
      ·
        refine ⟨7875605274419071993235027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84006456260470101261173621 7875605274419071993235027)
        ·
          refine ⟨11813407911628607989852541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7875605274419071993235027 11813407911628607989852541)
          ·
            refine ⟨4430027966860727996194703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11813407911628607989852541 4430027966860727996194703)
            ·
              refine ⟨6645041950291091994292055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4430027966860727996194703 6645041950291091994292055)
              ·
                refine ⟨9967562925436637991438083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6645041950291091994292055 9967562925436637991438083)
                ·
                  refine ⟨14951344388154956987157125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9967562925436637991438083 14951344388154956987157125)
                  ·
                    refine ⟨2803377072779054435091961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14951344388154956987157125 2803377072779054435091961)
                    ·
                      refine ⟨2102532804584290826318971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2803377072779054435091961 2102532804584290826318971)
                      ·
                        rfl

theorem cell23_4094668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_4094668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094668 prefixEnd_4094668 := by exact prefixLift 4094668
  have htrace : WordTrace (prefixWord ++ tailWord_4094668) baseStart_4094668 baseEnd_4094668 := by
    simpa [prefixWord, tailWord_4094668, baseEnd_4094668] using wordTrace_append hprefix tailTrace_4094668
  have hstable : (prefixWord ++ tailWord_4094668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094668).length < 2 ^ (prefixWord ++ tailWord_4094668).sum := by decide
  have hdescent : baseEnd_4094668 < baseStart_4094668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094687 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 1, 7]
def baseStart_4094687 : Nat := 118140960795 + 4094687 * 2 ^ 59
def prefixEnd_4094687 : Nat := 4983230072969 + 3 ^ 40 * 4094687 * 2
def baseEnd_4094687 : Nat := 700847520238908750660461

theorem tailTrace_4094687 : CollatzResearch.WordTrace tailWord_4094687 prefixEnd_4094687 700847520238908750660461 := by
  unfold tailWord_4094687
  simp only [CollatzResearch.WordTrace]
  refine ⟨149345504116655790709250315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99563669411103860472833543 149345504116655790709250315)
  ·
    refine ⟨224018256174983686063875473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149345504116655790709250315 224018256174983686063875473)
    ·
      refine ⟨168013692131237764547906605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224018256174983686063875473 168013692131237764547906605)
      ·
        refine ⟨63005134549214161705464977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168013692131237764547906605 63005134549214161705464977)
        ·
          refine ⟨47253850911910621279098733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63005134549214161705464977 47253850911910621279098733)
          ·
            refine ⟨17720194091966482979662025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47253850911910621279098733 17720194091966482979662025)
            ·
              refine ⟨13290145568974862234746519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17720194091966482979662025 13290145568974862234746519)
              ·
                refine ⟨19935218353462293352119779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13290145568974862234746519 19935218353462293352119779)
                ·
                  refine ⟨29902827530193440028179669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19935218353462293352119779 29902827530193440028179669)
                  ·
                    refine ⟨700847520238908750660461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29902827530193440028179669 700847520238908750660461)
                    ·
                      rfl

theorem cell23_4094687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 7].length) (baseStart_4094687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094687 prefixEnd_4094687 := by exact prefixLift 4094687
  have htrace : WordTrace (prefixWord ++ tailWord_4094687) baseStart_4094687 baseEnd_4094687 := by
    simpa [prefixWord, tailWord_4094687, baseEnd_4094687] using wordTrace_append hprefix tailTrace_4094687
  have hstable : (prefixWord ++ tailWord_4094687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094687).length < 2 ^ (prefixWord ++ tailWord_4094687).sum := by decide
  have hdescent : baseEnd_4094687 < baseStart_4094687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094691 : List Nat := [1, 1, 1, 7, 1, 1, 3, 3, 5]
def baseStart_4094691 : Nat := 118140960795 + 4094691 * 2 ^ 59
def prefixEnd_4094691 : Nat := 4983230072969 + 3 ^ 40 * 4094691 * 2
def baseEnd_4094691 : Nat := 233616068293260470703485

theorem tailTrace_4094691 : CollatzResearch.WordTrace tailWord_4094691 prefixEnd_4094691 233616068293260470703485 := by
  unfold tailWord_4094691
  simp only [CollatzResearch.WordTrace]
  refine ⟨149345650008641299392395927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99563766672427532928263951 149345650008641299392395927)
  ·
    refine ⟨224018475012961949088593891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149345650008641299392395927 224018475012961949088593891)
    ·
      refine ⟨336027712519442923632890837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224018475012961949088593891 336027712519442923632890837)
      ·
        refine ⟨7875649512174443522645879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 336027712519442923632890837 7875649512174443522645879)
        ·
          refine ⟨11813474268261665283968819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7875649512174443522645879 11813474268261665283968819)
          ·
            refine ⟨17720211402392497925953229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11813474268261665283968819 17720211402392497925953229)
            ·
              refine ⟨6645079275897186722232461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17720211402392497925953229 6645079275897186722232461)
              ·
                refine ⟨2491904728461445020837173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6645079275897186722232461 2491904728461445020837173)
                ·
                  refine ⟨233616068293260470703485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2491904728461445020837173 233616068293260470703485)
                  ·
                    rfl

theorem cell23_4094691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 5].length) (baseStart_4094691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094691 prefixEnd_4094691 := by exact prefixLift 4094691
  have htrace : WordTrace (prefixWord ++ tailWord_4094691) baseStart_4094691 baseEnd_4094691 := by
    simpa [prefixWord, tailWord_4094691, baseEnd_4094691] using wordTrace_append hprefix tailTrace_4094691
  have hstable : (prefixWord ++ tailWord_4094691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094691).length < 2 ^ (prefixWord ++ tailWord_4094691).sum := by decide
  have hdescent : baseEnd_4094691 < baseStart_4094691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094724 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_4094724 : Nat := 118140960795 + 4094724 * 2 ^ 59
def prefixEnd_4094724 : Nat := 4983230072969 + 3 ^ 40 * 4094724 * 2
def baseEnd_4094724 : Nat := 2102561559500942607218713

theorem tailTrace_4094724 : CollatzResearch.WordTrace tailWord_4094724 prefixEnd_4094724 2102561559500942607218713 := by
  unfold tailWord_4094724
  simp only [CollatzResearch.WordTrace]
  refine ⟨74673426808760873014173613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99564569078347830685564817 74673426808760873014173613)
  ·
    refine ⟨28002535053285327380315105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74673426808760873014173613 28002535053285327380315105)
    ·
      refine ⟨21001901289963995535236329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28002535053285327380315105 21001901289963995535236329)
      ·
        refine ⟨15751425967472996651427247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21001901289963995535236329 15751425967472996651427247)
        ·
          refine ⟨23627138951209494977140871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15751425967472996651427247 23627138951209494977140871)
          ·
            refine ⟨35440708426814242465711307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23627138951209494977140871 35440708426814242465711307)
            ·
              refine ⟨53161062640221363698566961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35440708426814242465711307 53161062640221363698566961)
              ·
                refine ⟨39870796980166022773925221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53161062640221363698566961 39870796980166022773925221)
                ·
                  refine ⟨7475774433781129270110979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39870796980166022773925221 7475774433781129270110979)
                  ·
                    refine ⟨11213661650671693905166469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7475774433781129270110979 11213661650671693905166469)
                    ·
                      refine ⟨2102561559500942607218713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11213661650671693905166469 2102561559500942607218713)
                      ·
                        rfl

theorem cell23_4094724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_4094724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094724 prefixEnd_4094724 := by exact prefixLift 4094724
  have htrace : WordTrace (prefixWord ++ tailWord_4094724) baseStart_4094724 baseEnd_4094724 := by
    simpa [prefixWord, tailWord_4094724, baseEnd_4094724] using wordTrace_append hprefix tailTrace_4094724
  have hstable : (prefixWord ++ tailWord_4094724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094724).length < 2 ^ (prefixWord ++ tailWord_4094724).sum := by decide
  have hdescent : baseEnd_4094724 < baseStart_4094724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094734 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 5, 4]
def baseStart_4094734 : Nat := 118140960795 + 4094734 * 2 ^ 59
def prefixEnd_4094734 : Nat := 4983230072969 + 3 ^ 40 * 4094734 * 2
def baseEnd_4094734 : Nat := 700855564769162522697889

theorem tailTrace_4094734 : CollatzResearch.WordTrace tailWord_4094734 prefixEnd_4094734 700855564769162522697889 := by
  unfold tailWord_4094734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18668402293435689717026407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99564812231657011824140837 18668402293435689717026407)
  ·
    refine ⟨28002603440153534575539611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18668402293435689717026407 28002603440153534575539611)
    ·
      refine ⟨42003905160230301863309417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28002603440153534575539611 42003905160230301863309417)
      ·
        refine ⟨31502928870172726397482063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42003905160230301863309417 31502928870172726397482063)
        ·
          refine ⟨47254393305259089596223095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31502928870172726397482063 47254393305259089596223095)
          ·
            refine ⟨70881589957888634394334643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47254393305259089596223095 70881589957888634394334643)
            ·
              refine ⟨106322384936832951591501965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70881589957888634394334643 106322384936832951591501965)
              ·
                refine ⟨39870894351312356846813237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106322384936832951591501965 39870894351312356846813237)
                ·
                  refine ⟨3737896345435533454388741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39870894351312356846813237 3737896345435533454388741)
                  ·
                    refine ⟨700855564769162522697889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3737896345435533454388741 700855564769162522697889)
                    ·
                      rfl

theorem cell23_4094734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_4094734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094734 prefixEnd_4094734 := by exact prefixLift 4094734
  have htrace : WordTrace (prefixWord ++ tailWord_4094734) baseStart_4094734 baseEnd_4094734 := by
    simpa [prefixWord, tailWord_4094734, baseEnd_4094734] using wordTrace_append hprefix tailTrace_4094734
  have hstable : (prefixWord ++ tailWord_4094734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094734).length < 2 ^ (prefixWord ++ tailWord_4094734).sum := by decide
  have hdescent : baseEnd_4094734 < baseStart_4094734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094737 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 4]
def baseStart_4094737 : Nat := 118140960795 + 4094737 * 2 ^ 59
def prefixEnd_4094737 : Nat := 4983230072969 + 3 ^ 40 * 4094737 * 2
def baseEnd_4094737 : Nat := 2102568234749451056356153

theorem tailTrace_4094737 : CollatzResearch.WordTrace tailWord_4094737 prefixEnd_4094737 2102568234749451056356153 := by
  unfold tailWord_4094737
  simp only [CollatzResearch.WordTrace]
  refine ⟨149347327766474649248570465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99564885177649766165713643 149347327766474649248570465)
  ·
    refine ⟨112010495824855986936427849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149347327766474649248570465 112010495824855986936427849)
    ·
      refine ⟨84007871868641990202320887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112010495824855986936427849 84007871868641990202320887)
      ·
        refine ⟨126011807802962985303481331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84007871868641990202320887 126011807802962985303481331)
        ·
          refine ⟨189017711704444477955221997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126011807802962985303481331 189017711704444477955221997)
          ·
            refine ⟨70881641889166679233208249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189017711704444477955221997 70881641889166679233208249)
            ·
              refine ⟨53161231416875009424906187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70881641889166679233208249 53161231416875009424906187)
              ·
                refine ⟨79741847125312514137359281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53161231416875009424906187 79741847125312514137359281)
                ·
                  refine ⟨59806385343984385603019461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79741847125312514137359281 59806385343984385603019461)
                  ·
                    refine ⟨11213697251997072300566149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59806385343984385603019461 11213697251997072300566149)
                    ·
                      refine ⟨2102568234749451056356153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11213697251997072300566149 2102568234749451056356153)
                      ·
                        rfl

theorem cell23_4094737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_4094737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094737 prefixEnd_4094737 := by exact prefixLift 4094737
  have htrace : WordTrace (prefixWord ++ tailWord_4094737) baseStart_4094737 baseEnd_4094737 := by
    simpa [prefixWord, tailWord_4094737, baseEnd_4094737] using wordTrace_append hprefix tailTrace_4094737
  have hstable : (prefixWord ++ tailWord_4094737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094737).length < 2 ^ (prefixWord ++ tailWord_4094737).sum := by decide
  have hdescent : baseEnd_4094737 < baseStart_4094737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094738 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 2, 5]
def baseStart_4094738 : Nat := 118140960795 + 4094738 * 2 ^ 59
def prefixEnd_4094738 : Nat := 4983230072969 + 3 ^ 40 * 4094738 * 2
def baseEnd_4094738 : Nat := 700856249410035184147883

theorem tailTrace_4094738 : CollatzResearch.WordTrace tailWord_4094738 prefixEnd_4094738 700856249410035184147883 := by
  unfold tailWord_4094738
  simp only [CollatzResearch.WordTrace]
  refine ⟨37336841059867756604839217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99564909492980684279571245 37336841059867756604839217)
  ·
    refine ⟨28002630794900817453629413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37336841059867756604839217 28002630794900817453629413)
    ·
      refine ⟨5250493274043903272555515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28002630794900817453629413 5250493274043903272555515)
      ·
        refine ⟨7875739911065854908833273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5250493274043903272555515 7875739911065854908833273)
        ·
          refine ⟨5906804933299391181624955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7875739911065854908833273 5906804933299391181624955)
          ·
            refine ⟨8860207399949086772437433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5906804933299391181624955 8860207399949086772437433)
            ·
              refine ⟨6645155549961815079328075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8860207399949086772437433 6645155549961815079328075)
              ·
                refine ⟨9967733324942722618992113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6645155549961815079328075 9967733324942722618992113)
                ·
                  refine ⟨7475799993707041964244085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9967733324942722618992113 7475799993707041964244085)
                  ·
                    refine ⟨700856249410035184147883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7475799993707041964244085 700856249410035184147883)
                    ·
                      rfl

theorem cell23_4094738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_4094738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094738 prefixEnd_4094738 := by exact prefixLift 4094738
  have htrace : WordTrace (prefixWord ++ tailWord_4094738) baseStart_4094738 baseEnd_4094738 := by
    simpa [prefixWord, tailWord_4094738, baseEnd_4094738] using wordTrace_append hprefix tailTrace_4094738
  have hstable : (prefixWord ++ tailWord_4094738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094738).length < 2 ^ (prefixWord ++ tailWord_4094738).sum := by decide
  have hdescent : baseEnd_4094738 < baseStart_4094738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094764 : List Nat := [2, 2, 1, 1, 1, 4, 4, 2, 6]
def baseStart_4094764 : Nat := 118140960795 + 4094764 * 2 ^ 59
def prefixEnd_4094764 : Nat := 4983230072969 + 3 ^ 40 * 4094764 * 2
def baseEnd_4094764 : Nat := 233620233191902494524281

theorem tailTrace_4094764 : CollatzResearch.WordTrace tailWord_4094764 prefixEnd_4094764 233620233191902494524281 := by
  unfold tailWord_4094764
  simp only [CollatzResearch.WordTrace]
  refine ⟨74674156268688416429901673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99565541691584555239868897 74674156268688416429901673)
  ·
    refine ⟨56005617201516312322426255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74674156268688416429901673 56005617201516312322426255)
    ·
      refine ⟨84008425802274468483639383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56005617201516312322426255 84008425802274468483639383)
      ·
        refine ⟨126012638703411702725459075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84008425802274468483639383 126012638703411702725459075)
        ·
          refine ⟨189018958055117554088188613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126012638703411702725459075 189018958055117554088188613)
          ·
            refine ⟨35441054635334541391535365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189018958055117554088188613 35441054635334541391535365)
            ·
              refine ⟨6645197744125226510912881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35441054635334541391535365 6645197744125226510912881)
              ·
                refine ⟨4983898308093919883184661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6645197744125226510912881 4983898308093919883184661)
                ·
                  refine ⟨233620233191902494524281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4983898308093919883184661 233620233191902494524281)
                  ·
                    rfl

theorem cell23_4094764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 6].length) (baseStart_4094764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094764 prefixEnd_4094764 := by exact prefixLift 4094764
  have htrace : WordTrace (prefixWord ++ tailWord_4094764) baseStart_4094764 baseEnd_4094764 := by
    simpa [prefixWord, tailWord_4094764, baseEnd_4094764] using wordTrace_append hprefix tailTrace_4094764
  have hstable : (prefixWord ++ tailWord_4094764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094764).length < 2 ^ (prefixWord ++ tailWord_4094764).sum := by decide
  have hdescent : baseEnd_4094764 < baseStart_4094764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094787 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 7]
def baseStart_4094787 : Nat := 118140960795 + 4094787 * 2 ^ 59
def prefixEnd_4094787 : Nat := 4983230072969 + 3 ^ 40 * 4094787 * 2
def baseEnd_4094787 : Nat := 2102593908782175860730923

theorem tailTrace_4094787 : CollatzResearch.WordTrace tailWord_4094787 prefixEnd_4094787 2102593908782175860730923 := by
  unfold tailWord_4094787
  simp only [CollatzResearch.WordTrace]
  refine ⟨149349151416293507787890615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99566100944195671858593743 149349151416293507787890615)
  ·
    refine ⟨224023727124440261681835923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149349151416293507787890615 224023727124440261681835923)
    ·
      refine ⟨336035590686660392522753885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224023727124440261681835923 336035590686660392522753885)
      ·
        refine ⟨126013346507497647196032707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336035590686660392522753885 126013346507497647196032707)
        ·
          refine ⟨189020019761246470794049061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126013346507497647196032707 189020019761246470794049061)
          ·
            refine ⟨35441253705233713273884199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189020019761246470794049061 35441253705233713273884199)
            ·
              refine ⟨53161880557850569910826299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35441253705233713273884199 53161880557850569910826299)
              ·
                refine ⟨79742820836775854866239449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53161880557850569910826299 79742820836775854866239449)
                ·
                  refine ⟨59807115627581891149679587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79742820836775854866239449 59807115627581891149679587)
                  ·
                    refine ⟨89710673441372836724519381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59807115627581891149679587 89710673441372836724519381)
                    ·
                      refine ⟨2102593908782175860730923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89710673441372836724519381 2102593908782175860730923)
                      ·
                        rfl

theorem cell23_4094787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_4094787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094787 prefixEnd_4094787 := by exact prefixLift 4094787
  have htrace : WordTrace (prefixWord ++ tailWord_4094787) baseStart_4094787 baseEnd_4094787 := by
    simpa [prefixWord, tailWord_4094787, baseEnd_4094787] using wordTrace_append hprefix tailTrace_4094787
  have hstable : (prefixWord ++ tailWord_4094787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094787).length < 2 ^ (prefixWord ++ tailWord_4094787).sum := by decide
  have hdescent : baseEnd_4094787 < baseStart_4094787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094834 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_4094834 : Nat := 118140960795 + 4094834 * 2 ^ 59
def prefixEnd_4094834 : Nat := 4983230072969 + 3 ^ 40 * 4094834 * 2
def baseEnd_4094834 : Nat := 2102618042372937176843207

theorem tailTrace_4094834 : CollatzResearch.WordTrace tailWord_4094834 prefixEnd_4094834 2102618042372937176843207 := by
  unfold tailWord_4094834
  simp only [CollatzResearch.WordTrace]
  refine ⟨37337716411780808703712889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99567243764748823209901037 37337716411780808703712889)
  ·
    refine ⟨28003287308835606527784667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37337716411780808703712889 28003287308835606527784667)
    ·
      refine ⟨42004930963253409791677001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28003287308835606527784667 42004930963253409791677001)
      ·
        refine ⟨31503698222440057343757751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42004930963253409791677001 31503698222440057343757751)
        ·
          refine ⟨47255547333660086015636627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31503698222440057343757751 47255547333660086015636627)
          ·
            refine ⟨70883321000490129023454941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47255547333660086015636627 70883321000490129023454941)
            ·
              refine ⟨26581245375183798383795603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70883321000490129023454941 26581245375183798383795603)
              ·
                refine ⟨39871868062775697575693405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26581245375183798383795603 39871868062775697575693405)
                ·
                  refine ⟨14951950523540886590885027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39871868062775697575693405 14951950523540886590885027)
                  ·
                    refine ⟨22427925785311329886327541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14951950523540886590885027 22427925785311329886327541)
                    ·
                      refine ⟨2102618042372937176843207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22427925785311329886327541 2102618042372937176843207)
                      ·
                        rfl

theorem cell23_4094834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_4094834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094834 prefixEnd_4094834 := by exact prefixLift 4094834
  have htrace : WordTrace (prefixWord ++ tailWord_4094834) baseStart_4094834 baseEnd_4094834 := by
    simpa [prefixWord, tailWord_4094834, baseEnd_4094834] using wordTrace_append hprefix tailTrace_4094834
  have hstable : (prefixWord ++ tailWord_4094834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094834).length < 2 ^ (prefixWord ++ tailWord_4094834).sum := by decide
  have hdescent : baseEnd_4094834 < baseStart_4094834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094841 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 1, 6]
def baseStart_4094841 : Nat := 118140960795 + 4094841 * 2 ^ 59
def prefixEnd_4094841 : Nat := 4983230072969 + 3 ^ 40 * 4094841 * 2
def baseEnd_4094841 : Nat := 700873878912506216485225

theorem tailTrace_4094841 : CollatzResearch.WordTrace tailWord_4094841 prefixEnd_4094841 700873878912506216485225 := by
  unfold tailWord_4094841
  simp only [CollatzResearch.WordTrace]
  refine ⟨149351120958097875010356377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99567413972065250006904251 149351120958097875010356377)
  ·
    refine ⟨112013340718573406257767283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149351120958097875010356377 112013340718573406257767283)
    ·
      refine ⟨168020011077860109386650925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112013340718573406257767283 168020011077860109386650925)
      ·
        refine ⟨63007504154197541019994097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168020011077860109386650925 63007504154197541019994097)
        ·
          refine ⟨47255628115648155764995573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63007504154197541019994097 47255628115648155764995573)
          ·
            refine ⟨4430215135842014602968335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47255628115648155764995573 4430215135842014602968335)
            ·
              refine ⟨6645322703763021904452503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4430215135842014602968335 6645322703763021904452503)
              ·
                refine ⟨9967984055644532856678755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6645322703763021904452503 9967984055644532856678755)
                ·
                  refine ⟨14951976083466799285018133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9967984055644532856678755 14951976083466799285018133)
                  ·
                    refine ⟨700873878912506216485225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14951976083466799285018133 700873878912506216485225)
                    ·
                      rfl

theorem cell23_4094841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 6].length) (baseStart_4094841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094841 prefixEnd_4094841 := by exact prefixLift 4094841
  have htrace : WordTrace (prefixWord ++ tailWord_4094841) baseStart_4094841 baseEnd_4094841 := by
    simpa [prefixWord, tailWord_4094841, baseEnd_4094841] using wordTrace_append hprefix tailTrace_4094841
  have hstable : (prefixWord ++ tailWord_4094841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094841).length < 2 ^ (prefixWord ++ tailWord_4094841).sum := by decide
  have hdescent : baseEnd_4094841 < baseStart_4094841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094868 : List Nat := [2, 4, 2, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_4094868 : Nat := 118140960795 + 4094868 * 2 ^ 59
def prefixEnd_4094868 : Nat := 4983230072969 + 3 ^ 40 * 4094868 * 2
def baseEnd_4094868 : Nat := 2102635500715190043818051

theorem tailTrace_4094868 : CollatzResearch.WordTrace tailWord_4094868 prefixEnd_4094868 2102635500715190043818051 := by
  unfold tailWord_4094868
  simp only [CollatzResearch.WordTrace]
  refine ⟨74676052864500029310794629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99568070486000039081059505 74676052864500029310794629)
  ·
    refine ⟨14001759912093755495773993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74676052864500029310794629 14001759912093755495773993)
    ·
      refine ⟨10501319934070316621830495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14001759912093755495773993 10501319934070316621830495)
      ·
        refine ⟨15751979901105474932745743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10501319934070316621830495 15751979901105474932745743)
        ·
          refine ⟨23627969851658212399118615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15751979901105474932745743 23627969851658212399118615)
          ·
            refine ⟨35441954777487318598677923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23627969851658212399118615 35441954777487318598677923)
            ·
              refine ⟨53162932166230977898016885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35441954777487318598677923 53162932166230977898016885)
              ·
                refine ⟨4984024890584154177939083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53162932166230977898016885 4984024890584154177939083)
                ·
                  refine ⟨7476037335876231266908625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4984024890584154177939083 7476037335876231266908625)
                  ·
                    refine ⟨5607028001907173450181469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7476037335876231266908625 5607028001907173450181469)
                    ·
                      refine ⟨2102635500715190043818051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5607028001907173450181469 2102635500715190043818051)
                      ·
                        rfl

theorem cell23_4094868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_4094868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094868 prefixEnd_4094868 := by exact prefixLift 4094868
  have htrace : WordTrace (prefixWord ++ tailWord_4094868) baseStart_4094868 baseEnd_4094868 := by
    simpa [prefixWord, tailWord_4094868, baseEnd_4094868] using wordTrace_append hprefix tailTrace_4094868
  have hstable : (prefixWord ++ tailWord_4094868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094868).length < 2 ^ (prefixWord ++ tailWord_4094868).sum := by decide
  have hdescent : baseEnd_4094868 < baseStart_4094868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094882 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 3, 2, 2]
def baseStart_4094882 : Nat := 118140960795 + 4094882 * 2 ^ 59
def prefixEnd_4094882 : Nat := 4983230072969 + 3 ^ 40 * 4094882 * 2
def baseEnd_4094882 : Nat := 2102642689444352989042987

theorem tailTrace_4094882 : CollatzResearch.WordTrace tailWord_4094882 prefixEnd_4094882 2102642689444352989042987 := by
  unfold tailWord_4094882
  simp only [CollatzResearch.WordTrace]
  refine ⟨37338154087737334753149725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99568410900632892675065933 37338154087737334753149725)
  ·
    refine ⟨14001807782901500532431147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37338154087737334753149725 14001807782901500532431147)
    ·
      refine ⟨21002711674352250798646721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14001807782901500532431147 21002711674352250798646721)
      ·
        refine ⟨15752033755764188098985041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21002711674352250798646721 15752033755764188098985041)
        ·
          refine ⟨11814025316823141074238781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15752033755764188098985041 11814025316823141074238781)
          ·
            refine ⟨4430259493808677902839543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11814025316823141074238781 4430259493808677902839543)
            ·
              refine ⟨6645389240713016854259315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4430259493808677902839543 6645389240713016854259315)
              ·
                refine ⟨9968083861069525281388973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6645389240713016854259315 9968083861069525281388973)
                ·
                  refine ⟨3738031447901071980520865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9968083861069525281388973 3738031447901071980520865)
                  ·
                    refine ⟨2803523585925803985390649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3738031447901071980520865 2803523585925803985390649)
                    ·
                      refine ⟨2102642689444352989042987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2803523585925803985390649 2102642689444352989042987)
                      ·
                        rfl

theorem cell23_4094882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_4094882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094882 prefixEnd_4094882 := by exact prefixLift 4094882
  have htrace : WordTrace (prefixWord ++ tailWord_4094882) baseStart_4094882 baseEnd_4094882 := by
    simpa [prefixWord, tailWord_4094882, baseEnd_4094882] using wordTrace_append hprefix tailTrace_4094882
  have hstable : (prefixWord ++ tailWord_4094882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094882).length < 2 ^ (prefixWord ++ tailWord_4094882).sum := by decide
  have hdescent : baseEnd_4094882 < baseStart_4094882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094884 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 2, 7]
def baseStart_4094884 : Nat := 118140960795 + 4094884 * 2 ^ 59
def prefixEnd_4094884 : Nat := 4983230072969 + 3 ^ 40 * 4094884 * 2
def baseEnd_4094884 : Nat := 700881238801887327072659

theorem tailTrace_4094884 : CollatzResearch.WordTrace tailWord_4094884 prefixEnd_4094884 700881238801887327072659 := by
  unfold tailWord_4094884
  simp only [CollatzResearch.WordTrace]
  refine ⟨74676344648471046677085853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99568459531294728902781137 74676344648471046677085853)
  ·
    refine ⟨28003629243176642503907195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74676344648471046677085853 28003629243176642503907195)
    ·
      refine ⟨42005443864764963755860793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28003629243176642503907195 42005443864764963755860793)
      ·
        refine ⟨31504082898573722816895595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42005443864764963755860793 31504082898573722816895595)
        ·
          refine ⟨47256124347860584225343393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31504082898573722816895595 47256124347860584225343393)
          ·
            refine ⟨35442093260895438169007545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47256124347860584225343393 35442093260895438169007545)
            ·
              refine ⟨26581569945671578626755659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35442093260895438169007545 26581569945671578626755659)
              ·
                refine ⟨39872354918507367940133489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26581569945671578626755659 39872354918507367940133489)
                ·
                  refine ⟨29904266188880525955100117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39872354918507367940133489 29904266188880525955100117)
                  ·
                    refine ⟨700881238801887327072659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29904266188880525955100117 700881238801887327072659)
                    ·
                      rfl

theorem cell23_4094884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_4094884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094884 prefixEnd_4094884 := by exact prefixLift 4094884
  have htrace : WordTrace (prefixWord ++ tailWord_4094884) baseStart_4094884 baseEnd_4094884 := by
    simpa [prefixWord, tailWord_4094884, baseEnd_4094884] using wordTrace_append hprefix tailTrace_4094884
  have hstable : (prefixWord ++ tailWord_4094884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094884).length < 2 ^ (prefixWord ++ tailWord_4094884).sum := by decide
  have hdescent : baseEnd_4094884 < baseStart_4094884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094891 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 5, 3, 2]
def baseStart_4094891 : Nat := 118140960795 + 4094891 * 2 ^ 59
def prefixEnd_4094891 : Nat := 4983230072969 + 3 ^ 40 * 4094891 * 2
def baseEnd_4094891 : Nat := 2102647310770243453830445

theorem tailTrace_4094891 : CollatzResearch.WordTrace tailWord_4094891 prefixEnd_4094891 2102647310770243453830445 := by
  unfold tailWord_4094891
  simp only [CollatzResearch.WordTrace]
  refine ⟨149352944607916733549676527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99568629738611155699784351 149352944607916733549676527)
  ·
    refine ⟨224029416911875100324514791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149352944607916733549676527 224029416911875100324514791)
    ·
      refine ⟨336044125367812650486772187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224029416911875100324514791 336044125367812650486772187)
      ·
        refine ⟨504066188051718975730158281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336044125367812650486772187 504066188051718975730158281)
        ·
          refine ⟨378049641038789231797618711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504066188051718975730158281 378049641038789231797618711)
          ·
            refine ⟨567074461558183847696428067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378049641038789231797618711 567074461558183847696428067)
            ·
              refine ⟨850611692337275771544642101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567074461558183847696428067 850611692337275771544642101)
              ·
                refine ⟨79744846156619603582310197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 850611692337275771544642101 79744846156619603582310197)
                ·
                  refine ⟨7476079327183087835841581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79744846156619603582310197 7476079327183087835841581)
                  ·
                    refine ⟨2803529747693657938440593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7476079327183087835841581 2803529747693657938440593)
                    ·
                      refine ⟨2102647310770243453830445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2803529747693657938440593 2102647310770243453830445)
                      ·
                        rfl

theorem cell23_4094891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 3, 2].length) (baseStart_4094891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094891 prefixEnd_4094891 := by exact prefixLift 4094891
  have htrace : WordTrace (prefixWord ++ tailWord_4094891) baseStart_4094891 baseEnd_4094891 := by
    simpa [prefixWord, tailWord_4094891, baseEnd_4094891] using wordTrace_append hprefix tailTrace_4094891
  have hstable : (prefixWord ++ tailWord_4094891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094891).length < 2 ^ (prefixWord ++ tailWord_4094891).sum := by decide
  have hdescent : baseEnd_4094891 < baseStart_4094891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094951 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_4094951 : Nat := 118140960795 + 4094951 * 2 ^ 59
def prefixEnd_4094951 : Nat := 4983230072969 + 3 ^ 40 * 4094951 * 2
def baseEnd_4094951 : Nat := 2102678119609513219080169

theorem tailTrace_4094951 : CollatzResearch.WordTrace tailWord_4094951 prefixEnd_4094951 2102678119609513219080169 := by
  unfold tailWord_4094951
  simp only [CollatzResearch.WordTrace]
  refine ⟨149355132987699363796860707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99570088658466242531240471 149355132987699363796860707)
  ·
    refine ⟨224032699481549045695291061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149355132987699363796860707 224032699481549045695291061)
    ·
      refine ⟨21003065576395223033933537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224032699481549045695291061 21003065576395223033933537)
      ·
        refine ⟨15752299182296417275450153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21003065576395223033933537 15752299182296417275450153)
        ·
          refine ⟨11814224386722312956587615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15752299182296417275450153 11814224386722312956587615)
          ·
            refine ⟨17721336580083469434881423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11814224386722312956587615 17721336580083469434881423)
            ·
              refine ⟨26582004870125204152322135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17721336580083469434881423 26582004870125204152322135)
              ·
                refine ⟨39873007305187806228483203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26582004870125204152322135 39873007305187806228483203)
                ·
                  refine ⟨59809510957781709342724805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39873007305187806228483203 59809510957781709342724805)
                  ·
                    refine ⟨11214283304584070501760901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59809510957781709342724805 11214283304584070501760901)
                    ·
                      refine ⟨2102678119609513219080169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11214283304584070501760901 2102678119609513219080169)
                      ·
                        rfl

theorem cell23_4094951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_4094951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094951 prefixEnd_4094951 := by exact prefixLift 4094951
  have htrace : WordTrace (prefixWord ++ tailWord_4094951) baseStart_4094951 baseEnd_4094951 := by
    simpa [prefixWord, tailWord_4094951, baseEnd_4094951] using wordTrace_append hprefix tailTrace_4094951
  have hstable : (prefixWord ++ tailWord_4094951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094951).length < 2 ^ (prefixWord ++ tailWord_4094951).sum := by decide
  have hdescent : baseEnd_4094951 < baseStart_4094951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4094961 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 7]
def baseStart_4094961 : Nat := 118140960795 + 4094961 * 2 ^ 59
def prefixEnd_4094961 : Nat := 4983230072969 + 3 ^ 40 * 4094961 * 2
def baseEnd_4094961 : Nat := 233631472712895353328347

theorem tailTrace_4094961 : CollatzResearch.WordTrace tailWord_4094961 prefixEnd_4094961 233631472712895353328347 := by
  unfold tailWord_4094961
  simp only [CollatzResearch.WordTrace]
  refine ⟨149355497717663135504724737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99570331811775423669816491 149355497717663135504724737)
  ·
    refine ⟨112016623288247351628543553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149355497717663135504724737 112016623288247351628543553)
    ·
      refine ⟨84012467466185513721407665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112016623288247351628543553 84012467466185513721407665)
      ·
        refine ⟨63009350599639135291055749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84012467466185513721407665 63009350599639135291055749)
        ·
          refine ⟨11814253237432337867072953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63009350599639135291055749 11814253237432337867072953)
          ·
            refine ⟨8860689928074253400304715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11814253237432337867072953 8860689928074253400304715)
            ·
              refine ⟨13291034892111380100457073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8860689928074253400304715 13291034892111380100457073)
              ·
                refine ⟨9968276169083535075342805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13291034892111380100457073 9968276169083535075342805)
                ·
                  refine ⟨233631472712895353328347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9968276169083535075342805 233631472712895353328347)
                  ·
                    rfl

theorem cell23_4094961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 7].length) (baseStart_4094961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4094961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4094961 prefixEnd_4094961 := by exact prefixLift 4094961
  have htrace : WordTrace (prefixWord ++ tailWord_4094961) baseStart_4094961 baseEnd_4094961 := by
    simpa [prefixWord, tailWord_4094961, baseEnd_4094961] using wordTrace_append hprefix tailTrace_4094961
  have hstable : (prefixWord ++ tailWord_4094961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4094961).length < 2 ^ (prefixWord ++ tailWord_4094961).sum := by decide
  have hdescent : baseEnd_4094961 < baseStart_4094961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4094961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095011 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 4]
def baseStart_4095011 : Nat := 118140960795 + 4095011 * 2 ^ 59
def prefixEnd_4095011 : Nat := 4983230072969 + 3 ^ 40 * 4095011 * 2
def baseEnd_4095011 : Nat := 2102708928448782984329893

theorem tailTrace_4095011 : CollatzResearch.WordTrace tailWord_4095011 prefixEnd_4095011 2102708928448782984329893 := by
  unfold tailWord_4095011
  simp only [CollatzResearch.WordTrace]
  refine ⟨149357321367481994044044887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99571547578321329362696591 149357321367481994044044887)
  ·
    refine ⟨224035982051222991066067331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149357321367481994044044887 224035982051222991066067331)
    ·
      refine ⟨336053973076834486599100997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224035982051222991066067331 336053973076834486599100997)
      ·
        refine ⟨63010119951906466237331437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336053973076834486599100997 63010119951906466237331437)
        ·
          refine ⟨23628794981964924838999289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63010119951906466237331437 23628794981964924838999289)
          ·
            refine ⟨17721596236473693629249467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23628794981964924838999289 17721596236473693629249467)
            ·
              refine ⟨26582394354710540443874201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17721596236473693629249467 26582394354710540443874201)
              ·
                refine ⟨19936795766032905332905651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26582394354710540443874201 19936795766032905332905651)
                ·
                  refine ⟨29905193649049357999358477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19936795766032905332905651 29905193649049357999358477)
                  ·
                    refine ⟨11214447618393509249759429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29905193649049357999358477 11214447618393509249759429)
                    ·
                      refine ⟨2102708928448782984329893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11214447618393509249759429 2102708928448782984329893)
                      ·
                        rfl

theorem cell23_4095011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_4095011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095011 prefixEnd_4095011 := by exact prefixLift 4095011
  have htrace : WordTrace (prefixWord ++ tailWord_4095011) baseStart_4095011 baseEnd_4095011 := by
    simpa [prefixWord, tailWord_4095011, baseEnd_4095011] using wordTrace_append hprefix tailTrace_4095011
  have hstable : (prefixWord ++ tailWord_4095011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095011).length < 2 ^ (prefixWord ++ tailWord_4095011).sum := by decide
  have hdescent : baseEnd_4095011 < baseStart_4095011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095048 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 2, 2, 3]
def baseStart_4095048 : Nat := 118140960795 + 4095048 * 2 ^ 59
def prefixEnd_4095048 : Nat := 4983230072969 + 3 ^ 40 * 4095048 * 2
def baseEnd_4095048 : Nat := 2102727927232999339567223

theorem tailTrace_4095048 : CollatzResearch.WordTrace tailWord_4095048 prefixEnd_4095048 2102727927232999339567223 := by
  unfold tailWord_4095048
  simp only [CollatzResearch.WordTrace]
  refine ⟨74679335434173974681570899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99572447245565299575427865 74679335434173974681570899)
  ·
    refine ⟨112019003151260962022356349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74679335434173974681570899 112019003151260962022356349)
    ·
      refine ⟨42007126181722860758383631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112019003151260962022356349 42007126181722860758383631)
      ·
        refine ⟨63010689272584291137575447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42007126181722860758383631 63010689272584291137575447)
        ·
          refine ⟨94516033908876436706363171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63010689272584291137575447 94516033908876436706363171)
          ·
            refine ⟨141774050863314655059544757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94516033908876436706363171 141774050863314655059544757)
            ·
              refine ⟨13291317268435748911832321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141774050863314655059544757 13291317268435748911832321)
              ·
                refine ⟨9968487951326811683874241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13291317268435748911832321 9968487951326811683874241)
                ·
                  refine ⟨7476365963495108762905681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9968487951326811683874241 7476365963495108762905681)
                  ·
                    refine ⟨5607274472621331572179261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7476365963495108762905681 5607274472621331572179261)
                    ·
                      refine ⟨2102727927232999339567223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5607274472621331572179261 2102727927232999339567223)
                      ·
                        rfl

theorem cell23_4095048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_4095048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095048 prefixEnd_4095048 := by exact prefixLift 4095048
  have htrace : WordTrace (prefixWord ++ tailWord_4095048) baseStart_4095048 baseEnd_4095048 := by
    simpa [prefixWord, tailWord_4095048, baseEnd_4095048] using wordTrace_append hprefix tailTrace_4095048
  have hstable : (prefixWord ++ tailWord_4095048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095048).length < 2 ^ (prefixWord ++ tailWord_4095048).sum := by decide
  have hdescent : baseEnd_4095048 < baseStart_4095048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095068 : List Nat := [2, 2, 4, 1, 1, 1, 3, 3, 6]
def baseStart_4095068 : Nat := 118140960795 + 4095068 * 2 ^ 59
def prefixEnd_4095068 : Nat := 4983230072969 + 3 ^ 40 * 4095068 * 2
def baseEnd_4095068 : Nat := 233637577427343251257459

theorem tailTrace_4095068 : CollatzResearch.WordTrace tailWord_4095068 prefixEnd_4095068 233637577427343251257459 := by
  unfold tailWord_4095068
  simp only [CollatzResearch.WordTrace]
  refine ⟨74679700164137746389434929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99572933552183661852579905 74679700164137746389434929)
  ·
    refine ⟨56009775123103309792076197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74679700164137746389434929 56009775123103309792076197)
    ·
      refine ⟨10501832835581870586014287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56009775123103309792076197 10501832835581870586014287)
      ·
        refine ⟨15752749253372805879021431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10501832835581870586014287 15752749253372805879021431)
        ·
          refine ⟨23629123880059208818532147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15752749253372805879021431 23629123880059208818532147)
          ·
            refine ⟨35443685820088813227798221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23629123880059208818532147 35443685820088813227798221)
            ·
              refine ⟨13291382182533304960424333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35443685820088813227798221 13291382182533304960424333)
              ·
                refine ⟨4984268318449989360159125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13291382182533304960424333 4984268318449989360159125)
                ·
                  refine ⟨233637577427343251257459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4984268318449989360159125 233637577427343251257459)
                  ·
                    rfl

theorem cell23_4095068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 6].length) (baseStart_4095068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095068 prefixEnd_4095068 := by exact prefixLift 4095068
  have htrace : WordTrace (prefixWord ++ tailWord_4095068) baseStart_4095068 baseEnd_4095068 := by
    simpa [prefixWord, tailWord_4095068, baseEnd_4095068] using wordTrace_append hprefix tailTrace_4095068
  have hstable : (prefixWord ++ tailWord_4095068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095068).length < 2 ^ (prefixWord ++ tailWord_4095068).sum := by decide
  have hdescent : baseEnd_4095068 < baseStart_4095068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095111 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 5, 6]
def baseStart_4095111 : Nat := 118140960795 + 4095111 * 2 ^ 59
def prefixEnd_4095111 : Nat := 4983230072969 + 3 ^ 40 * 4095111 * 2
def baseEnd_4095111 : Nat := 700920092171410864359811

theorem tailTrace_4095111 : CollatzResearch.WordTrace tailWord_4095111 prefixEnd_4095111 700920092171410864359811 := by
  unfold tailWord_4095111
  simp only [CollatzResearch.WordTrace]
  refine ⟨149360968667119711122685187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99573979111413140748456791 149360968667119711122685187)
  ·
    refine ⟨224041453000679566684027781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149360968667119711122685187 224041453000679566684027781)
    ·
      refine ⟨42007772437627418753255209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224041453000679566684027781 42007772437627418753255209)
      ·
        refine ⟨31505829328220564064941407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42007772437627418753255209 31505829328220564064941407)
        ·
          refine ⟨47258743992330846097412111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31505829328220564064941407 47258743992330846097412111)
          ·
            refine ⟨70888115988496269146118167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47258743992330846097412111 70888115988496269146118167)
            ·
              refine ⟨106332173982744403719177251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70888115988496269146118167 106332173982744403719177251)
              ·
                refine ⟨159498260974116605578765877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106332173982744403719177251 159498260974116605578765877)
                ·
                  refine ⟨14952961966323431773009301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159498260974116605578765877 14952961966323431773009301)
                  ·
                    refine ⟨700920092171410864359811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14952961966323431773009301 700920092171410864359811)
                    ·
                      rfl

theorem cell23_4095111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_4095111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095111 prefixEnd_4095111 := by exact prefixLift 4095111
  have htrace : WordTrace (prefixWord ++ tailWord_4095111) baseStart_4095111 baseEnd_4095111 := by
    simpa [prefixWord, tailWord_4095111, baseEnd_4095111] using wordTrace_append hprefix tailTrace_4095111
  have hstable : (prefixWord ++ tailWord_4095111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095111).length < 2 ^ (prefixWord ++ tailWord_4095111).sum := by decide
  have hdescent : baseEnd_4095111 < baseStart_4095111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095128 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 1, 6]
def baseStart_4095128 : Nat := 118140960795 + 4095128 * 2 ^ 59
def prefixEnd_4095128 : Nat := 4983230072969 + 3 ^ 40 * 4095128 * 2
def baseEnd_4095128 : Nat := 700923001895119675522285

theorem tailTrace_4095128 : CollatzResearch.WordTrace tailWord_4095128 prefixEnd_4095128 700923001895119675522285 := by
  unfold tailWord_4095128
  simp only [CollatzResearch.WordTrace]
  refine ⟨74680794354029061513027019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99574392472038748684036025 74680794354029061513027019)
  ·
    refine ⟨112021191531043592269540529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74680794354029061513027019 112021191531043592269540529)
    ·
      refine ⟨84015893648282694202155397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112021191531043592269540529 84015893648282694202155397)
      ·
        refine ⟨15752980059053005162904137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84015893648282694202155397 15752980059053005162904137)
        ·
          refine ⟨11814735044289753872178103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15752980059053005162904137 11814735044289753872178103)
          ·
            refine ⟨17722102566434630808267155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11814735044289753872178103 17722102566434630808267155)
            ·
              refine ⟨26583153849651946212400733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17722102566434630808267155 26583153849651946212400733)
              ·
                refine ⟨9968682693619479829650275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26583153849651946212400733 9968682693619479829650275)
                ·
                  refine ⟨14953024040429219744475413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9968682693619479829650275 14953024040429219744475413)
                  ·
                    refine ⟨700923001895119675522285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14953024040429219744475413 700923001895119675522285)
                    ·
                      rfl

theorem cell23_4095128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_4095128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095128 prefixEnd_4095128 := by exact prefixLift 4095128
  have htrace : WordTrace (prefixWord ++ tailWord_4095128) baseStart_4095128 baseEnd_4095128 := by
    simpa [prefixWord, tailWord_4095128, baseEnd_4095128] using wordTrace_append hprefix tailTrace_4095128
  have hstable : (prefixWord ++ tailWord_4095128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095128).length < 2 ^ (prefixWord ++ tailWord_4095128).sum := by decide
  have hdescent : baseEnd_4095128 < baseStart_4095128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095146 : List Nat := [3, 1, 5, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_4095146 : Nat := 118140960795 + 4095146 * 2 ^ 59
def prefixEnd_4095146 : Nat := 4983230072969 + 3 ^ 40 * 4095146 * 2
def baseEnd_4095146 : Nat := 2102778248337139956141773

theorem tailTrace_4095146 : CollatzResearch.WordTrace tailWord_4095146 prefixEnd_4095146 2102778248337139956141773 := by
  unfold tailWord_4095146
  simp only [CollatzResearch.WordTrace]
  refine ⟨37340561305498228025052323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99574830147995274733472861 37340561305498228025052323)
  ·
    refine ⟨56010841958247342037578485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37340561305498228025052323 56010841958247342037578485)
    ·
      refine ⟨5251016433585688316022983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56010841958247342037578485 5251016433585688316022983)
      ·
        refine ⟨7876524650378532474034475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5251016433585688316022983 7876524650378532474034475)
        ·
          refine ⟨11814786975567798711051713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7876524650378532474034475 11814786975567798711051713)
          ·
            refine ⟨8861090231675849033288785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11814786975567798711051713 8861090231675849033288785)
            ·
              refine ⟨6645817673756886774966589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8861090231675849033288785 6645817673756886774966589)
              ·
                refine ⟨2492181627658832540612471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6645817673756886774966589 2492181627658832540612471)
                ·
                  refine ⟨3738272441488248810918707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492181627658832540612471 3738272441488248810918707)
                  ·
                    refine ⟨5607408662232373216378061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3738272441488248810918707 5607408662232373216378061)
                    ·
                      refine ⟨2102778248337139956141773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5607408662232373216378061 2102778248337139956141773)
                      ·
                        rfl

theorem cell23_4095146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_4095146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095146 prefixEnd_4095146 := by exact prefixLift 4095146
  have htrace : WordTrace (prefixWord ++ tailWord_4095146) baseStart_4095146 baseEnd_4095146 := by
    simpa [prefixWord, tailWord_4095146, baseEnd_4095146] using wordTrace_append hprefix tailTrace_4095146
  have hstable : (prefixWord ++ tailWord_4095146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095146).length < 2 ^ (prefixWord ++ tailWord_4095146).sum := by decide
  have hdescent : baseEnd_4095146 < baseStart_4095146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095149 : List Nat := [1, 5, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_4095149 : Nat := 118140960795 + 4095149 * 2 ^ 59
def prefixEnd_4095149 : Nat := 4983230072969 + 3 ^ 40 * 4095149 * 2
def baseEnd_4095149 : Nat := 700926596259701148134753

theorem tailTrace_4095149 : CollatzResearch.WordTrace tailWord_4095149 prefixEnd_4095149 700926596259701148134753 := by
  unfold tailWord_4095149
  simp only [CollatzResearch.WordTrace]
  refine ⟨149362354640982043612568501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99574903093988029075045667 149362354640982043612568501)
  ·
    refine ⟨14002720747592066588678297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149362354640982043612568501 14002720747592066588678297)
    ·
      refine ⟨10502040560694049941508723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14002720747592066588678297 10502040560694049941508723)
      ·
        refine ⟨15753060841041074912263085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10502040560694049941508723 15753060841041074912263085)
        ·
          refine ⟨5907397815390403092098657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15753060841041074912263085 5907397815390403092098657)
          ·
            refine ⟨4430548361542802319073993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5907397815390403092098657 4430548361542802319073993)
            ·
              refine ⟨3322911271157101739305495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4430548361542802319073993 3322911271157101739305495)
              ·
                refine ⟨4984366906735652608958243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3322911271157101739305495 4984366906735652608958243)
                ·
                  refine ⟨7476550360103478913437365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4984366906735652608958243 7476550360103478913437365)
                  ·
                    refine ⟨700926596259701148134753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7476550360103478913437365 700926596259701148134753)
                    ·
                      rfl

theorem cell23_4095149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_4095149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095149 prefixEnd_4095149 := by exact prefixLift 4095149
  have htrace : WordTrace (prefixWord ++ tailWord_4095149) baseStart_4095149 baseEnd_4095149 := by
    simpa [prefixWord, tailWord_4095149, baseEnd_4095149] using wordTrace_append hprefix tailTrace_4095149
  have hstable : (prefixWord ++ tailWord_4095149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095149).length < 2 ^ (prefixWord ++ tailWord_4095149).sum := by decide
  have hdescent : baseEnd_4095149 < baseStart_4095149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095169 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_4095169 : Nat := 118140960795 + 4095169 * 2 ^ 59
def prefixEnd_4095169 : Nat := 4983230072969 + 3 ^ 40 * 4095169 * 2
def baseEnd_4095169 : Nat := 2102790058392193366154167

theorem tailTrace_4095169 : CollatzResearch.WordTrace tailWord_4095169 prefixEnd_4095169 2102790058392193366154167 := by
  unfold tailWord_4095169
  simp only [CollatzResearch.WordTrace]
  refine ⟨149363084100909587028296561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99575389400606391352197707 149363084100909587028296561)
  ·
    refine ⟨112022313075682190271222421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149363084100909587028296561 112022313075682190271222421)
    ·
      refine ⟨5251045925422602668963551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112022313075682190271222421 5251045925422602668963551)
      ·
        refine ⟨7876568888133904003445327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5251045925422602668963551 7876568888133904003445327)
        ·
          refine ⟨11814853332200856005167991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7876568888133904003445327 11814853332200856005167991)
          ·
            refine ⟨17722279998301284007751987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11814853332200856005167991 17722279998301284007751987)
            ·
              refine ⟨26583419997451926011627981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17722279998301284007751987 26583419997451926011627981)
              ·
                refine ⟨9968782499044472254360493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26583419997451926011627981 9968782499044472254360493)
                ·
                  refine ⟨3738293437141677095385185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9968782499044472254360493 3738293437141677095385185)
                  ·
                    refine ⟨2803720077856257821538889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3738293437141677095385185 2803720077856257821538889)
                    ·
                      refine ⟨2102790058392193366154167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2803720077856257821538889 2102790058392193366154167)
                      ·
                        rfl

theorem cell23_4095169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_4095169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095169 prefixEnd_4095169 := by exact prefixLift 4095169
  have htrace : WordTrace (prefixWord ++ tailWord_4095169) baseStart_4095169 baseEnd_4095169 := by
    simpa [prefixWord, tailWord_4095169, baseEnd_4095169] using wordTrace_append hprefix tailTrace_4095169
  have hstable : (prefixWord ++ tailWord_4095169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095169).length < 2 ^ (prefixWord ++ tailWord_4095169).sum := by decide
  have hdescent : baseEnd_4095169 < baseStart_4095169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095171 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 2, 7]
def baseStart_4095171 : Nat := 118140960795 + 4095171 * 2 ^ 59
def prefixEnd_4095171 : Nat := 4983230072969 + 3 ^ 40 * 4095171 * 2
def baseEnd_4095171 : Nat := 700930361784500786109719

theorem tailTrace_4095171 : CollatzResearch.WordTrace tailWord_4095171 prefixEnd_4095171 700930361784500786109719 := by
  unfold tailWord_4095171
  simp only [CollatzResearch.WordTrace]
  refine ⟨149363157046902341369869367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99575438031268227579912911 149363157046902341369869367)
  ·
    refine ⟨224044735570353512054804051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149363157046902341369869367 224044735570353512054804051)
    ·
      refine ⟨336067103355530268082206077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224044735570353512054804051 336067103355530268082206077)
      ·
        refine ⟨126025163758323850530827279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336067103355530268082206077 126025163758323850530827279)
        ·
          refine ⟨189037745637485775796240919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126025163758323850530827279 189037745637485775796240919)
          ·
            refine ⟨283556618456228663694361379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189037745637485775796240919 283556618456228663694361379)
            ·
              refine ⟨425334927684342995541542069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283556618456228663694361379 425334927684342995541542069)
              ·
                refine ⟨39875149470407155832019569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 425334927684342995541542069 39875149470407155832019569)
                ·
                  refine ⟨29906362102805366874014677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39875149470407155832019569 29906362102805366874014677)
                  ·
                    refine ⟨700930361784500786109719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29906362102805366874014677 700930361784500786109719)
                    ·
                      rfl

theorem cell23_4095171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 7].length) (baseStart_4095171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095171 prefixEnd_4095171 := by exact prefixLift 4095171
  have htrace : WordTrace (prefixWord ++ tailWord_4095171) baseStart_4095171 baseEnd_4095171 := by
    simpa [prefixWord, tailWord_4095171, baseEnd_4095171] using wordTrace_append hprefix tailTrace_4095171
  have hstable : (prefixWord ++ tailWord_4095171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095171).length < 2 ^ (prefixWord ++ tailWord_4095171).sum := by decide
  have hdescent : baseEnd_4095171 < baseStart_4095171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095182 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4]
def baseStart_4095182 : Nat := 118140960795 + 4095182 * 2 ^ 59
def prefixEnd_4095182 : Nat := 4983230072969 + 3 ^ 40 * 4095182 * 2
def baseEnd_4095182 : Nat := 2102796733640701815291607

theorem tailTrace_4095182 : CollatzResearch.WordTrace tailWord_4095182 prefixEnd_4095182 2102796733640701815291607 := by
  unfold tailWord_4095182
  simp only [CollatzResearch.WordTrace]
  refine ⟨18670444781232811281064975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99575705499908326832346533 18670444781232811281064975)
  ·
    refine ⟨28005667171849216921597463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18670444781232811281064975 28005667171849216921597463)
    ·
      refine ⟨42008500757773825382396195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28005667171849216921597463 42008500757773825382396195)
      ·
        refine ⟨63012751136660738073594293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42008500757773825382396195 63012751136660738073594293)
        ·
          refine ⟨5907445419061944194399465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63012751136660738073594293 5907445419061944194399465)
          ·
            refine ⟨4430584064296458145799599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5907445419061944194399465 4430584064296458145799599)
            ·
              refine ⟨6645876096444687218699399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4430584064296458145799599 6645876096444687218699399)
              ·
                refine ⟨9968814144667030828049099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6645876096444687218699399 9968814144667030828049099)
                ·
                  refine ⟨14953221217000546242073649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9968814144667030828049099 14953221217000546242073649)
                  ·
                    refine ⟨11214915912750409681555237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14953221217000546242073649 11214915912750409681555237)
                    ·
                      refine ⟨2102796733640701815291607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11214915912750409681555237 2102796733640701815291607)
                      ·
                        rfl

theorem cell23_4095182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_4095182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095182 prefixEnd_4095182 := by exact prefixLift 4095182
  have htrace : WordTrace (prefixWord ++ tailWord_4095182) baseStart_4095182 baseEnd_4095182 := by
    simpa [prefixWord, tailWord_4095182, baseEnd_4095182] using wordTrace_append hprefix tailTrace_4095182
  have hstable : (prefixWord ++ tailWord_4095182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095182).length < 2 ^ (prefixWord ++ tailWord_4095182).sum := by decide
  have hdescent : baseEnd_4095182 < baseStart_4095182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095192 : List Nat := [2, 1, 2, 2, 6, 1, 2, 7]
def baseStart_4095192 : Nat := 118140960795 + 4095192 * 2 ^ 59
def prefixEnd_4095192 : Nat := 4983230072969 + 3 ^ 40 * 4095192 * 2
def baseEnd_4095192 : Nat := 77881550683231362080243

theorem tailTrace_4095192 : CollatzResearch.WordTrace tailWord_4095192 prefixEnd_4095192 77881550683231362080243 := by
  unfold tailWord_4095192
  simp only [CollatzResearch.WordTrace]
  refine ⟨74681961489913130978191915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99575948653217507970922553 74681961489913130978191915)
  ·
    refine ⟨112022942234869696467287873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74681961489913130978191915 112022942234869696467287873)
    ·
      refine ⟨84017206676152272350465905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112022942234869696467287873 84017206676152272350465905)
      ·
        refine ⟨63012905007114204262849429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84017206676152272350465905 63012905007114204262849429)
        ·
          refine ⟨2953729922208478324821067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63012905007114204262849429 2953729922208478324821067)
          ·
            refine ⟨4430594883312717487231601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2953729922208478324821067 4430594883312717487231601)
            ·
              refine ⟨3322946162484538115423701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4430594883312717487231601 3322946162484538115423701)
              ·
                refine ⟨77881550683231362080243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3322946162484538115423701 77881550683231362080243)
                ·
                  rfl

theorem cell23_4095192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 7].length) (baseStart_4095192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095192 prefixEnd_4095192 := by exact prefixLift 4095192
  have htrace : WordTrace (prefixWord ++ tailWord_4095192) baseStart_4095192 baseEnd_4095192 := by
    simpa [prefixWord, tailWord_4095192, baseEnd_4095192] using wordTrace_append hprefix tailTrace_4095192
  have hstable : (prefixWord ++ tailWord_4095192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095192).length < 2 ^ (prefixWord ++ tailWord_4095192).sum := by decide
  have hdescent : baseEnd_4095192 < baseStart_4095192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095212 : List Nat := [2, 2, 1, 1, 2, 4, 2, 3, 1, 3, 2]
def baseStart_4095212 : Nat := 118140960795 + 4095212 * 2 ^ 59
def prefixEnd_4095212 : Nat := 4983230072969 + 3 ^ 40 * 4095212 * 2
def baseEnd_4095212 : Nat := 2102812138060336697916469

theorem tailTrace_4095212 : CollatzResearch.WordTrace tailWord_4095212 prefixEnd_4095212 2102812138060336697916469 := by
  unfold tailWord_4095212
  simp only [CollatzResearch.WordTrace]
  refine ⟨74682326219876902686055945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99576434959835870248074593 74682326219876902686055945)
  ·
    refine ⟨56011744664907677014541959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74682326219876902686055945 56011744664907677014541959)
    ·
      refine ⟨84017616997361515521812939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56011744664907677014541959 84017616997361515521812939)
      ·
        refine ⟨126026425496042273282719409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84017616997361515521812939 126026425496042273282719409)
        ·
          refine ⟨94519819122031704962039557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126026425496042273282719409 94519819122031704962039557)
          ·
            refine ⟨17722466085380944680382417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94519819122031704962039557 17722466085380944680382417)
            ·
              refine ⟨13291849564035708510286813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17722466085380944680382417 13291849564035708510286813)
              ·
                refine ⟨4984443586513390691357555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13291849564035708510286813 4984443586513390691357555)
                ·
                  refine ⟨7476665379770086037036333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4984443586513390691357555 7476665379770086037036333)
                  ·
                    refine ⟨2803749517413782263888625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7476665379770086037036333 2803749517413782263888625)
                    ·
                      refine ⟨2102812138060336697916469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2803749517413782263888625 2102812138060336697916469)
                      ·
                        rfl

theorem cell23_4095212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 3, 2].length) (baseStart_4095212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095212 prefixEnd_4095212 := by exact prefixLift 4095212
  have htrace : WordTrace (prefixWord ++ tailWord_4095212) baseStart_4095212 baseEnd_4095212 := by
    simpa [prefixWord, tailWord_4095212, baseEnd_4095212] using wordTrace_append hprefix tailTrace_4095212
  have hstable : (prefixWord ++ tailWord_4095212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095212).length < 2 ^ (prefixWord ++ tailWord_4095212).sum := by decide
  have hdescent : baseEnd_4095212 < baseStart_4095212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095220 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_4095220 : Nat := 118140960795 + 4095220 * 2 ^ 59
def prefixEnd_4095220 : Nat := 4983230072969 + 3 ^ 40 * 4095220 * 2
def baseEnd_4095220 : Nat := 2102816245905572666616433

theorem tailTrace_4095220 : CollatzResearch.WordTrace tailWord_4095220 prefixEnd_4095220 2102816245905572666616433 := by
  unfold tailWord_4095220
  simp only [CollatzResearch.WordTrace]
  refine ⟨74682472111862411369201557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99576629482483215158935409 74682472111862411369201557)
  ·
    refine ⟨3500740880243550532931323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74682472111862411369201557 3500740880243550532931323)
    ·
      refine ⟨5251111320365325799396985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3500740880243550532931323 5251111320365325799396985)
      ·
        refine ⟨3938333490273994349547739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5251111320365325799396985 3938333490273994349547739)
        ·
          refine ⟨5907500235410991524321609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3938333490273994349547739 5907500235410991524321609)
          ·
            refine ⟨4430625176558243643241207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5907500235410991524321609 4430625176558243643241207)
            ·
              refine ⟨6645937764837365464861811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4430625176558243643241207 6645937764837365464861811)
              ·
                refine ⟨9968906647256048197292717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6645937764837365464861811 9968906647256048197292717)
                ·
                  refine ⟨3738339992721018073984769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9968906647256048197292717 3738339992721018073984769)
                  ·
                    refine ⟨2803754994540763555488577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3738339992721018073984769 2803754994540763555488577)
                    ·
                      refine ⟨2102816245905572666616433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2803754994540763555488577 2102816245905572666616433)
                      ·
                        rfl

theorem cell23_4095220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_4095220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095220 prefixEnd_4095220 := by exact prefixLift 4095220
  have htrace : WordTrace (prefixWord ++ tailWord_4095220) baseStart_4095220 baseEnd_4095220 := by
    simpa [prefixWord, tailWord_4095220, baseEnd_4095220] using wordTrace_append hprefix tailTrace_4095220
  have hstable : (prefixWord ++ tailWord_4095220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095220).length < 2 ^ (prefixWord ++ tailWord_4095220).sum := by decide
  have hdescent : baseEnd_4095220 < baseStart_4095220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095236 : List Nat := [2, 3, 2, 2, 2, 3, 2, 1, 2, 1, 3]
def baseStart_4095236 : Nat := 118140960795 + 4095236 * 2 ^ 59
def prefixEnd_4095236 : Nat := 4983230072969 + 3 ^ 40 * 4095236 * 2
def baseEnd_4095236 : Nat := 2102824461596044604016359

theorem tailTrace_4095236 : CollatzResearch.WordTrace tailWord_4095236 prefixEnd_4095236 2102824461596044604016359 := by
  unfold tailWord_4095236
  simp only [CollatzResearch.WordTrace]
  refine ⟨74682763895833428735492781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99577018527777904980657041 74682763895833428735492781)
  ·
    refine ⟨28006036460937535775809793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74682763895833428735492781 28006036460937535775809793)
    ·
      refine ⟨21004527345703151831857345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28006036460937535775809793 21004527345703151831857345)
      ·
        refine ⟨15753395509277363873893009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21004527345703151831857345 15753395509277363873893009)
        ·
          refine ⟨11815046631958022905419757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15753395509277363873893009 11815046631958022905419757)
          ·
            refine ⟨4430642486984258589532409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11815046631958022905419757 4430642486984258589532409)
            ·
              refine ⟨3322981865238193942149307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4430642486984258589532409 3322981865238193942149307)
              ·
                refine ⟨4984472797857290913223961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3322981865238193942149307 4984472797857290913223961)
                ·
                  refine ⟨3738354598392968184917971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4984472797857290913223961 3738354598392968184917971)
                  ·
                    refine ⟨5607531897589452277376957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3738354598392968184917971 5607531897589452277376957)
                    ·
                      refine ⟨2102824461596044604016359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5607531897589452277376957 2102824461596044604016359)
                      ·
                        rfl

theorem cell23_4095236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_4095236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095236 prefixEnd_4095236 := by exact prefixLift 4095236
  have htrace : WordTrace (prefixWord ++ tailWord_4095236) baseStart_4095236 baseEnd_4095236 := by
    simpa [prefixWord, tailWord_4095236, baseEnd_4095236] using wordTrace_append hprefix tailTrace_4095236
  have hstable : (prefixWord ++ tailWord_4095236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095236).length < 2 ^ (prefixWord ++ tailWord_4095236).sum := by decide
  have hdescent : baseEnd_4095236 < baseStart_4095236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095265 : List Nat := [1, 2, 3, 2, 1, 1, 1, 7, 5]
def baseStart_4095265 : Nat := 118140960795 + 4095265 * 2 ^ 59
def prefixEnd_4095265 : Nat := 4983230072969 + 3 ^ 40 * 4095265 * 2
def baseEnd_4095265 : Nat := 233648816948336110061525

theorem tailTrace_4095265 : CollatzResearch.WordTrace tailWord_4095265 prefixEnd_4095265 233648816948336110061525 := by
  unfold tailWord_4095265
  simp only [CollatzResearch.WordTrace]
  refine ⟨149366585508561795423791249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99577723672374530282527499 149366585508561795423791249)
  ·
    refine ⟨112024939131421346567843437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149366585508561795423791249 112024939131421346567843437)
    ·
      refine ⟨42009352174283004962941289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112024939131421346567843437 42009352174283004962941289)
      ·
        refine ⟨31507014130712253722205967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42009352174283004962941289 31507014130712253722205967)
        ·
          refine ⟨47260521196068380583308951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31507014130712253722205967 47260521196068380583308951)
          ·
            refine ⟨70890781794102570874963427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47260521196068380583308951 70890781794102570874963427)
            ·
              refine ⟨106336172691153856312445141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70890781794102570874963427 106336172691153856312445141)
              ·
                refine ⟨2492254047448918507322933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 106336172691153856312445141 2492254047448918507322933)
                ·
                  refine ⟨233648816948336110061525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2492254047448918507322933 233648816948336110061525)
                  ·
                    rfl

theorem cell23_4095265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 5].length) (baseStart_4095265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095265 prefixEnd_4095265 := by exact prefixLift 4095265
  have htrace : WordTrace (prefixWord ++ tailWord_4095265) baseStart_4095265 baseEnd_4095265 := by
    simpa [prefixWord, tailWord_4095265, baseEnd_4095265] using wordTrace_append hprefix tailTrace_4095265
  have hstable : (prefixWord ++ tailWord_4095265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095265).length < 2 ^ (prefixWord ++ tailWord_4095265).sum := by decide
  have hdescent : baseEnd_4095265 < baseStart_4095265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095282 : List Nat := [3, 2, 1, 1, 4, 2, 1, 4, 5]
def baseStart_4095282 : Nat := 118140960795 + 4095282 * 2 ^ 59
def prefixEnd_4095282 : Nat := 4983230072969 + 3 ^ 40 * 4095282 * 2
def baseEnd_4095282 : Nat := 233649786856239047115683

theorem tailTrace_4095282 : CollatzResearch.WordTrace tailWord_4095282 prefixEnd_4095282 233649786856239047115683 := by
  unfold tailWord_4095282
  simp only [CollatzResearch.WordTrace]
  refine ⟨37341801387375051831790025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99578137033000138218106733 37341801387375051831790025)
  ·
    refine ⟨28006351040531288873842519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37341801387375051831790025 28006351040531288873842519)
    ·
      refine ⟨42009526560796933310763779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28006351040531288873842519 42009526560796933310763779)
      ·
        refine ⟨63014289841195399966145669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42009526560796933310763779 63014289841195399966145669)
        ·
          refine ⟨11815179345224137493652313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63014289841195399966145669 11815179345224137493652313)
          ·
            refine ⟨8861384508918103120239235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11815179345224137493652313 8861384508918103120239235)
            ·
              refine ⟨13292076763377154680358853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8861384508918103120239235 13292076763377154680358853)
              ·
                refine ⟨2492264393133216502567285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13292076763377154680358853 2492264393133216502567285)
                ·
                  refine ⟨233649786856239047115683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2492264393133216502567285 233649786856239047115683)
                  ·
                    rfl

theorem cell23_4095282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_4095282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095282 prefixEnd_4095282 := by exact prefixLift 4095282
  have htrace : WordTrace (prefixWord ++ tailWord_4095282) baseStart_4095282 baseEnd_4095282 := by
    simpa [prefixWord, tailWord_4095282, baseEnd_4095282] using wordTrace_append hprefix tailTrace_4095282
  have hstable : (prefixWord ++ tailWord_4095282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095282).length < 2 ^ (prefixWord ++ tailWord_4095282).sum := by decide
  have hdescent : baseEnd_4095282 < baseStart_4095282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095315 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 1, 6, 2]
def baseStart_4095315 : Nat := 118140960795 + 4095315 * 2 ^ 59
def prefixEnd_4095315 : Nat := 4983230072969 + 3 ^ 40 * 4095315 * 2
def baseEnd_4095315 : Nat := 2102865026567749794928495

theorem tailTrace_4095315 : CollatzResearch.WordTrace tailWord_4095315 prefixEnd_4095315 2102865026567749794928495 := by
  unfold tailWord_4095315
  simp only [CollatzResearch.WordTrace]
  refine ⟨149368409158380653963111399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99578939438920435975407599 149368409158380653963111399)
  ·
    refine ⟨224052613737570980944667099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149368409158380653963111399 224052613737570980944667099)
    ·
      refine ⟨336078920606356471417000649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224052613737570980944667099 336078920606356471417000649)
      ·
        refine ⟨252059190454767353562750487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336078920606356471417000649 252059190454767353562750487)
        ·
          refine ⟨378088785682151030344125731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252059190454767353562750487 378088785682151030344125731)
          ·
            refine ⟨567133178523226545516188597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378088785682151030344125731 567133178523226545516188597)
            ·
              refine ⟨53168735486552488642142681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 567133178523226545516188597 53168735486552488642142681)
              ·
                refine ⟨39876551614914366481607011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53168735486552488642142681 39876551614914366481607011)
                ·
                  refine ⟨59814827422371549722410517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39876551614914366481607011 59814827422371549722410517)
                  ·
                    refine ⟨2803820035423666393237993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59814827422371549722410517 2803820035423666393237993)
                    ·
                      refine ⟨2102865026567749794928495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2803820035423666393237993 2102865026567749794928495)
                      ·
                        rfl

theorem cell23_4095315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 6, 2].length) (baseStart_4095315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095315 prefixEnd_4095315 := by exact prefixLift 4095315
  have htrace : WordTrace (prefixWord ++ tailWord_4095315) baseStart_4095315 baseEnd_4095315 := by
    simpa [prefixWord, tailWord_4095315, baseEnd_4095315] using wordTrace_append hprefix tailTrace_4095315
  have hstable : (prefixWord ++ tailWord_4095315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095315).length < 2 ^ (prefixWord ++ tailWord_4095315).sum := by decide
  have hdescent : baseEnd_4095315 < baseStart_4095315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095332 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 2, 4, 2]
def baseStart_4095332 : Nat := 118140960795 + 4095332 * 2 ^ 59
def prefixEnd_4095332 : Nat := 4983230072969 + 3 ^ 40 * 4095332 * 2
def baseEnd_4095332 : Nat := 2102873755738876228415917

theorem tailTrace_4095332 : CollatzResearch.WordTrace tailWord_4095332 prefixEnd_4095332 2102873755738876228415917 := by
  unfold tailWord_4095332
  simp only [CollatzResearch.WordTrace]
  refine ⟨74684514599659532933240125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99579352799546043910986833 74684514599659532933240125)
  ·
    refine ⟨28006692974872324849965047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74684514599659532933240125 28006692974872324849965047)
    ·
      refine ⟨42010039462308487274947571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28006692974872324849965047 42010039462308487274947571)
      ·
        refine ⟨63015059193462730912421357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42010039462308487274947571 63015059193462730912421357)
        ·
          refine ⟨23630647197548524092158009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63015059193462730912421357 23630647197548524092158009)
          ·
            refine ⟨17722985398161393069118507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23630647197548524092158009 17722985398161393069118507)
            ·
              refine ⟨26584478097242089603677761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17722985398161393069118507 26584478097242089603677761)
              ·
                refine ⟨19938358572931567202758321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26584478097242089603677761 19938358572931567202758321)
                ·
                  refine ⟨14953768929698675402068741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19938358572931567202758321 14953768929698675402068741)
                  ·
                    refine ⟨2803831674318501637887889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14953768929698675402068741 2803831674318501637887889)
                    ·
                      refine ⟨2102873755738876228415917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2803831674318501637887889 2102873755738876228415917)
                      ·
                        rfl

theorem cell23_4095332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_4095332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095332 prefixEnd_4095332 := by exact prefixLift 4095332
  have htrace : WordTrace (prefixWord ++ tailWord_4095332) baseStart_4095332 baseEnd_4095332 := by
    simpa [prefixWord, tailWord_4095332, baseEnd_4095332] using wordTrace_append hprefix tailTrace_4095332
  have hstable : (prefixWord ++ tailWord_4095332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095332).length < 2 ^ (prefixWord ++ tailWord_4095332).sum := by decide
  have hdescent : baseEnd_4095332 < baseStart_4095332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095415 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 1, 6]
def baseStart_4095415 : Nat := 118140960795 + 4095415 * 2 ^ 59
def prefixEnd_4095415 : Nat := 4983230072969 + 3 ^ 40 * 4095415 * 2
def baseEnd_4095415 : Nat := 700972124877733134559345

theorem tailTrace_4095415 : CollatzResearch.WordTrace tailWord_4095415 prefixEnd_4095415 700972124877733134559345 := by
  unfold tailWord_4095415
  simp only [CollatzResearch.WordTrace]
  refine ⟨149372056458018371041751699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99581370972012247361167799 149372056458018371041751699)
  ·
    refine ⟨224058084687027556562627549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149372056458018371041751699 224058084687027556562627549)
    ·
      refine ⟨84021781757635333710985331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224058084687027556562627549 84021781757635333710985331)
      ·
        refine ⟨126032672636453000566477997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84021781757635333710985331 126032672636453000566477997)
        ·
          refine ⟨47262252238669875212429249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126032672636453000566477997 47262252238669875212429249)
          ·
            refine ⟨35446689179002406409321937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47262252238669875212429249 35446689179002406409321937)
            ·
              refine ⟨26585016884251804806991453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35446689179002406409321937 26585016884251804806991453)
              ·
                refine ⟨9969381331594426802621795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26585016884251804806991453 9969381331594426802621795)
                ·
                  refine ⟨14954071997391640203932693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9969381331594426802621795 14954071997391640203932693)
                  ·
                    refine ⟨700972124877733134559345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14954071997391640203932693 700972124877733134559345)
                    ·
                      rfl

theorem cell23_4095415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_4095415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095415 prefixEnd_4095415 := by exact prefixLift 4095415
  have htrace : WordTrace (prefixWord ++ tailWord_4095415) baseStart_4095415 baseEnd_4095415 := by
    simpa [prefixWord, tailWord_4095415, baseEnd_4095415] using wordTrace_append hprefix tailTrace_4095415
  have hstable : (prefixWord ++ tailWord_4095415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095415).length < 2 ^ (prefixWord ++ tailWord_4095415).sum := by decide
  have hdescent : baseEnd_4095415 < baseStart_4095415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095435 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 4]
def baseStart_4095435 : Nat := 118140960795 + 4095435 * 2 ^ 59
def prefixEnd_4095435 : Nat := 4983230072969 + 3 ^ 40 * 4095435 * 2
def baseEnd_4095435 : Nat := 2102926644246289325427943

theorem tailTrace_4095435 : CollatzResearch.WordTrace tailWord_4095435 prefixEnd_4095435 2102926644246289325427943 := by
  unfold tailWord_4095435
  simp only [CollatzResearch.WordTrace]
  refine ⟨149372785917945914457479759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99581857278630609638319839 149372785917945914457479759)
  ·
    refine ⟨224059178876918871686219639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149372785917945914457479759 224059178876918871686219639)
    ·
      refine ⟨336088768315378307529329459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224059178876918871686219639 336088768315378307529329459)
      ·
        refine ⟨504133152473067461293994189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336088768315378307529329459 504133152473067461293994189)
        ·
          refine ⟨189049932177400297985247821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504133152473067461293994189 189049932177400297985247821)
          ·
            refine ⟨70893724566525111744467933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189049932177400297985247821 70893724566525111744467933)
            ·
              refine ⟨26585146712446916904175475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70893724566525111744467933 26585146712446916904175475)
              ·
                refine ⟨39877720068670375356263213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26585146712446916904175475 39877720068670375356263213)
                ·
                  refine ⟨14954145025751390758598705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39877720068670375356263213 14954145025751390758598705)
                  ·
                    refine ⟨11215608769313543068949029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14954145025751390758598705 11215608769313543068949029)
                    ·
                      refine ⟨2102926644246289325427943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11215608769313543068949029 2102926644246289325427943)
                      ·
                        rfl

theorem cell23_4095435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 4].length) (baseStart_4095435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095435 prefixEnd_4095435 := by exact prefixLift 4095435
  have htrace : WordTrace (prefixWord ++ tailWord_4095435) baseStart_4095435 baseEnd_4095435 := by
    simpa [prefixWord, tailWord_4095435, baseEnd_4095435] using wordTrace_append hprefix tailTrace_4095435
  have hstable : (prefixWord ++ tailWord_4095435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095435).length < 2 ^ (prefixWord ++ tailWord_4095435).sum := by decide
  have hdescent : baseEnd_4095435 < baseStart_4095435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095449 : List Nat := [1, 2, 1, 2, 4, 3, 2, 2, 2, 4]
def baseStart_4095449 : Nat := 118140960795 + 4095449 * 2 ^ 59
def prefixEnd_4095449 : Nat := 4983230072969 + 3 ^ 40 * 4095449 * 2
def baseEnd_4095449 : Nat := 700977944325150756884293

theorem tailTrace_4095449 : CollatzResearch.WordTrace tailWord_4095449 prefixEnd_4095449 700977944325150756884293 := by
  unfold tailWord_4095449
  simp only [CollatzResearch.WordTrace]
  refine ⟨149373296539895194848489401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99582197693263463232326267 149373296539895194848489401)
  ·
    refine ⟨112029972404921396136367051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149373296539895194848489401 112029972404921396136367051)
    ·
      refine ⟨168044958607382094204550577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112029972404921396136367051 168044958607382094204550577)
      ·
        refine ⟨126033718955536570653412933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168044958607382094204550577 126033718955536570653412933)
        ·
          refine ⟨23631322304163106997514925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126033718955536570653412933 23631322304163106997514925)
          ·
            refine ⟨8861745864061165124068097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23631322304163106997514925 8861745864061165124068097)
            ·
              refine ⟨6646309398045873843051073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8861745864061165124068097 6646309398045873843051073)
              ·
                refine ⟨4984732048534405382288305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6646309398045873843051073 4984732048534405382288305)
                ·
                  refine ⟨3738549036400804036716229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4984732048534405382288305 3738549036400804036716229)
                  ·
                    refine ⟨700977944325150756884293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3738549036400804036716229 700977944325150756884293)
                    ·
                      rfl

theorem cell23_4095449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 4].length) (baseStart_4095449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095449 prefixEnd_4095449 := by exact prefixLift 4095449
  have htrace : WordTrace (prefixWord ++ tailWord_4095449) baseStart_4095449 baseEnd_4095449 := by
    simpa [prefixWord, tailWord_4095449, baseEnd_4095449] using wordTrace_append hprefix tailTrace_4095449
  have hstable : (prefixWord ++ tailWord_4095449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095449).length < 2 ^ (prefixWord ++ tailWord_4095449).sum := by decide
  have hdescent : baseEnd_4095449 < baseStart_4095449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095472 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 3]
def baseStart_4095472 : Nat := 118140960795 + 4095472 * 2 ^ 59
def prefixEnd_4095472 : Nat := 4983230072969 + 3 ^ 40 * 4095472 * 2
def baseEnd_4095472 : Nat := 2102945643030505680665273

theorem tailTrace_4095472 : CollatzResearch.WordTrace tailWord_4095472 prefixEnd_4095472 2102945643030505680665273 := by
  unfold tailWord_4095472
  simp only [CollatzResearch.WordTrace]
  refine ⟨74687067709405934888288335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99582756945874579851051113 74687067709405934888288335)
  ·
    refine ⟨112030601564108902332432503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74687067709405934888288335 112030601564108902332432503)
    ·
      refine ⟨168045902346163353498648755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112030601564108902332432503 168045902346163353498648755)
      ·
        refine ⟨252068853519245030247973133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168045902346163353498648755 252068853519245030247973133)
        ·
          refine ⟨94525820069716886342989925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252068853519245030247973133 94525820069716886342989925)
          ·
            refine ⟨17723591263071916189310611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94525820069716886342989925 17723591263071916189310611)
            ·
              refine ⟨26585386894607874283965917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17723591263071916189310611 26585386894607874283965917)
              ·
                refine ⟨9969520085477952856487219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26585386894607874283965917 9969520085477952856487219)
                ·
                  refine ⟨14954280128216929284730829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9969520085477952856487219 14954280128216929284730829)
                  ·
                    refine ⟨5607855048081348481774061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14954280128216929284730829 5607855048081348481774061)
                    ·
                      refine ⟨2102945643030505680665273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5607855048081348481774061 2102945643030505680665273)
                      ·
                        rfl

theorem cell23_4095472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 3].length) (baseStart_4095472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095472 prefixEnd_4095472 := by exact prefixLift 4095472
  have htrace : WordTrace (prefixWord ++ tailWord_4095472) baseStart_4095472 baseEnd_4095472 := by
    simpa [prefixWord, tailWord_4095472, baseEnd_4095472] using wordTrace_append hprefix tailTrace_4095472
  have hstable : (prefixWord ++ tailWord_4095472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095472).length < 2 ^ (prefixWord ++ tailWord_4095472).sum := by decide
  have hdescent : baseEnd_4095472 < baseStart_4095472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095490 : List Nat := [3, 4, 1, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_4095490 : Nat := 118140960795 + 4095490 * 2 ^ 59
def prefixEnd_4095490 : Nat := 4983230072969 + 3 ^ 40 * 4095490 * 2
def baseEnd_4095490 : Nat := 2102954885682286610240191

theorem tailTrace_4095490 : CollatzResearch.WordTrace tailWord_4095490 prefixEnd_4095490 2102954885682286610240191 := by
  unfold tailWord_4095490
  simp only [CollatzResearch.WordTrace]
  refine ⟨37343697983186664712682981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99583194621831105900487949 37343697983186664712682981)
  ·
    refine ⟨7001943371847499633628059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37343697983186664712682981 7001943371847499633628059)
    ·
      refine ⟨10502915057771249450442089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7001943371847499633628059 10502915057771249450442089)
      ·
        refine ⟨7877186293328437087831567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10502915057771249450442089 7877186293328437087831567)
        ·
          refine ⟨11815779439992655631747351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7877186293328437087831567 11815779439992655631747351)
          ·
            refine ⟨17723669159988983447621027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11815779439992655631747351 17723669159988983447621027)
            ·
              refine ⟨26585503739983475171431541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17723669159988983447621027 26585503739983475171431541)
              ·
                refine ⟨2492390975623450797321707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26585503739983475171431541 2492390975623450797321707)
                ·
                  refine ⟨3738586463435176195982561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492390975623450797321707 3738586463435176195982561)
                  ·
                    refine ⟨2803939847576382146986921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3738586463435176195982561 2803939847576382146986921)
                    ·
                      refine ⟨2102954885682286610240191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2803939847576382146986921 2102954885682286610240191)
                      ·
                        rfl

theorem cell23_4095490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_4095490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095490 prefixEnd_4095490 := by exact prefixLift 4095490
  have htrace : WordTrace (prefixWord ++ tailWord_4095490) baseStart_4095490 baseEnd_4095490 := by
    simpa [prefixWord, tailWord_4095490, baseEnd_4095490] using wordTrace_append hprefix tailTrace_4095490
  have hstable : (prefixWord ++ tailWord_4095490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095490).length < 2 ^ (prefixWord ++ tailWord_4095490).sum := by decide
  have hdescent : baseEnd_4095490 < baseStart_4095490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095505 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 4, 6]
def baseStart_4095505 : Nat := 118140960795 + 4095505 * 2 ^ 59
def prefixEnd_4095505 : Nat := 4983230072969 + 3 ^ 40 * 4095505 * 2
def baseEnd_4095505 : Nat := 700987529297368017184207

theorem tailTrace_4095505 : CollatzResearch.WordTrace tailWord_4095505 prefixEnd_4095505 700987529297368017184207 := by
  unfold tailWord_4095505
  simp only [CollatzResearch.WordTrace]
  refine ⟨149375339027692316412527969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99583559351794877608351979 149375339027692316412527969)
  ·
    refine ⟨112031504270769237309395977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149375339027692316412527969 112031504270769237309395977)
    ·
      refine ⟨84023628203076927982046983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112031504270769237309395977 84023628203076927982046983)
      ·
        refine ⟨126035442304615391973070475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84023628203076927982046983 126035442304615391973070475)
        ·
          refine ⟨189053163456923087959605713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126035442304615391973070475 189053163456923087959605713)
          ·
            refine ⟨141789872592692315969704285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189053163456923087959605713 141789872592692315969704285)
            ·
              refine ⟨53171202222259618488639107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141789872592692315969704285 53171202222259618488639107)
              ·
                refine ⟨79756803333389427732958661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53171202222259618488639107 79756803333389427732958661)
                ·
                  refine ⟨14954400625010517699929749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79756803333389427732958661 14954400625010517699929749)
                  ·
                    refine ⟨700987529297368017184207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14954400625010517699929749 700987529297368017184207)
                    ·
                      rfl

theorem cell23_4095505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_4095505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095505 prefixEnd_4095505 := by exact prefixLift 4095505
  have htrace : WordTrace (prefixWord ++ tailWord_4095505) baseStart_4095505 baseEnd_4095505 := by
    simpa [prefixWord, tailWord_4095505, baseEnd_4095505] using wordTrace_append hprefix tailTrace_4095505
  have hstable : (prefixWord ++ tailWord_4095505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095505).length < 2 ^ (prefixWord ++ tailWord_4095505).sum := by decide
  have hdescent : baseEnd_4095505 < baseStart_4095505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095522 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_4095522 : Nat := 118140960795 + 4095522 * 2 ^ 59
def prefixEnd_4095522 : Nat := 4983230072969 + 3 ^ 40 * 4095522 * 2
def baseEnd_4095522 : Nat := 700990439021076828346681

theorem tailTrace_4095522 : CollatzResearch.WordTrace tailWord_4095522 prefixEnd_4095522 700990439021076828346681 := by
  unfold tailWord_4095522
  simp only [CollatzResearch.WordTrace]
  refine ⟨37343989767157682078974205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99583972712420485543931213 37343989767157682078974205)
  ·
    refine ⟨14003996162684130779615327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37343989767157682078974205 14003996162684130779615327)
    ·
      refine ⟨21005994244026196169422991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14003996162684130779615327 21005994244026196169422991)
      ·
        refine ⟨31508991366039294254134487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21005994244026196169422991 31508991366039294254134487)
        ·
          refine ⟨47263487049058941381201731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31508991366039294254134487 47263487049058941381201731)
          ·
            refine ⟨70895230573588412071802597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47263487049058941381201731 70895230573588412071802597)
            ·
              refine ⟨13292855732547827263462987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70895230573588412071802597 13292855732547827263462987)
              ·
                refine ⟨19939283598821740895194481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13292855732547827263462987 19939283598821740895194481)
                ·
                  refine ⟨14954462699116305671395861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19939283598821740895194481 14954462699116305671395861)
                  ·
                    refine ⟨700990439021076828346681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14954462699116305671395861 700990439021076828346681)
                    ·
                      rfl

theorem cell23_4095522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_4095522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095522 prefixEnd_4095522 := by exact prefixLift 4095522
  have htrace : WordTrace (prefixWord ++ tailWord_4095522) baseStart_4095522 baseEnd_4095522 := by
    simpa [prefixWord, tailWord_4095522, baseEnd_4095522] using wordTrace_append hprefix tailTrace_4095522
  have hstable : (prefixWord ++ tailWord_4095522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095522).length < 2 ^ (prefixWord ++ tailWord_4095522).sum := by decide
  have hdescent : baseEnd_4095522 < baseStart_4095522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095523 : List Nat := [1, 1, 1, 4, 5, 1, 3, 1, 2, 1, 3]
def baseStart_4095523 : Nat := 118140960795 + 4095523 * 2 ^ 59
def prefixEnd_4095523 : Nat := 4983230072969 + 3 ^ 40 * 4095523 * 2
def baseEnd_4095523 : Nat := 2102971830543884981127539

theorem tailTrace_4095523 : CollatzResearch.WordTrace tailWord_4095523 prefixEnd_4095523 2102971830543884981127539 := by
  unfold tailWord_4095523
  simp only [CollatzResearch.WordTrace]
  refine ⟨149375995541627105486683223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99583997027751403657788815 149375995541627105486683223)
  ·
    refine ⟨224063993312440658230024835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149375995541627105486683223 224063993312440658230024835)
    ·
      refine ⟨336095989968660987345037253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224063993312440658230024835 336095989968660987345037253)
      ·
        refine ⟨63017998119123935127194485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336095989968660987345037253 63017998119123935127194485)
        ·
          refine ⟨5907937323667868918174483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63017998119123935127194485 5907937323667868918174483)
          ·
            refine ⟨8861905985501803377261725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5907937323667868918174483 8861905985501803377261725)
            ·
              refine ⟨3323214744563176266473147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8861905985501803377261725 3323214744563176266473147)
              ·
                refine ⟨4984822116844764399709721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3323214744563176266473147 4984822116844764399709721)
                ·
                  refine ⟨3738616587633573299782291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4984822116844764399709721 3738616587633573299782291)
                  ·
                    refine ⟨5607924881450359949673437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3738616587633573299782291 5607924881450359949673437)
                    ·
                      refine ⟨2102971830543884981127539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5607924881450359949673437 2102971830543884981127539)
                      ·
                        rfl

theorem cell23_4095523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_4095523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095523 prefixEnd_4095523 := by exact prefixLift 4095523
  have htrace : WordTrace (prefixWord ++ tailWord_4095523) baseStart_4095523 baseEnd_4095523 := by
    simpa [prefixWord, tailWord_4095523, baseEnd_4095523] using wordTrace_append hprefix tailTrace_4095523
  have hstable : (prefixWord ++ tailWord_4095523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095523).length < 2 ^ (prefixWord ++ tailWord_4095523).sum := by decide
  have hdescent : baseEnd_4095523 < baseStart_4095523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095549 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 2, 1, 5]
def baseStart_4095549 : Nat := 118140960795 + 4095549 * 2 ^ 59
def prefixEnd_4095549 : Nat := 4983230072969 + 3 ^ 40 * 4095549 * 2
def baseEnd_4095549 : Nat := 2102985181040901879402419

theorem tailTrace_4095549 : CollatzResearch.WordTrace tailWord_4095549 prefixEnd_4095549 2102985181040901879402419 := by
  unfold tailWord_4095549
  simp only [CollatzResearch.WordTrace]
  refine ⟨149376943839532911927129701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99584629226355274618086467 149376943839532911927129701)
  ·
    refine ⟨28008176969912420986336819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149376943839532911927129701 28008176969912420986336819)
    ·
      refine ⟨42012265454868631479505229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28008176969912420986336819 42012265454868631479505229)
      ·
        refine ⟨15754599545575736804814461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42012265454868631479505229 15754599545575736804814461)
        ·
          refine ⟨5907974829590901301805423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15754599545575736804814461 5907974829590901301805423)
          ·
            refine ⟨8861962244386351952708135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5907974829590901301805423 8861962244386351952708135)
            ·
              refine ⟨13292943366579527929062203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8861962244386351952708135 13292943366579527929062203)
              ·
                refine ⟨19939415049869291893593305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13292943366579527929062203 19939415049869291893593305)
                ·
                  refine ⟨14954561287401968920194979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19939415049869291893593305 14954561287401968920194979)
                  ·
                    refine ⟨22431841931102953380292469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14954561287401968920194979 22431841931102953380292469)
                    ·
                      refine ⟨2102985181040901879402419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22431841931102953380292469 2102985181040901879402419)
                      ·
                        rfl

theorem cell23_4095549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_4095549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095549 prefixEnd_4095549 := by exact prefixLift 4095549
  have htrace : WordTrace (prefixWord ++ tailWord_4095549) baseStart_4095549 baseEnd_4095549 := by
    simpa [prefixWord, tailWord_4095549, baseEnd_4095549] using wordTrace_append hprefix tailTrace_4095549
  have hstable : (prefixWord ++ tailWord_4095549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095549).length < 2 ^ (prefixWord ++ tailWord_4095549).sum := by decide
  have hdescent : baseEnd_4095549 < baseStart_4095549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095555 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 6]
def baseStart_4095555 : Nat := 118140960795 + 4095555 * 2 ^ 59
def prefixEnd_4095555 : Nat := 4983230072969 + 3 ^ 40 * 4095555 * 2
def baseEnd_4095555 : Nat := 2102988261924828855927391

theorem tailTrace_4095555 : CollatzResearch.WordTrace tailWord_4095555 prefixEnd_4095555 2102988261924828855927391 := by
  unfold tailWord_4095555
  simp only [CollatzResearch.WordTrace]
  refine ⟨149377162677511174951848119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99584775118340783301232079 149377162677511174951848119)
  ·
    refine ⟨224065744016266762427772179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149377162677511174951848119 224065744016266762427772179)
    ·
      refine ⟨336098616024400143641658269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224065744016266762427772179 336098616024400143641658269)
      ·
        refine ⟨126036981009150053865621851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336098616024400143641658269 126036981009150053865621851)
        ·
          refine ⟨189055471513725080798432777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126036981009150053865621851 189055471513725080798432777)
          ·
            refine ⟨141791603635293810598824583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189055471513725080798432777 141791603635293810598824583)
            ·
              refine ⟨212687405452940715898236875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141791603635293810598824583 212687405452940715898236875)
              ·
                refine ⟨319031108179411073847355313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212687405452940715898236875 319031108179411073847355313)
                ·
                  refine ⟨239273331134558305385516485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319031108179411073847355313 239273331134558305385516485)
                  ·
                    refine ⟨44863749587729682259784341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 239273331134558305385516485 44863749587729682259784341)
                    ·
                      refine ⟨2102988261924828855927391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44863749587729682259784341 2102988261924828855927391)
                      ·
                        rfl

theorem cell23_4095555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_4095555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095555 prefixEnd_4095555 := by exact prefixLift 4095555
  have htrace : WordTrace (prefixWord ++ tailWord_4095555) baseStart_4095555 baseEnd_4095555 := by
    simpa [prefixWord, tailWord_4095555, baseEnd_4095555] using wordTrace_append hprefix tailTrace_4095555
  have hstable : (prefixWord ++ tailWord_4095555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095555).length < 2 ^ (prefixWord ++ tailWord_4095555).sum := by decide
  have hdescent : baseEnd_4095555 < baseStart_4095555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095574 : List Nat := [5, 2, 2, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_4095574 : Nat := 118140960795 + 4095574 * 2 ^ 59
def prefixEnd_4095574 : Nat := 4983230072969 + 3 ^ 40 * 4095574 * 2
def baseEnd_4095574 : Nat := 2102998018057264281589805

theorem tailTrace_4095574 : CollatzResearch.WordTrace tailWord_4095574 prefixEnd_4095574 2102998018057264281589805 := by
  unfold tailWord_4095574
  simp only [CollatzResearch.WordTrace]
  refine ⟨9336115979027646324799361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99585237109628227464526517 9336115979027646324799361)
  ·
    refine ⟨7002086984270734743599521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9336115979027646324799361 7002086984270734743599521)
    ·
      refine ⟨5251565238203051057699641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7002086984270734743599521 5251565238203051057699641)
      ·
        refine ⟨3938673928652288293274731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5251565238203051057699641 3938673928652288293274731)
        ·
          refine ⟨5908010892978432439912097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3938673928652288293274731 5908010892978432439912097)
          ·
            refine ⟨4431008169733824329934073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5908010892978432439912097 4431008169733824329934073)
            ·
              refine ⟨3323256127300368247450555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4431008169733824329934073 3323256127300368247450555)
              ·
                refine ⟨4984884190950552371175833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3323256127300368247450555 4984884190950552371175833)
                ·
                  refine ⟨3738663143212914278381875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4984884190950552371175833 3738663143212914278381875)
                  ·
                    refine ⟨5607994714819371417572813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3738663143212914278381875 5607994714819371417572813)
                    ·
                      refine ⟨2102998018057264281589805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5607994714819371417572813 2102998018057264281589805)
                      ·
                        rfl

theorem cell23_4095574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_4095574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095574 prefixEnd_4095574 := by exact prefixLift 4095574
  have htrace : WordTrace (prefixWord ++ tailWord_4095574) baseStart_4095574 baseEnd_4095574 := by
    simpa [prefixWord, tailWord_4095574, baseEnd_4095574] using wordTrace_append hprefix tailTrace_4095574
  have hstable : (prefixWord ++ tailWord_4095574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095574).length < 2 ^ (prefixWord ++ tailWord_4095574).sum := by decide
  have hdescent : baseEnd_4095574 < baseStart_4095574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095580 : List Nat := [2, 2, 4, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_4095580 : Nat := 118140960795 + 4095580 * 2 ^ 59
def prefixEnd_4095580 : Nat := 4983230072969 + 3 ^ 40 * 4095580 * 2
def baseEnd_4095580 : Nat := 2103001098941191258114777

theorem tailTrace_4095580 : CollatzResearch.WordTrace tailWord_4095580 prefixEnd_4095580 2103001098941191258114777 := by
  unfold tailWord_4095580
  simp only [CollatzResearch.WordTrace]
  refine ⟨74689037251210302110754097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99585383001613736147672129 74689037251210302110754097)
  ·
    refine ⟨56016777938407726583065573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74689037251210302110754097 56016777938407726583065573)
    ·
      refine ⟨10503145863451448734324795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56016777938407726583065573 10503145863451448734324795)
      ·
        refine ⟨15754718795177173101487193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10503145863451448734324795 15754718795177173101487193)
        ·
          refine ⟨11816039096382879826115395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15754718795177173101487193 11816039096382879826115395)
          ·
            refine ⟨17724058644574319739173093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11816039096382879826115395 17724058644574319739173093)
            ·
              refine ⟨3323260995857684951094955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17724058644574319739173093 3323260995857684951094955)
              ·
                refine ⟨4984891493786527426642433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3323260995857684951094955 4984891493786527426642433)
                ·
                  refine ⟨3738668620339895569981825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4984891493786527426642433 3738668620339895569981825)
                  ·
                    refine ⟨2804001465254921677486369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3738668620339895569981825 2804001465254921677486369)
                    ·
                      refine ⟨2103001098941191258114777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804001465254921677486369 2103001098941191258114777)
                      ·
                        rfl

theorem cell23_4095580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_4095580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095580 prefixEnd_4095580 := by exact prefixLift 4095580
  have htrace : WordTrace (prefixWord ++ tailWord_4095580) baseStart_4095580 baseEnd_4095580 := by
    simpa [prefixWord, tailWord_4095580, baseEnd_4095580] using wordTrace_append hprefix tailTrace_4095580
  have hstable : (prefixWord ++ tailWord_4095580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095580).length < 2 ^ (prefixWord ++ tailWord_4095580).sum := by decide
  have hdescent : baseEnd_4095580 < baseStart_4095580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095619 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 2, 4, 2]
def baseStart_4095619 : Nat := 118140960795 + 4095619 * 2 ^ 59
def prefixEnd_4095619 : Nat := 4983230072969 + 3 ^ 40 * 4095619 * 2
def baseEnd_4095619 : Nat := 2103021124686716605527097

theorem tailTrace_4095619 : CollatzResearch.WordTrace tailWord_4095619 prefixEnd_4095619 2103021124686716605527097 := by
  unfold tailWord_4095619
  simp only [CollatzResearch.WordTrace]
  refine ⟨149379496949279313882177911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99586331299519542588118607 149379496949279313882177911)
  ·
    refine ⟨224069245423918970823266867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149379496949279313882177911 224069245423918970823266867)
    ·
      refine ⟨336103868135878456234900301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224069245423918970823266867 336103868135878456234900301)
      ·
        refine ⟨126038950550954421088087613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336103868135878456234900301 126038950550954421088087613)
        ·
          refine ⟨47264606456607907908032855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126038950550954421088087613 47264606456607907908032855)
          ·
            refine ⟨70896909684911861862049283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47264606456607907908032855 70896909684911861862049283)
            ·
              refine ⟨106345364527367792793073925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70896909684911861862049283 106345364527367792793073925)
              ·
                refine ⟨19939755848881461148701361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106345364527367792793073925 19939755848881461148701361)
                ·
                  refine ⟨14954816886661095861526021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19939755848881461148701361 14954816886661095861526021)
                  ·
                    refine ⟨2804028166248955474036129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14954816886661095861526021 2804028166248955474036129)
                    ·
                      refine ⟨2103021124686716605527097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804028166248955474036129 2103021124686716605527097)
                      ·
                        rfl

theorem cell23_4095619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 4, 2].length) (baseStart_4095619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095619 prefixEnd_4095619 := by exact prefixLift 4095619
  have htrace : WordTrace (prefixWord ++ tailWord_4095619) baseStart_4095619 baseEnd_4095619 := by
    simpa [prefixWord, tailWord_4095619, baseEnd_4095619] using wordTrace_append hprefix tailTrace_4095619
  have hstable : (prefixWord ++ tailWord_4095619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095619).length < 2 ^ (prefixWord ++ tailWord_4095619).sum := by decide
  have hdescent : baseEnd_4095619 < baseStart_4095619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095620 : List Nat := [2, 3, 2, 1, 5, 1, 2, 2, 5]
def baseStart_4095620 : Nat := 118140960795 + 4095620 * 2 ^ 59
def prefixEnd_4095620 : Nat := 4983230072969 + 3 ^ 40 * 4095620 * 2
def baseEnd_4095620 : Nat := 233669070907485677957177

theorem tailTrace_4095620 : CollatzResearch.WordTrace tailWord_4095620 prefixEnd_4095620 233669070907485677957177 := by
  unfold tailWord_4095620
  simp only [CollatzResearch.WordTrace]
  refine ⟨74689766711137845526482157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99586355614850460701976209 74689766711137845526482157)
  ·
    refine ⟨28008662516676692072430809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74689766711137845526482157 28008662516676692072430809)
    ·
      refine ⟨21006496887507519054323107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28008662516676692072430809 21006496887507519054323107)
      ·
        refine ⟨31509745331261278581484661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21006496887507519054323107 31509745331261278581484661)
        ·
          refine ⟨2954038624805744867014187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31509745331261278581484661 2954038624805744867014187)
          ·
            refine ⟨4431057937208617300521281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954038624805744867014187 4431057937208617300521281)
            ·
              refine ⟨3323293452906462975390961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4431057937208617300521281 3323293452906462975390961)
              ·
                refine ⟨2492470089679847231543221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3323293452906462975390961 2492470089679847231543221)
                ·
                  refine ⟨233669070907485677957177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2492470089679847231543221 233669070907485677957177)
                  ·
                    rfl

theorem cell23_4095620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_4095620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095620 prefixEnd_4095620 := by exact prefixLift 4095620
  have htrace : WordTrace (prefixWord ++ tailWord_4095620) baseStart_4095620 baseEnd_4095620 := by
    simpa [prefixWord, tailWord_4095620, baseEnd_4095620] using wordTrace_append hprefix tailTrace_4095620
  have hstable : (prefixWord ++ tailWord_4095620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095620).length < 2 ^ (prefixWord ++ tailWord_4095620).sum := by decide
  have hdescent : baseEnd_4095620 < baseStart_4095620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095646 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_4095646 : Nat := 118140960795 + 4095646 * 2 ^ 59
def prefixEnd_4095646 : Nat := 4983230072969 + 3 ^ 40 * 4095646 * 2
def baseEnd_4095646 : Nat := 701011662888129333296491

theorem tailTrace_4095646 : CollatzResearch.WordTrace tailWord_4095646 prefixEnd_4095646 701011662888129333296491 := by
  unfold tailWord_4095646
  simp only [CollatzResearch.WordTrace]
  refine ⟨18672560215022687186676349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99586987813454331662273861 18672560215022687186676349)
  ·
    refine ⟨7002210080633507695003631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18672560215022687186676349 7002210080633507695003631)
    ·
      refine ⟨10503315120950261542505447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7002210080633507695003631 10503315120950261542505447)
      ·
        refine ⟨15754972681425392313758171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10503315120950261542505447 15754972681425392313758171)
        ·
          refine ⟨23632459022138088470637257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15754972681425392313758171 23632459022138088470637257)
          ·
            refine ⟨17724344266603566352977943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23632459022138088470637257 17724344266603566352977943)
            ·
              refine ⟨26586516399905349529466915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17724344266603566352977943 26586516399905349529466915)
              ·
                refine ⟨39879774599858024294200373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26586516399905349529466915 39879774599858024294200373)
                ·
                  refine ⟨3738728868736689777581285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39879774599858024294200373 3738728868736689777581285)
                  ·
                    refine ⟨701011662888129333296491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3738728868736689777581285 701011662888129333296491)
                    ·
                      rfl

theorem cell23_4095646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_4095646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095646 prefixEnd_4095646 := by exact prefixLift 4095646
  have htrace : WordTrace (prefixWord ++ tailWord_4095646) baseStart_4095646 baseEnd_4095646 := by
    simpa [prefixWord, tailWord_4095646, baseEnd_4095646] using wordTrace_append hprefix tailTrace_4095646
  have hstable : (prefixWord ++ tailWord_4095646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095646).length < 2 ^ (prefixWord ++ tailWord_4095646).sum := by decide
  have hdescent : baseEnd_4095646 < baseStart_4095646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095650 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_4095650 : Nat := 118140960795 + 4095650 * 2 ^ 59
def prefixEnd_4095650 : Nat := 4983230072969 + 3 ^ 40 * 4095650 * 2
def baseEnd_4095650 : Nat := 701012347529001994746485

theorem tailTrace_4095650 : CollatzResearch.WordTrace tailWord_4095650 prefixEnd_4095650 701012347529001994746485 := by
  unfold tailWord_4095650
  simp only [CollatzResearch.WordTrace]
  refine ⟨37345156903041751544139101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99587085074778004117704269 37345156903041751544139101)
  ·
    refine ⟨14004433838640656829052163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37345156903041751544139101 14004433838640656829052163)
    ·
      refine ⟨21006650757960985243578245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14004433838640656829052163 21006650757960985243578245)
      ·
        refine ⟨3938747017117684733170921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21006650757960985243578245 3938747017117684733170921)
        ·
          refine ⟨2954060262838263549878191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3938747017117684733170921 2954060262838263549878191)
          ·
            refine ⟨4431090394257395324817287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954060262838263549878191 4431090394257395324817287)
            ·
              refine ⟨6646635591386092987225931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4431090394257395324817287 6646635591386092987225931)
              ·
                refine ⟨9969953387079139480838897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6646635591386092987225931 9969953387079139480838897)
                ·
                  refine ⟨7477465040309354610629173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9969953387079139480838897 7477465040309354610629173)
                  ·
                    refine ⟨701012347529001994746485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7477465040309354610629173 701012347529001994746485)
                    ·
                      rfl

theorem cell23_4095650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_4095650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095650 prefixEnd_4095650 := by exact prefixLift 4095650
  have htrace : WordTrace (prefixWord ++ tailWord_4095650) baseStart_4095650 baseEnd_4095650 := by
    simpa [prefixWord, tailWord_4095650, baseEnd_4095650] using wordTrace_append hprefix tailTrace_4095650
  have hstable : (prefixWord ++ tailWord_4095650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095650).length < 2 ^ (prefixWord ++ tailWord_4095650).sum := by decide
  have hdescent : baseEnd_4095650 < baseStart_4095650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095676 : List Nat := [2, 2, 2, 3, 1, 4, 1, 2, 6]
def baseStart_4095676 : Nat := 118140960795 + 4095676 * 2 ^ 59
def prefixEnd_4095676 : Nat := 4983230072969 + 3 ^ 40 * 4095676 * 2
def baseEnd_4095676 : Nat := 233672265898224764723815

theorem tailTrace_4095676 : CollatzResearch.WordTrace tailWord_4095676 prefixEnd_4095676 233672265898224764723815 := by
  unfold tailWord_4095676
  simp only [CollatzResearch.WordTrace]
  refine ⟨74690787955036406308501441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99587717273381875078001921 74690787955036406308501441)
  ·
    refine ⟨56018090966277304731376081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74690787955036406308501441 56018090966277304731376081)
    ·
      refine ⟨42013568224707978548532061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56018090966277304731376081 42013568224707978548532061)
      ·
        refine ⟨15755088084265491955699523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42013568224707978548532061 15755088084265491955699523)
        ·
          refine ⟨23632632126398237933549285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15755088084265491955699523 23632632126398237933549285)
          ·
            refine ⟨4431118523699669612540491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23632632126398237933549285 4431118523699669612540491)
            ·
              refine ⟨6646677785549504418810737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4431118523699669612540491 6646677785549504418810737)
              ·
                refine ⟨4985008339162128314108053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6646677785549504418810737 4985008339162128314108053)
                ·
                  refine ⟨233672265898224764723815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4985008339162128314108053 233672265898224764723815)
                  ·
                    rfl

theorem cell23_4095676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 6].length) (baseStart_4095676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095676 prefixEnd_4095676 := by exact prefixLift 4095676
  have htrace : WordTrace (prefixWord ++ tailWord_4095676) baseStart_4095676 baseEnd_4095676 := by
    simpa [prefixWord, tailWord_4095676, baseEnd_4095676] using wordTrace_append hprefix tailTrace_4095676
  have hstable : (prefixWord ++ tailWord_4095676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095676).length < 2 ^ (prefixWord ++ tailWord_4095676).sum := by decide
  have hdescent : baseEnd_4095676 < baseStart_4095676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095706 : List Nat := [3, 1, 1, 2, 2, 4, 2, 2, 1, 5]
def baseStart_4095706 : Nat := 118140960795 + 4095706 * 2 ^ 59
def prefixEnd_4095706 : Nat := 4983230072969 + 3 ^ 40 * 4095706 * 2
def baseEnd_4095706 : Nat := 701021932501219255046399

theorem tailTrace_4095706 : CollatzResearch.WordTrace tailWord_4095706 prefixEnd_4095706 701021932501219255046399 := by
  unfold tailWord_4095706
  simp only [CollatzResearch.WordTrace]
  refine ⟨37345667524991031935148743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99588446733309418493729981 37345667524991031935148743)
  ·
    refine ⟨56018501287486547902723115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37345667524991031935148743 56018501287486547902723115)
    ·
      refine ⟨84027751931229821854084673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56018501287486547902723115 84027751931229821854084673)
      ·
        refine ⟨63020813948422366390563505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84027751931229821854084673 63020813948422366390563505)
        ·
          refine ⟨47265610461316774792922629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63020813948422366390563505 47265610461316774792922629)
          ·
            refine ⟨8862301961496895273672993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47265610461316774792922629 8862301961496895273672993)
            ·
              refine ⟨6646726471122671455254745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8862301961496895273672993 6646726471122671455254745)
              ·
                refine ⟨4985044853342003591441059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6646726471122671455254745 4985044853342003591441059)
                ·
                  refine ⟨7477567280013005387161589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4985044853342003591441059 7477567280013005387161589)
                  ·
                    refine ⟨701021932501219255046399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7477567280013005387161589 701021932501219255046399)
                    ·
                      rfl

theorem cell23_4095706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_4095706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095706 prefixEnd_4095706 := by exact prefixLift 4095706
  have htrace : WordTrace (prefixWord ++ tailWord_4095706) baseStart_4095706 baseEnd_4095706 := by
    simpa [prefixWord, tailWord_4095706, baseEnd_4095706] using wordTrace_append hprefix tailTrace_4095706
  have hstable : (prefixWord ++ tailWord_4095706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095706).length < 2 ^ (prefixWord ++ tailWord_4095706).sum := by decide
  have hdescent : baseEnd_4095706 < baseStart_4095706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095720 : List Nat := [2, 1, 4, 1, 3, 1, 3, 3, 1, 1, 3]
def baseStart_4095720 : Nat := 118140960795 + 4095720 * 2 ^ 59
def prefixEnd_4095720 : Nat := 4983230072969 + 3 ^ 40 * 4095720 * 2
def baseEnd_4095720 : Nat := 2103072986232820710364133

theorem tailTrace_4095720 : CollatzResearch.WordTrace tailWord_4095720 prefixEnd_4095720 2103072986232820710364133 := by
  unfold tailWord_4095720
  simp only [CollatzResearch.WordTrace]
  refine ⟨74691590360956704065802307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99588787147942272087736409 74691590360956704065802307)
  ·
    refine ⟨112037385541435056098703461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74691590360956704065802307 112037385541435056098703461)
    ·
      refine ⟨21007009789019073018506899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112037385541435056098703461 21007009789019073018506899)
      ·
        refine ⟨31510514683528609527760349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21007009789019073018506899 31510514683528609527760349)
        ·
          refine ⟨11816443006323228572910131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31510514683528609527760349 11816443006323228572910131)
          ·
            refine ⟨17724664509484842859365197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11816443006323228572910131 17724664509484842859365197)
            ·
              refine ⟨6646749191056816072261949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17724664509484842859365197 6646749191056816072261949)
              ·
                refine ⟨2492530946646306027098231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6646749191056816072261949 2492530946646306027098231)
                ·
                  refine ⟨3738796419969459040647347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492530946646306027098231 3738796419969459040647347)
                  ·
                    refine ⟨5608194629954188560971021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3738796419969459040647347 5608194629954188560971021)
                    ·
                      refine ⟨2103072986232820710364133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5608194629954188560971021 2103072986232820710364133)
                      ·
                        rfl

theorem cell23_4095720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_4095720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095720 prefixEnd_4095720 := by exact prefixLift 4095720
  have htrace : WordTrace (prefixWord ++ tailWord_4095720) baseStart_4095720 baseEnd_4095720 := by
    simpa [prefixWord, tailWord_4095720, baseEnd_4095720] using wordTrace_append hprefix tailTrace_4095720
  have hstable : (prefixWord ++ tailWord_4095720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095720).length < 2 ^ (prefixWord ++ tailWord_4095720).sum := by decide
  have hdescent : baseEnd_4095720 < baseStart_4095720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095726 : List Nat := [4, 1, 2, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_4095726 : Nat := 118140960795 + 4095726 * 2 ^ 59
def prefixEnd_4095726 : Nat := 4983230072969 + 3 ^ 40 * 4095726 * 2
def baseEnd_4095726 : Nat := 2103076067116747686889105

theorem tailTrace_4095726 : CollatzResearch.WordTrace tailWord_4095726 prefixEnd_4095726 2103076067116747686889105 := by
  unfold tailWord_4095726
  simp only [CollatzResearch.WordTrace]
  refine ⟨18672924944986458894540379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99588933039927780770882021 18672924944986458894540379)
  ·
    refine ⟨28009387417479688341810569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18672924944986458894540379 28009387417479688341810569)
    ·
      refine ⟨21007040563109766256357927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28009387417479688341810569 21007040563109766256357927)
      ·
        refine ⟨31510560844664649384536891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21007040563109766256357927 31510560844664649384536891)
        ·
          refine ⟨47265841266996974076805337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31510560844664649384536891 47265841266996974076805337)
          ·
            refine ⟨35449380950247730557604003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47265841266996974076805337 35449380950247730557604003)
            ·
              refine ⟨53174071425371595836406005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35449380950247730557604003 53174071425371595836406005)
              ·
                refine ⟨4985069196128587109663063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53174071425371595836406005 4985069196128587109663063)
                ·
                  refine ⟨7477603794192880664494595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4985069196128587109663063 7477603794192880664494595)
                  ·
                    refine ⟨11216405691289320996741893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7477603794192880664494595 11216405691289320996741893)
                    ·
                      refine ⟨2103076067116747686889105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11216405691289320996741893 2103076067116747686889105)
                      ·
                        rfl

theorem cell23_4095726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_4095726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095726 prefixEnd_4095726 := by exact prefixLift 4095726
  have htrace : WordTrace (prefixWord ++ tailWord_4095726) baseStart_4095726 baseEnd_4095726 := by
    simpa [prefixWord, tailWord_4095726, baseEnd_4095726] using wordTrace_append hprefix tailTrace_4095726
  have hstable : (prefixWord ++ tailWord_4095726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095726).length < 2 ^ (prefixWord ++ tailWord_4095726).sum := by decide
  have hdescent : baseEnd_4095726 < baseStart_4095726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095729 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 1, 1, 5]
def baseStart_4095729 : Nat := 118140960795 + 4095729 * 2 ^ 59
def prefixEnd_4095729 : Nat := 4983230072969 + 3 ^ 40 * 4095729 * 2
def baseEnd_4095729 : Nat := 2103077607558711175151591

theorem tailTrace_4095729 : CollatzResearch.WordTrace tailWord_4095729 prefixEnd_4095729 2103077607558711175151591 := by
  unfold tailWord_4095729
  simp only [CollatzResearch.WordTrace]
  refine ⟨149383508978880802668682241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99589005985920535112454827 149383508978880802668682241)
  ·
    refine ⟨112037631734160602001511681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149383508978880802668682241 112037631734160602001511681)
    ·
      refine ⟨84028223800620451501133761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112037631734160602001511681 84028223800620451501133761)
      ·
        refine ⟨63021167850465338625850321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84028223800620451501133761 63021167850465338625850321)
        ·
          refine ⟨47265875887849003969387741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63021167850465338625850321 47265875887849003969387741)
          ·
            refine ⟨17724703457943376488520403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47265875887849003969387741 17724703457943376488520403)
            ·
              refine ⟨26587055186915064732780605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17724703457943376488520403 26587055186915064732780605)
              ·
                refine ⟨9970145695093149274792727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26587055186915064732780605 9970145695093149274792727)
                ·
                  refine ⟨14955218542639723912189091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9970145695093149274792727 14955218542639723912189091)
                  ·
                    refine ⟨22432827813959585868283637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14955218542639723912189091 22432827813959585868283637)
                    ·
                      refine ⟨2103077607558711175151591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22432827813959585868283637 2103077607558711175151591)
                      ·
                        rfl

theorem cell23_4095729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_4095729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095729 prefixEnd_4095729 := by exact prefixLift 4095729
  have htrace : WordTrace (prefixWord ++ tailWord_4095729) baseStart_4095729 baseEnd_4095729 := by
    simpa [prefixWord, tailWord_4095729, baseEnd_4095729] using wordTrace_append hprefix tailTrace_4095729
  have hstable : (prefixWord ++ tailWord_4095729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095729).length < 2 ^ (prefixWord ++ tailWord_4095729).sum := by decide
  have hdescent : baseEnd_4095729 < baseStart_4095729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095743 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 3, 2, 2]
def baseStart_4095743 : Nat := 118140960795 + 4095743 * 2 ^ 59
def prefixEnd_4095743 : Nat := 4983230072969 + 3 ^ 40 * 4095743 * 2
def baseEnd_4095743 : Nat := 2103084796287874120376527

theorem tailTrace_4095743 : CollatzResearch.WordTrace tailWord_4095743 prefixEnd_4095743 2103084796287874120376527 := by
  unfold tailWord_4095743
  simp only [CollatzResearch.WordTrace]
  refine ⟨149384019600830083059691883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99589346400553388706461255 149384019600830083059691883)
  ·
    refine ⟨224076029401245124589537825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149384019600830083059691883 224076029401245124589537825)
    ·
      refine ⟨168057022050933843442153369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224076029401245124589537825 168057022050933843442153369)
      ·
        refine ⟨126042766538200382581615027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168057022050933843442153369 126042766538200382581615027)
        ·
          refine ⟨189064149807300573872422541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126042766538200382581615027 189064149807300573872422541)
          ·
            refine ⟨70899056177737715202158453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189064149807300573872422541 70899056177737715202158453)
            ·
              refine ⟨6646786516662910800202355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70899056177737715202158453 6646786516662910800202355)
              ·
                refine ⟨9970179774994366200303533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6646786516662910800202355 9970179774994366200303533)
                ·
                  refine ⟨3738817415622887325113825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9970179774994366200303533 3738817415622887325113825)
                  ·
                    refine ⟨2804113061717165493835369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3738817415622887325113825 2804113061717165493835369)
                    ·
                      refine ⟨2103084796287874120376527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804113061717165493835369 2103084796287874120376527)
                      ·
                        rfl

theorem cell23_4095743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 2, 2].length) (baseStart_4095743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095743 prefixEnd_4095743 := by exact prefixLift 4095743
  have htrace : WordTrace (prefixWord ++ tailWord_4095743) baseStart_4095743 baseEnd_4095743 := by
    simpa [prefixWord, tailWord_4095743, baseEnd_4095743] using wordTrace_append hprefix tailTrace_4095743
  have hstable : (prefixWord ++ tailWord_4095743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095743).length < 2 ^ (prefixWord ++ tailWord_4095743).sum := by decide
  have hdescent : baseEnd_4095743 < baseStart_4095743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095746 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_4095746 : Nat := 118140960795 + 4095746 * 2 ^ 59
def prefixEnd_4095746 : Nat := 4983230072969 + 3 ^ 40 * 4095746 * 2
def baseEnd_4095746 : Nat := 2103086336729837608639013

theorem tailTrace_4095746 : CollatzResearch.WordTrace tailWord_4095746 prefixEnd_4095746 2103086336729837608639013 := by
  unfold tailWord_4095746
  simp only [CollatzResearch.WordTrace]
  refine ⟨37346032254954803643012773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99589419346546143048034061 37346032254954803643012773)
  ·
    refine ⟨7002381047804025683064895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37346032254954803643012773 7002381047804025683064895)
    ·
      refine ⟨10503571571706038524597343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7002381047804025683064895 10503571571706038524597343)
      ·
        refine ⟨15755357357559057786896015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10503571571706038524597343 15755357357559057786896015)
        ·
          refine ⟨23633036036338586680344023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15755357357559057786896015 23633036036338586680344023)
          ·
            refine ⟨35449554054507880020516035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23633036036338586680344023 35449554054507880020516035)
            ·
              refine ⟨53174331081761820030774053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35449554054507880020516035 53174331081761820030774053)
              ·
                refine ⟨9970187077830341255770135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53174331081761820030774053 9970187077830341255770135)
                ·
                  refine ⟨14955280616745511883655203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9970187077830341255770135 14955280616745511883655203)
                  ·
                    refine ⟨22432920925118267825482805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14955280616745511883655203 22432920925118267825482805)
                    ·
                      refine ⟨2103086336729837608639013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22432920925118267825482805 2103086336729837608639013)
                      ·
                        rfl

theorem cell23_4095746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_4095746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095746 prefixEnd_4095746 := by exact prefixLift 4095746
  have htrace : WordTrace (prefixWord ++ tailWord_4095746) baseStart_4095746 baseEnd_4095746 := by
    simpa [prefixWord, tailWord_4095746, baseEnd_4095746] using wordTrace_append hprefix tailTrace_4095746
  have hstable : (prefixWord ++ tailWord_4095746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095746).length < 2 ^ (prefixWord ++ tailWord_4095746).sum := by decide
  have hdescent : baseEnd_4095746 < baseStart_4095746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095757 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_4095757 : Nat := 118140960795 + 4095757 * 2 ^ 59
def prefixEnd_4095757 : Nat := 4983230072969 + 3 ^ 40 * 4095757 * 2
def baseEnd_4095757 : Nat := 701030661672345688533821

theorem tailTrace_4095757 : CollatzResearch.WordTrace tailWord_4095757 prefixEnd_4095757 701030661672345688533821 := by
  unfold tailWord_4095757
  simp only [CollatzResearch.WordTrace]
  refine ⟨149384530222779363450701525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99589686815186242300467683 149384530222779363450701525)
  ·
    refine ⟨3501199927096391330875817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 149384530222779363450701525 3501199927096391330875817)
    ·
      refine ⟨2625899945322293498156863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3501199927096391330875817 2625899945322293498156863)
      ·
        refine ⟨3938849917983440247235295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2625899945322293498156863 3938849917983440247235295)
        ·
          refine ⟨5908274876975160370852943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3938849917983440247235295 5908274876975160370852943)
          ·
            refine ⟨8862412315462740556279415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5908274876975160370852943 8862412315462740556279415)
            ·
              refine ⟨13293618473194110834419123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8862412315462740556279415 13293618473194110834419123)
              ·
                refine ⟨19940427709791166251628685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13293618473194110834419123 19940427709791166251628685)
                ·
                  refine ⟨7477660391171687344360757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19940427709791166251628685 7477660391171687344360757)
                  ·
                    refine ⟨701030661672345688533821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7477660391171687344360757 701030661672345688533821)
                    ·
                      rfl

theorem cell23_4095757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_4095757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095757 prefixEnd_4095757 := by exact prefixLift 4095757
  have htrace : WordTrace (prefixWord ++ tailWord_4095757) baseStart_4095757 baseEnd_4095757 := by
    simpa [prefixWord, tailWord_4095757, baseEnd_4095757] using wordTrace_append hprefix tailTrace_4095757
  have hstable : (prefixWord ++ tailWord_4095757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095757).length < 2 ^ (prefixWord ++ tailWord_4095757).sum := by decide
  have hdescent : baseEnd_4095757 < baseStart_4095757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095764 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_4095764 : Nat := 118140960795 + 4095764 * 2 ^ 59
def prefixEnd_4095764 : Nat := 4983230072969 + 3 ^ 40 * 4095764 * 2
def baseEnd_4095764 : Nat := 2103095579381618538213931

theorem tailTrace_4095764 : CollatzResearch.WordTrace tailWord_4095764 prefixEnd_4095764 2103095579381618538213931 := by
  unfold tailWord_4095764
  simp only [CollatzResearch.WordTrace]
  refine ⟨74692392766877001823103173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99589857022502669097470897 74692392766877001823103173)
  ·
    refine ⟨14004823643789437841831845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74692392766877001823103173 14004823643789437841831845)
    ·
      refine ⟨2625904433210519595343471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14004823643789437841831845 2625904433210519595343471)
      ·
        refine ⟨3938856649815779393015207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2625904433210519595343471 3938856649815779393015207)
        ·
          refine ⟨5908284974723669089522811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3938856649815779393015207 5908284974723669089522811)
          ·
            refine ⟨8862427462085503634284217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5908284974723669089522811 8862427462085503634284217)
            ·
              refine ⟨6646820596564127725713163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8862427462085503634284217 6646820596564127725713163)
              ·
                refine ⟨9970230894846191588569745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6646820596564127725713163 9970230894846191588569745)
                ·
                  refine ⟨7477673171134643691427309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9970230894846191588569745 7477673171134643691427309)
                  ·
                    refine ⟨2804127439175491384285241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7477673171134643691427309 2804127439175491384285241)
                    ·
                      refine ⟨2103095579381618538213931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804127439175491384285241 2103095579381618538213931)
                      ·
                        rfl

theorem cell23_4095764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_4095764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095764 prefixEnd_4095764 := by exact prefixLift 4095764
  have htrace : WordTrace (prefixWord ++ tailWord_4095764) baseStart_4095764 baseEnd_4095764 := by
    simpa [prefixWord, tailWord_4095764, baseEnd_4095764] using wordTrace_append hprefix tailTrace_4095764
  have hstable : (prefixWord ++ tailWord_4095764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095764).length < 2 ^ (prefixWord ++ tailWord_4095764).sum := by decide
  have hdescent : baseEnd_4095764 < baseStart_4095764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095776 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 3]
def baseStart_4095776 : Nat := 118140960795 + 4095776 * 2 ^ 59
def prefixEnd_4095776 : Nat := 4983230072969 + 3 ^ 40 * 4095776 * 2
def baseEnd_4095776 : Nat := 2103101741149472491263875

theorem tailTrace_4095776 : CollatzResearch.WordTrace tailWord_4095776 prefixEnd_4095776 2103101741149472491263875 := by
  unfold tailWord_4095776
  simp only [CollatzResearch.WordTrace]
  refine ⟨74692611604855264847821591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99590148806473686463762121 74692611604855264847821591)
  ·
    refine ⟨112038917407282897271732387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74692611604855264847821591 112038917407282897271732387)
    ·
      refine ⟨168058376110924345907598581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112038917407282897271732387 168058376110924345907598581)
      ·
        refine ⟨15755472760399157428837367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168058376110924345907598581 15755472760399157428837367)
        ·
          refine ⟨23633209140598736143256051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15755472760399157428837367 23633209140598736143256051)
          ·
            refine ⟨35449813710898104214884077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23633209140598736143256051 35449813710898104214884077)
            ·
              refine ⟨13293680141586789080581529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35449813710898104214884077 13293680141586789080581529)
              ·
                refine ⟨9970260106190091810436147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13293680141586789080581529 9970260106190091810436147)
                ·
                  refine ⟨14955390159285137715654221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9970260106190091810436147 14955390159285137715654221)
                  ·
                    refine ⟨5608271309731926643370333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14955390159285137715654221 5608271309731926643370333)
                    ·
                      refine ⟨2103101741149472491263875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5608271309731926643370333 2103101741149472491263875)
                      ·
                        rfl

theorem cell23_4095776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_4095776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095776 prefixEnd_4095776 := by exact prefixLift 4095776
  have htrace : WordTrace (prefixWord ++ tailWord_4095776) baseStart_4095776 baseEnd_4095776 := by
    simpa [prefixWord, tailWord_4095776, baseEnd_4095776] using wordTrace_append hprefix tailTrace_4095776
  have hstable : (prefixWord ++ tailWord_4095776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095776).length < 2 ^ (prefixWord ++ tailWord_4095776).sum := by decide
  have hdescent : baseEnd_4095776 < baseStart_4095776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095780 : List Nat := [2, 3, 1, 3, 2, 2, 3, 1, 1, 2, 3]
def baseStart_4095780 : Nat := 118140960795 + 4095780 * 2 ^ 59
def prefixEnd_4095780 : Nat := 4983230072969 + 3 ^ 40 * 4095780 * 2
def baseEnd_4095780 : Nat := 2103103795072090475613857

theorem tailTrace_4095780 : CollatzResearch.WordTrace tailWord_4095780 prefixEnd_4095780 2103103795072090475613857 := by
  unfold tailWord_4095780
  simp only [CollatzResearch.WordTrace]
  refine ⟨74692684550848019189394397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99590246067797358919192529 74692684550848019189394397)
  ·
    refine ⟨28009756706568007196022899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74692684550848019189394397 28009756706568007196022899)
    ·
      refine ⟨42014635059852010794034349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28009756706568007196022899 42014635059852010794034349)
      ·
        refine ⟨15755488147444504047762881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42014635059852010794034349 15755488147444504047762881)
        ·
          refine ⟨11816616110583378035822161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15755488147444504047762881 11816616110583378035822161)
          ·
            refine ⟨8862462082937533526866621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11816616110583378035822161 8862462082937533526866621)
            ·
              refine ⟨3323423281101575072574983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8862462082937533526866621 3323423281101575072574983)
              ·
                refine ⟨4985134921652362608862475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3323423281101575072574983 4985134921652362608862475)
                ·
                  refine ⟨7477702382478543913293713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4985134921652362608862475 7477702382478543913293713)
                  ·
                    refine ⟨5608276786858907934970285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7477702382478543913293713 5608276786858907934970285)
                    ·
                      refine ⟨2103103795072090475613857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5608276786858907934970285 2103103795072090475613857)
                      ·
                        rfl

theorem cell23_4095780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_4095780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095780 prefixEnd_4095780 := by exact prefixLift 4095780
  have htrace : WordTrace (prefixWord ++ tailWord_4095780) baseStart_4095780 baseEnd_4095780 := by
    simpa [prefixWord, tailWord_4095780, baseEnd_4095780] using wordTrace_append hprefix tailTrace_4095780
  have hstable : (prefixWord ++ tailWord_4095780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095780).length < 2 ^ (prefixWord ++ tailWord_4095780).sum := by decide
  have hdescent : baseEnd_4095780 < baseStart_4095780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095793 : List Nat := [1, 2, 2, 3, 2, 2, 1, 4, 2, 1, 3]
def baseStart_4095793 : Nat := 118140960795 + 4095793 * 2 ^ 59
def prefixEnd_4095793 : Nat := 4983230072969 + 3 ^ 40 * 4095793 * 2
def baseEnd_4095793 : Nat := 2103110470320598924751297

theorem tailTrace_4095793 : CollatzResearch.WordTrace tailWord_4095793 prefixEnd_4095793 2103110470320598924751297 := by
  unfold tailWord_4095793
  simp only [CollatzResearch.WordTrace]
  refine ⟨149385843250648941599012033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99590562167099294399341355 149385843250648941599012033)
  ·
    refine ⟨112039382437986706199259025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149385843250648941599012033 112039382437986706199259025)
    ·
      refine ⟨84029536828490029649444269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112039382437986706199259025 84029536828490029649444269)
      ·
        refine ⟨31511076310683761118541601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84029536828490029649444269 31511076310683761118541601)
        ·
          refine ⟨23633307233012820838906201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31511076310683761118541601 23633307233012820838906201)
          ·
            refine ⟨17724980424759615629179651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23633307233012820838906201 17724980424759615629179651)
            ·
              refine ⟨26587470637139423443769477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17724980424759615629179651 26587470637139423443769477)
              ·
                refine ⟨4985150744463641895706777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26587470637139423443769477 4985150744463641895706777)
                ·
                  refine ⟨3738863058347731421780083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4985150744463641895706777 3738863058347731421780083)
                  ·
                    refine ⟨5608294587521597132670125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3738863058347731421780083 5608294587521597132670125)
                    ·
                      refine ⟨2103110470320598924751297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5608294587521597132670125 2103110470320598924751297)
                      ·
                        rfl

theorem cell23_4095793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_4095793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095793 prefixEnd_4095793 := by exact prefixLift 4095793
  have htrace : WordTrace (prefixWord ++ tailWord_4095793) baseStart_4095793 baseEnd_4095793 := by
    simpa [prefixWord, tailWord_4095793, baseEnd_4095793] using wordTrace_append hprefix tailTrace_4095793
  have hstable : (prefixWord ++ tailWord_4095793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095793).length < 2 ^ (prefixWord ++ tailWord_4095793).sum := by decide
  have hdescent : baseEnd_4095793 < baseStart_4095793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095794 : List Nat := [3, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2]
def baseStart_4095794 : Nat := 118140960795 + 4095794 * 2 ^ 59
def prefixEnd_4095794 : Nat := 4983230072969 + 3 ^ 40 * 4095794 * 2
def baseEnd_4095794 : Nat := 2103110983801253420838793

theorem tailTrace_4095794 : CollatzResearch.WordTrace tailWord_4095794 prefixEnd_4095794 2103110983801253420838793 := by
  unfold tailWord_4095794
  simp only [CollatzResearch.WordTrace]
  refine ⟨37346469930911329692449609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99590586482430212513198957 37346469930911329692449609)
  ·
    refine ⟨28009852448183497269337207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37346469930911329692449609 28009852448183497269337207)
    ·
      refine ⟨42014778672275245904005811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28009852448183497269337207 42014778672275245904005811)
      ·
        refine ⟨63022168008412868856008717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42014778672275245904005811 63022168008412868856008717)
        ·
          refine ⟨23633313003154825821003269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63022168008412868856008717 23633313003154825821003269)
          ·
            refine ⟨4431246188091529841438113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23633313003154825821003269 4431246188091529841438113)
            ·
              refine ⟨3323434641068647381078585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4431246188091529841438113 3323434641068647381078585)
              ·
                refine ⟨2492575980801485535808939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3323434641068647381078585 2492575980801485535808939)
                ·
                  refine ⟨3738863971202228303713409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492575980801485535808939 3738863971202228303713409)
                  ·
                    refine ⟨2804147978401671227785057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3738863971202228303713409 2804147978401671227785057)
                    ·
                      refine ⟨2103110983801253420838793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804147978401671227785057 2103110983801253420838793)
                      ·
                        rfl

theorem cell23_4095794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_4095794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095794 prefixEnd_4095794 := by exact prefixLift 4095794
  have htrace : WordTrace (prefixWord ++ tailWord_4095794) baseStart_4095794 baseEnd_4095794 := by
    simpa [prefixWord, tailWord_4095794, baseEnd_4095794] using wordTrace_append hprefix tailTrace_4095794
  have hstable : (prefixWord ++ tailWord_4095794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095794).length < 2 ^ (prefixWord ++ tailWord_4095794).sum := by decide
  have hdescent : baseEnd_4095794 < baseStart_4095794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095796 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_4095796 : Nat := 118140960795 + 4095796 * 2 ^ 59
def prefixEnd_4095796 : Nat := 4983230072969 + 3 ^ 40 * 4095796 * 2
def baseEnd_4095796 : Nat := 701037336920854137671261

theorem tailTrace_4095796 : CollatzResearch.WordTrace tailWord_4095796 prefixEnd_4095796 701037336920854137671261 := by
  unfold tailWord_4095796
  simp only [CollatzResearch.WordTrace]
  refine ⟨74692976334819036555685621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99590635113092048740914161 74692976334819036555685621)
  ·
    refine ⟨7002466531389284677095527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74692976334819036555685621 7002466531389284677095527)
    ·
      refine ⟨10503699797083927015643291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7002466531389284677095527 10503699797083927015643291)
      ·
        refine ⟨15755549695625890523464937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10503699797083927015643291 15755549695625890523464937)
        ·
          refine ⟨11816662271719417892598703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15755549695625890523464937 11816662271719417892598703)
          ·
            refine ⟨17724993407579126838898055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11816662271719417892598703 17724993407579126838898055)
            ·
              refine ⟨26587490111368690258347083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17724993407579126838898055 26587490111368690258347083)
              ·
                refine ⟨39881235167053035387520625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26587490111368690258347083 39881235167053035387520625)
                ·
                  refine ⟨29910926375289776540640469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39881235167053035387520625 29910926375289776540640469)
                  ·
                    refine ⟨701037336920854137671261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29910926375289776540640469 701037336920854137671261)
                    ·
                      rfl

theorem cell23_4095796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_4095796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095796 prefixEnd_4095796 := by exact prefixLift 4095796
  have htrace : WordTrace (prefixWord ++ tailWord_4095796) baseStart_4095796 baseEnd_4095796 := by
    simpa [prefixWord, tailWord_4095796, baseEnd_4095796] using wordTrace_append hprefix tailTrace_4095796
  have hstable : (prefixWord ++ tailWord_4095796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095796).length < 2 ^ (prefixWord ++ tailWord_4095796).sum := by decide
  have hdescent : baseEnd_4095796 < baseStart_4095796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095833 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 4, 2, 2]
def baseStart_4095833 : Nat := 118140960795 + 4095833 * 2 ^ 59
def prefixEnd_4095833 : Nat := 4983230072969 + 3 ^ 40 * 4095833 * 2
def baseEnd_4095833 : Nat := 2103131009546778768251113

theorem tailTrace_4095833 : CollatzResearch.WordTrace tailWord_4095833 prefixEnd_4095833 2103131009546778768251113 := by
  unfold tailWord_4095833
  simp only [CollatzResearch.WordTrace]
  refine ⟨149387302170504028430468153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99591534780336018953645435 149387302170504028430468153)
  ·
    refine ⟨112040476627878021322851115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149387302170504028430468153 112040476627878021322851115)
    ·
      refine ⟨168060714941817031984276673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112040476627878021322851115 168060714941817031984276673)
      ·
        refine ⟨126045536206362773988207505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168060714941817031984276673 126045536206362773988207505)
        ·
          refine ⟨94534152154772080491155629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126045536206362773988207505 94534152154772080491155629)
          ·
            refine ⟨35450307058039530184183361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94534152154772080491155629 35450307058039530184183361)
            ·
              refine ⟨26587730293529647638137521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35450307058039530184183361 26587730293529647638137521)
              ·
                refine ⟨19940797720147235728603141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26587730293529647638137521 19940797720147235728603141)
                ·
                  refine ⟨3738899572527606699113089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19940797720147235728603141 3738899572527606699113089)
                  ·
                    refine ⟨2804174679395705024334817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3738899572527606699113089 2804174679395705024334817)
                    ·
                      refine ⟨2103131009546778768251113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804174679395705024334817 2103131009546778768251113)
                      ·
                        rfl

theorem cell23_4095833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 2, 2].length) (baseStart_4095833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095833 prefixEnd_4095833 := by exact prefixLift 4095833
  have htrace : WordTrace (prefixWord ++ tailWord_4095833) baseStart_4095833 baseEnd_4095833 := by
    simpa [prefixWord, tailWord_4095833, baseEnd_4095833] using wordTrace_append hprefix tailTrace_4095833
  have hstable : (prefixWord ++ tailWord_4095833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095833).length < 2 ^ (prefixWord ++ tailWord_4095833).sum := by decide
  have hdescent : baseEnd_4095833 < baseStart_4095833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095866 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3]
def baseStart_4095866 : Nat := 118140960795 + 4095866 * 2 ^ 59
def prefixEnd_4095866 : Nat := 4983230072969 + 3 ^ 40 * 4095866 * 2
def baseEnd_4095866 : Nat := 2103147954408377139138461

theorem tailTrace_4095866 : CollatzResearch.WordTrace tailWord_4095866 prefixEnd_4095866 2103147954408377139138461 := by
  unfold tailWord_4095866
  simp only [CollatzResearch.WordTrace]
  refine ⟨37347126444846118766604863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99592337186256316710946301 37347126444846118766604863)
  ·
    refine ⟨56020689667269178149907295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37347126444846118766604863 56020689667269178149907295)
    ·
      refine ⟨84031034500903767224860943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56020689667269178149907295 84031034500903767224860943)
      ·
        refine ⟨126046551751355650837291415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84031034500903767224860943 126046551751355650837291415)
        ·
          refine ⟨189069827627033476255937123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126046551751355650837291415 189069827627033476255937123)
          ·
            refine ⟨283604741440550214383905685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189069827627033476255937123 283604741440550214383905685)
            ·
              refine ⟨13293972255025791299245579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 283604741440550214383905685 13293972255025791299245579)
              ·
                refine ⟨19940958382538686948868369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13293972255025791299245579 19940958382538686948868369)
                ·
                  refine ⟨14955718786904015211651277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19940958382538686948868369 14955718786904015211651277)
                  ·
                    refine ⟨5608394545089005704369229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14955718786904015211651277 5608394545089005704369229)
                    ·
                      refine ⟨2103147954408377139138461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5608394545089005704369229 2103147954408377139138461)
                      ·
                        rfl

theorem cell23_4095866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_4095866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095866 prefixEnd_4095866 := by exact prefixLift 4095866
  have htrace : WordTrace (prefixWord ++ tailWord_4095866) baseStart_4095866 baseEnd_4095866 := by
    simpa [prefixWord, tailWord_4095866, baseEnd_4095866] using wordTrace_append hprefix tailTrace_4095866
  have hstable : (prefixWord ++ tailWord_4095866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095866).length < 2 ^ (prefixWord ++ tailWord_4095866).sum := by decide
  have hdescent : baseEnd_4095866 < baseStart_4095866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095890 : List Nat := [3, 2, 3, 2, 1, 1, 3, 3, 5]
def baseStart_4095890 : Nat := 118140960795 + 4095890 * 2 ^ 59
def prefixEnd_4095890 : Nat := 4983230072969 + 3 ^ 40 * 4095890 * 2
def baseEnd_4095890 : Nat := 233684475327120560582039

theorem tailTrace_4095890 : CollatzResearch.WordTrace tailWord_4095890 prefixEnd_4095890 233684475327120560582039 := by
  unfold tailWord_4095890
  simp only [CollatzResearch.WordTrace]
  refine ⟨37347345282824381791323281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99592920754198351443528749 37347345282824381791323281)
  ·
    refine ⟨28010508962118286343492461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37347345282824381791323281 28010508962118286343492461)
    ·
      refine ⟨10503940860794357378809673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28010508962118286343492461 10503940860794357378809673)
      ·
        refine ⟨7877955645595768034107255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10503940860794357378809673 7877955645595768034107255)
        ·
          refine ⟨11816933468393652051160883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7877955645595768034107255 11816933468393652051160883)
          ·
            refine ⟨17725400202590478076741325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11816933468393652051160883 17725400202590478076741325)
            ·
              refine ⟨6647025075971429278777997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17725400202590478076741325 6647025075971429278777997)
              ·
                refine ⟨2492634403489285979541749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6647025075971429278777997 2492634403489285979541749)
                ·
                  refine ⟨233684475327120560582039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2492634403489285979541749 233684475327120560582039)
                  ·
                    rfl

theorem cell23_4095890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_4095890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095890 prefixEnd_4095890 := by exact prefixLift 4095890
  have htrace : WordTrace (prefixWord ++ tailWord_4095890) baseStart_4095890 baseEnd_4095890 := by
    simpa [prefixWord, tailWord_4095890, baseEnd_4095890] using wordTrace_append hprefix tailTrace_4095890
  have hstable : (prefixWord ++ tailWord_4095890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095890).length < 2 ^ (prefixWord ++ tailWord_4095890).sum := by decide
  have hdescent : baseEnd_4095890 < baseStart_4095890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095903 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 2, 5]
def baseStart_4095903 : Nat := 118140960795 + 4095903 * 2 ^ 59
def prefixEnd_4095903 : Nat := 4983230072969 + 3 ^ 40 * 4095903 * 2
def baseEnd_4095903 : Nat := 701055651064197831458597

theorem tailTrace_4095903 : CollatzResearch.WordTrace tailWord_4095903 prefixEnd_4095903 701055651064197831458597 := by
  unfold tailWord_4095903
  simp only [CollatzResearch.WordTrace]
  refine ⟨149389855280250430385516363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99593236853500286923677575 149389855280250430385516363)
  ·
    refine ⟨224084782920375645578274545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149389855280250430385516363 224084782920375645578274545)
    ·
      refine ⟨168063587190281734183705909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224084782920375645578274545 168063587190281734183705909)
      ·
        refine ⟨15755961299088912579722429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168063587190281734183705909 15755961299088912579722429)
        ·
          refine ⟨5908485487158342217395911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15755961299088912579722429 5908485487158342217395911)
          ·
            refine ⟨8862728230737513326093867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5908485487158342217395911 8862728230737513326093867)
            ·
              refine ⟨13294092346106269989140801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8862728230737513326093867 13294092346106269989140801)
              ·
                refine ⟨9970569259579702491855601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13294092346106269989140801 9970569259579702491855601)
                ·
                  refine ⟨7477926944684776868891701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9970569259579702491855601 7477926944684776868891701)
                  ·
                    refine ⟨701055651064197831458597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7477926944684776868891701 701055651064197831458597)
                    ·
                      rfl

theorem cell23_4095903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 5].length) (baseStart_4095903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095903 prefixEnd_4095903 := by exact prefixLift 4095903
  have htrace : WordTrace (prefixWord ++ tailWord_4095903) baseStart_4095903 baseEnd_4095903 := by
    simpa [prefixWord, tailWord_4095903, baseEnd_4095903] using wordTrace_append hprefix tailTrace_4095903
  have hstable : (prefixWord ++ tailWord_4095903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095903).length < 2 ^ (prefixWord ++ tailWord_4095903).sum := by decide
  have hdescent : baseEnd_4095903 < baseStart_4095903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095939 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 9]
def baseStart_4095939 : Nat := 118140960795 + 4095939 * 2 ^ 59
def prefixEnd_4095939 : Nat := 4983230072969 + 3 ^ 40 * 4095939 * 2
def baseEnd_4095939 : Nat := 2103185438496155353525625

theorem tailTrace_4095939 : CollatzResearch.WordTrace tailWord_4095939 prefixEnd_4095939 2103185438496155353525625 := by
  unfold tailWord_4095939
  simp only [CollatzResearch.WordTrace]
  refine ⟨149391168308120008533826871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99594112205413339022551247 149391168308120008533826871)
  ·
    refine ⟨224086752462180012800740307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149391168308120008533826871 224086752462180012800740307)
    ·
      refine ⟨336130128693270019201110461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224086752462180012800740307 336130128693270019201110461)
      ·
        refine ⟨126048798259976257200416423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336130128693270019201110461 126048798259976257200416423)
        ·
          refine ⟨189073197389964385800624635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126048798259976257200416423 189073197389964385800624635)
          ·
            refine ⟨283609796084946578700936953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189073197389964385800624635 283609796084946578700936953)
            ·
              refine ⟨212707347063709934025702715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283609796084946578700936953 212707347063709934025702715)
              ·
                refine ⟨319061020595564901038554073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212707347063709934025702715 319061020595564901038554073)
                ·
                  refine ⟨239295765446673675778915555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319061020595564901038554073 239295765446673675778915555)
                  ·
                    refine ⟨358943648170010513668373333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 239295765446673675778915555 358943648170010513668373333)
                    ·
                      refine ⟨2103185438496155353525625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 358943648170010513668373333 2103185438496155353525625)
                      ·
                        rfl

theorem cell23_4095939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_4095939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095939 prefixEnd_4095939 := by exact prefixLift 4095939
  have htrace : WordTrace (prefixWord ++ tailWord_4095939) baseStart_4095939 baseEnd_4095939 := by
    simpa [prefixWord, tailWord_4095939, baseEnd_4095939] using wordTrace_append hprefix tailTrace_4095939
  have hstable : (prefixWord ++ tailWord_4095939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095939).length < 2 ^ (prefixWord ++ tailWord_4095939).sum := by decide
  have hdescent : baseEnd_4095939 < baseStart_4095939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095950 : List Nat := [4, 1, 1, 1, 2, 2, 2, 5, 1, 4]
def baseStart_4095950 : Nat := 118140960795 + 4095950 * 2 ^ 59
def prefixEnd_4095950 : Nat := 4983230072969 + 3 ^ 40 * 4095950 * 2
def baseEnd_4095950 : Nat := 701063695594451603496025

theorem tailTrace_4095950 : CollatzResearch.WordTrace tailWord_4095950 prefixEnd_4095950 701063695594451603496025 := by
  unfold tailWord_4095950
  simp only [CollatzResearch.WordTrace]
  refine ⟨18673946188885019676559663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99594379674053438274984869 18673946188885019676559663)
  ·
    refine ⟨28010919283327529514839495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18673946188885019676559663 28010919283327529514839495)
    ·
      refine ⟨42016378924991294272259243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28010919283327529514839495 42016378924991294272259243)
      ·
        refine ⟨63024568387486941408388865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42016378924991294272259243 63024568387486941408388865)
        ·
          refine ⟨47268426290615206056291649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63024568387486941408388865 47268426290615206056291649)
          ·
            refine ⟨35451319717961404542218737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47268426290615206056291649 35451319717961404542218737)
            ·
              refine ⟨26588489788471053406664053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35451319717961404542218737 26588489788471053406664053)
              ·
                refine ⟨2492670917669161256874755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26588489788471053406664053 2492670917669161256874755)
                ·
                  refine ⟨3739006376503741885312133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492670917669161256874755 3739006376503741885312133)
                  ·
                    refine ⟨701063695594451603496025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3739006376503741885312133 701063695594451603496025)
                    ·
                      rfl

theorem cell23_4095950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_4095950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095950 prefixEnd_4095950 := by exact prefixLift 4095950
  have htrace : WordTrace (prefixWord ++ tailWord_4095950) baseStart_4095950 baseEnd_4095950 := by
    simpa [prefixWord, tailWord_4095950, baseEnd_4095950] using wordTrace_append hprefix tailTrace_4095950
  have hstable : (prefixWord ++ tailWord_4095950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095950).length < 2 ^ (prefixWord ++ tailWord_4095950).sum := by decide
  have hdescent : baseEnd_4095950 < baseStart_4095950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095967 : List Nat := [1, 1, 2, 3, 4, 1, 4, 2, 1, 4]
def baseStart_4095967 : Nat := 118140960795 + 4095967 * 2 ^ 59
def prefixEnd_4095967 : Nat := 4983230072969 + 3 ^ 40 * 4095967 * 2
def baseEnd_4095967 : Nat := 701066605318160414658499

theorem tailTrace_4095967 : CollatzResearch.WordTrace tailWord_4095967 prefixEnd_4095967 701066605318160414658499 := by
  unfold tailWord_4095967
  simp only [CollatzResearch.WordTrace]
  refine ⟨149392189552018569315846155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99594793034679046210564103 149392189552018569315846155)
  ·
    refine ⟨224088284328027853973769233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149392189552018569315846155 224088284328027853973769233)
    ·
      refine ⟨168066213246020890480326925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224088284328027853973769233 168066213246020890480326925)
      ·
        refine ⟨63024829967257833930122597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168066213246020890480326925 63024829967257833930122597)
        ·
          refine ⟨11817155618860843861897987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63024829967257833930122597 11817155618860843861897987)
          ·
            refine ⟨17725733428291265792846981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11817155618860843861897987 17725733428291265792846981)
            ·
              refine ⟨3323575017804612336158809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17725733428291265792846981 3323575017804612336158809)
              ·
                refine ⟨2492681263353459252119107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3323575017804612336158809 2492681263353459252119107)
                ·
                  refine ⟨3739021895030188878178661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492681263353459252119107 3739021895030188878178661)
                  ·
                    refine ⟨701066605318160414658499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3739021895030188878178661 701066605318160414658499)
                    ·
                      rfl

theorem cell23_4095967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 1, 4].length) (baseStart_4095967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095967 prefixEnd_4095967 := by exact prefixLift 4095967
  have htrace : WordTrace (prefixWord ++ tailWord_4095967) baseStart_4095967 baseEnd_4095967 := by
    simpa [prefixWord, tailWord_4095967, baseEnd_4095967] using wordTrace_append hprefix tailTrace_4095967
  have hstable : (prefixWord ++ tailWord_4095967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095967).length < 2 ^ (prefixWord ++ tailWord_4095967).sum := by decide
  have hdescent : baseEnd_4095967 < baseStart_4095967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4095983 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 1, 5, 2]
def baseStart_4095983 : Nat := 118140960795 + 4095983 * 2 ^ 59
def prefixEnd_4095983 : Nat := 4983230072969 + 3 ^ 40 * 4095983 * 2
def baseEnd_4095983 : Nat := 2103208031644953181375423

theorem tailTrace_4095983 : CollatzResearch.WordTrace tailWord_4095983 prefixEnd_4095983 2103208031644953181375423 := by
  unfold tailWord_4095983
  simp only [CollatzResearch.WordTrace]
  refine ⟨149392773119960604048428603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99595182079973736032285735 149392773119960604048428603)
  ·
    refine ⟨224089159679940906072642905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149392773119960604048428603 224089159679940906072642905)
    ·
      refine ⟨168066869759955679554482179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224089159679940906072642905 168066869759955679554482179)
      ·
        refine ⟨252100304639933519331723269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168066869759955679554482179 252100304639933519331723269)
        ·
          refine ⟨47268807119987534874698113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252100304639933519331723269 47268807119987534874698113)
          ·
            refine ⟨35451605339990651156023585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47268807119987534874698113 35451605339990651156023585)
            ·
              refine ⟨26588704004992988367017689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35451605339990651156023585 26588704004992988367017689)
              ·
                refine ⟨19941528003744741275263267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26588704004992988367017689 19941528003744741275263267)
                ·
                  refine ⟨29912292005617111912894901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19941528003744741275263267 29912292005617111912894901)
                  ·
                    refine ⟨2804277375526604241833897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29912292005617111912894901 2804277375526604241833897)
                    ·
                      refine ⟨2103208031644953181375423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804277375526604241833897 2103208031644953181375423)
                      ·
                        rfl

theorem cell23_4095983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 5, 2].length) (baseStart_4095983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4095983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4095983 prefixEnd_4095983 := by exact prefixLift 4095983
  have htrace : WordTrace (prefixWord ++ tailWord_4095983) baseStart_4095983 baseEnd_4095983 := by
    simpa [prefixWord, tailWord_4095983, baseEnd_4095983] using wordTrace_append hprefix tailTrace_4095983
  have hstable : (prefixWord ++ tailWord_4095983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4095983).length < 2 ^ (prefixWord ++ tailWord_4095983).sum := by decide
  have hdescent : baseEnd_4095983 < baseStart_4095983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4095983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096007 : List Nat := [1, 1, 4, 3, 1, 2, 1, 5, 1, 1, 3]
def baseStart_4096007 : Nat := 118140960795 + 4096007 * 2 ^ 59
def prefixEnd_4096007 : Nat := 4983230072969 + 3 ^ 40 * 4096007 * 2
def baseEnd_4096007 : Nat := 2103220355180661087475313

theorem tailTrace_4096007 : CollatzResearch.WordTrace tailWord_4096007 prefixEnd_4096007 2103220355180661087475313 := by
  unfold tailWord_4096007
  simp only [CollatzResearch.WordTrace]
  refine ⟨149393648471873656147302275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99595765647915770764868183 149393648471873656147302275)
  ·
    refine ⟨224090472707810484220953413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149393648471873656147302275 224090472707810484220953413)
    ·
      refine ⟨42016963632714465791428765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224090472707810484220953413 42016963632714465791428765)
      ·
        refine ⟨15756361362267924671785787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42016963632714465791428765 15756361362267924671785787)
        ·
          refine ⟨23634542043401887007678681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15756361362267924671785787 23634542043401887007678681)
          ·
            refine ⟨17725906532551415255759011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23634542043401887007678681 17725906532551415255759011)
            ·
              refine ⟨26588859798827122883638517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17725906532551415255759011 26588859798827122883638517)
              ·
                refine ⟨2492705606140042770341111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26588859798827122883638517 2492705606140042770341111)
                ·
                  refine ⟨3739058409210064155511667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492705606140042770341111 3739058409210064155511667)
                  ·
                    refine ⟨5608587613815096233267501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3739058409210064155511667 5608587613815096233267501)
                    ·
                      refine ⟨2103220355180661087475313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5608587613815096233267501 2103220355180661087475313)
                      ·
                        rfl

theorem cell23_4096007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_4096007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096007 prefixEnd_4096007 := by exact prefixLift 4096007
  have htrace : WordTrace (prefixWord ++ tailWord_4096007) baseStart_4096007 baseEnd_4096007 := by
    simpa [prefixWord, tailWord_4096007, baseEnd_4096007] using wordTrace_append hprefix tailTrace_4096007
  have hstable : (prefixWord ++ tailWord_4096007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096007).length < 2 ^ (prefixWord ++ tailWord_4096007).sum := by decide
  have hdescent : baseEnd_4096007 < baseStart_4096007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096010 : List Nat := [3, 1, 2, 2, 4, 1, 1, 3, 1, 5]
def baseStart_4096010 : Nat := 118140960795 + 4096010 * 2 ^ 59
def prefixEnd_4096010 : Nat := 4983230072969 + 3 ^ 40 * 4096010 * 2
def baseEnd_4096010 : Nat := 701073965207541525245933

theorem tailTrace_4096010 : CollatzResearch.WordTrace tailWord_4096010 prefixEnd_4096010 701073965207541525245933 := by
  unfold tailWord_4096010
  simp only [CollatzResearch.WordTrace]
  refine ⟨37348439472715696914915371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99595838593908525106440989 37348439472715696914915371)
  ·
    refine ⟨56022659209073545372373057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37348439472715696914915371 56022659209073545372373057)
    ·
      refine ⟨42016994406805159029279793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56022659209073545372373057 42016994406805159029279793)
      ·
        refine ⟨31512745805103869271959845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42016994406805159029279793 31512745805103869271959845)
        ·
          refine ⟨5908639838456975488492471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31512745805103869271959845 5908639838456975488492471)
          ·
            refine ⟨8862959757685463232738707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5908639838456975488492471 8862959757685463232738707)
            ·
              refine ⟨13294439636528194849108061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8862959757685463232738707 13294439636528194849108061)
              ·
                refine ⟨4985414863698073068415523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13294439636528194849108061 4985414863698073068415523)
                ·
                  refine ⟨7478122295547109602623285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4985414863698073068415523 7478122295547109602623285)
                  ·
                    refine ⟨701073965207541525245933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7478122295547109602623285 701073965207541525245933)
                    ·
                      rfl

theorem cell23_4096010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_4096010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096010 prefixEnd_4096010 := by exact prefixLift 4096010
  have htrace : WordTrace (prefixWord ++ tailWord_4096010) baseStart_4096010 baseEnd_4096010 := by
    simpa [prefixWord, tailWord_4096010, baseEnd_4096010] using wordTrace_append hprefix tailTrace_4096010
  have hstable : (prefixWord ++ tailWord_4096010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096010).length < 2 ^ (prefixWord ++ tailWord_4096010).sum := by decide
  have hdescent : baseEnd_4096010 < baseStart_4096010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096050 : List Nat := [3, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3]
def baseStart_4096050 : Nat := 118140960795 + 4096050 * 2 ^ 59
def prefixEnd_4096050 : Nat := 4983230072969 + 3 ^ 40 * 4096050 * 2
def baseEnd_4096050 : Nat := 2103242434848804419237615

theorem tailTrace_4096050 : CollatzResearch.WordTrace tailWord_4096050 prefixEnd_4096050 2103242434848804419237615 := by
  unfold tailWord_4096050
  simp only [CollatzResearch.WordTrace]
  refine ⟨37348804202679468622779401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99596811207145249660745069 37348804202679468622779401)
  ·
    refine ⟨28011603152009601467084551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37348804202679468622779401 28011603152009601467084551)
    ·
      refine ⟨42017404728014402200626827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28011603152009601467084551 42017404728014402200626827)
      ·
        refine ⟨63026107092021603300940241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42017404728014402200626827 63026107092021603300940241)
        ·
          refine ⟨47269580319016202475705181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63026107092021603300940241 47269580319016202475705181)
          ·
            refine ⟨17726092619631075928389443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47269580319016202475705181 17726092619631075928389443)
            ·
              refine ⟨26589138929446613892584165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17726092619631075928389443 26589138929446613892584165)
              ·
                refine ⟨4985463549271240104859531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26589138929446613892584165 4985463549271240104859531)
                ·
                  refine ⟨7478195323906860157289297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4985463549271240104859531 7478195323906860157289297)
                  ·
                    refine ⟨5608646492930145117966973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7478195323906860157289297 5608646492930145117966973)
                    ·
                      refine ⟨2103242434848804419237615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5608646492930145117966973 2103242434848804419237615)
                      ·
                        rfl

theorem cell23_4096050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_4096050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096050 prefixEnd_4096050 := by exact prefixLift 4096050
  have htrace : WordTrace (prefixWord ++ tailWord_4096050) baseStart_4096050 baseEnd_4096050 := by
    simpa [prefixWord, tailWord_4096050, baseEnd_4096050] using wordTrace_append hprefix tailTrace_4096050
  have hstable : (prefixWord ++ tailWord_4096050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096050).length < 2 ^ (prefixWord ++ tailWord_4096050).sum := by decide
  have hdescent : baseEnd_4096050 < baseStart_4096050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096053 : List Nat := [1, 3, 3, 1, 1, 1, 6, 7]
def baseStart_4096053 : Nat := 118140960795 + 4096053 * 2 ^ 59
def prefixEnd_4096053 : Nat := 4983230072969 + 3 ^ 40 * 4096053 * 2
def baseEnd_4096053 : Nat := 77897925010769181759263

theorem tailTrace_4096053 : CollatzResearch.WordTrace tailWord_4096053 prefixEnd_4096053 77897925010769181759263 := by
  unfold tailWord_4096053
  simp only [CollatzResearch.WordTrace]
  refine ⟨149395326229707006003476813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99596884153138004002317875 149395326229707006003476813)
  ·
    refine ⟨56023247336140127251303805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149395326229707006003476813 56023247336140127251303805)
    ·
      refine ⟨21008717751052547719238927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56023247336140127251303805 21008717751052547719238927)
      ·
        refine ⟨31513076626578821578858391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21008717751052547719238927 31513076626578821578858391)
        ·
          refine ⟨47269614939868232368287587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31513076626578821578858391 47269614939868232368287587)
          ·
            refine ⟨70904422409802348552431381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47269614939868232368287587 70904422409802348552431381)
            ·
              refine ⟨3323644800459485088395221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70904422409802348552431381 3323644800459485088395221)
              ·
                refine ⟨77897925010769181759263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3323644800459485088395221 77897925010769181759263)
                ·
                  rfl

theorem cell23_4096053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 7].length) (baseStart_4096053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096053 prefixEnd_4096053 := by exact prefixLift 4096053
  have htrace : WordTrace (prefixWord ++ tailWord_4096053) baseStart_4096053 baseEnd_4096053 := by
    simpa [prefixWord, tailWord_4096053, baseEnd_4096053] using wordTrace_append hprefix tailTrace_4096053
  have hstable : (prefixWord ++ tailWord_4096053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096053).length < 2 ^ (prefixWord ++ tailWord_4096053).sum := by decide
  have hdescent : baseEnd_4096053 < baseStart_4096053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096063 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 3]
def baseStart_4096063 : Nat := 118140960795 + 4096063 * 2 ^ 59
def prefixEnd_4096063 : Nat := 4983230072969 + 3 ^ 40 * 4096063 * 2
def baseEnd_4096063 : Nat := 2103249110097312868375055

theorem tailTrace_4096063 : CollatzResearch.WordTrace tailWord_4096063 prefixEnd_4096063 2103249110097312868375055 := by
  unfold tailWord_4096063
  simp only [CollatzResearch.WordTrace]
  refine ⟨149395690959670777711340843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99597127306447185140893895 149395690959670777711340843)
  ·
    refine ⟨224093536439506166567011265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149395690959670777711340843 224093536439506166567011265)
    ·
      refine ⟨168070152329629624925258449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224093536439506166567011265 168070152329629624925258449)
      ·
        refine ⟨126052614247222218693943837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168070152329629624925258449 126052614247222218693943837)
        ·
          refine ⟨47269730342708332010228939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126052614247222218693943837 47269730342708332010228939)
          ·
            refine ⟨70904595514062498015343409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47269730342708332010228939 70904595514062498015343409)
            ·
              refine ⟨53178446635546873511507557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70904595514062498015343409 53178446635546873511507557)
              ·
                refine ⟨9970958744165038783407667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53178446635546873511507557 9970958744165038783407667)
                ·
                  refine ⟨14956438116247558175111501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9970958744165038783407667 14956438116247558175111501)
                  ·
                    refine ⟨5608664293592834315666813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14956438116247558175111501 5608664293592834315666813)
                    ·
                      refine ⟨2103249110097312868375055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5608664293592834315666813 2103249110097312868375055)
                      ·
                        rfl

theorem cell23_4096063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_4096063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096063 prefixEnd_4096063 := by exact prefixLift 4096063
  have htrace : WordTrace (prefixWord ++ tailWord_4096063) baseStart_4096063 baseEnd_4096063 := by
    simpa [prefixWord, tailWord_4096063, baseEnd_4096063] using wordTrace_append hprefix tailTrace_4096063
  have hstable : (prefixWord ++ tailWord_4096063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096063).length < 2 ^ (prefixWord ++ tailWord_4096063).sum := by decide
  have hdescent : baseEnd_4096063 < baseStart_4096063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096064 : List Nat := [2, 1, 1, 2, 2, 4, 3, 3, 1, 2, 2]
def baseStart_4096064 : Nat := 118140960795 + 4096064 * 2 ^ 59
def prefixEnd_4096064 : Nat := 4983230072969 + 3 ^ 40 * 4096064 * 2
def baseEnd_4096064 : Nat := 2103249623577967364462551

theorem tailTrace_4096064 : CollatzResearch.WordTrace tailWord_4096064 prefixEnd_4096064 2103249623577967364462551 := by
  unfold tailWord_4096064
  simp only [CollatzResearch.WordTrace]
  refine ⟨74697863716333577441063623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99597151621778103254751497 74697863716333577441063623)
  ·
    refine ⟨112046795574500366161595435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74697863716333577441063623 112046795574500366161595435)
    ·
      refine ⟨168070193361750549242393153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112046795574500366161595435 168070193361750549242393153)
      ·
        refine ⟨126052645021312911931794865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168070193361750549242393153 126052645021312911931794865)
        ·
          refine ⟨94539483765984683948846149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126052645021312911931794865 94539483765984683948846149)
          ·
            refine ⟨17726153206122128240408653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94539483765984683948846149 17726153206122128240408653)
            ·
              refine ⟨6647307452295798090153245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17726153206122128240408653 6647307452295798090153245)
              ·
                refine ⟨2492740294610924283807467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6647307452295798090153245 2492740294610924283807467)
                ·
                  refine ⟨3739110441916386425711201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492740294610924283807467 3739110441916386425711201)
                  ·
                    refine ⟨2804332831437289819283401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3739110441916386425711201 2804332831437289819283401)
                    ·
                      refine ⟨2103249623577967364462551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804332831437289819283401 2103249623577967364462551)
                      ·
                        rfl

theorem cell23_4096064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 1, 2, 2].length) (baseStart_4096064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096064 prefixEnd_4096064 := by exact prefixLift 4096064
  have htrace : WordTrace (prefixWord ++ tailWord_4096064) baseStart_4096064 baseEnd_4096064 := by
    simpa [prefixWord, tailWord_4096064, baseEnd_4096064] using wordTrace_append hprefix tailTrace_4096064
  have hstable : (prefixWord ++ tailWord_4096064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096064).length < 2 ^ (prefixWord ++ tailWord_4096064).sum := by decide
  have hdescent : baseEnd_4096064 < baseStart_4096064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096090 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2]
def baseStart_4096090 : Nat := 118140960795 + 4096090 * 2 ^ 59
def prefixEnd_4096090 : Nat := 4983230072969 + 3 ^ 40 * 4096090 * 2
def baseEnd_4096090 : Nat := 2103262974074984262737431

theorem tailTrace_4096090 : CollatzResearch.WordTrace tailWord_4096090 prefixEnd_4096090 2103262974074984262737431 := by
  unfold tailWord_4096090
  simp only [CollatzResearch.WordTrace]
  refine ⟨37349168932643240330643431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99597783820381974215049149 37349168932643240330643431)
  ·
    refine ⟨56023753398964860495965147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37349168932643240330643431 56023753398964860495965147)
    ·
      refine ⟨84035630098447290743947721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56023753398964860495965147 84035630098447290743947721)
      ·
        refine ⟨63026722573835468057960791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84035630098447290743947721 63026722573835468057960791)
        ·
          refine ⟨94540083860753202086941187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63026722573835468057960791 94540083860753202086941187)
          ·
            refine ⟨141810125791129803130411781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94540083860753202086941187 141810125791129803130411781)
            ·
              refine ⟨26589398585836838086952209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141810125791129803130411781 26589398585836838086952209)
              ·
                refine ⟨19942048939377628565214157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26589398585836838086952209 19942048939377628565214157)
                ·
                  refine ⟨7478268352266610711955309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19942048939377628565214157 7478268352266610711955309)
                  ·
                    refine ⟨2804350632099979016983241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7478268352266610711955309 2804350632099979016983241)
                    ·
                      refine ⟨2103262974074984262737431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804350632099979016983241 2103262974074984262737431)
                      ·
                        rfl

theorem cell23_4096090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_4096090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096090 prefixEnd_4096090 := by exact prefixLift 4096090
  have htrace : WordTrace (prefixWord ++ tailWord_4096090) baseStart_4096090 baseEnd_4096090 := by
    simpa [prefixWord, tailWord_4096090, baseEnd_4096090] using wordTrace_append hprefix tailTrace_4096090
  have hstable : (prefixWord ++ tailWord_4096090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096090).length < 2 ^ (prefixWord ++ tailWord_4096090).sum := by decide
  have hdescent : baseEnd_4096090 < baseStart_4096090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096124 : List Nat := [2, 2, 2, 1, 1, 5, 3, 1, 1, 3, 2]
def baseStart_4096124 : Nat := 118140960795 + 4096124 * 2 ^ 59
def prefixEnd_4096124 : Nat := 4983230072969 + 3 ^ 40 * 4096124 * 2
def baseEnd_4096124 : Nat := 2103280432417237129712275

theorem tailTrace_4096124 : CollatzResearch.WordTrace tailWord_4096124 prefixEnd_4096124 2103280432417237129712275 := by
  unfold tailWord_4096124
  simp only [CollatzResearch.WordTrace]
  refine ⟨74698957906224892564655713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99598610541633190086207617 74698957906224892564655713)
  ·
    refine ⟨56024218429668669423491785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74698957906224892564655713 56024218429668669423491785)
    ·
      refine ⟨42018163822251502067618839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56024218429668669423491785 42018163822251502067618839)
      ·
        refine ⟨63027245733377253101428259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42018163822251502067618839 63027245733377253101428259)
        ·
          refine ⟨94540868600065879652142389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63027245733377253101428259 94540868600065879652142389)
          ·
            refine ⟨8863206431256176217388349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94540868600065879652142389 8863206431256176217388349)
            ·
              refine ⟨3323702411721066081520631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8863206431256176217388349 3323702411721066081520631)
              ·
                refine ⟨4985553617581599122280947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3323702411721066081520631 4985553617581599122280947)
                ·
                  refine ⟨7478330426372398683421421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4985553617581599122280947 7478330426372398683421421)
                  ·
                    refine ⟨2804373909889649506283033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7478330426372398683421421 2804373909889649506283033)
                    ·
                      refine ⟨2103280432417237129712275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804373909889649506283033 2103280432417237129712275)
                      ·
                        rfl

theorem cell23_4096124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_4096124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096124 prefixEnd_4096124 := by exact prefixLift 4096124
  have htrace : WordTrace (prefixWord ++ tailWord_4096124) baseStart_4096124 baseEnd_4096124 := by
    simpa [prefixWord, tailWord_4096124, baseEnd_4096124] using wordTrace_append hprefix tailTrace_4096124
  have hstable : (prefixWord ++ tailWord_4096124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096124).length < 2 ^ (prefixWord ++ tailWord_4096124).sum := by decide
  have hdescent : baseEnd_4096124 < baseStart_4096124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096154 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2]
def baseStart_4096154 : Nat := 118140960795 + 4096154 * 2 ^ 59
def prefixEnd_4096154 : Nat := 4983230072969 + 3 ^ 40 * 4096154 * 2
def baseEnd_4096154 : Nat := 2103295836836872012337137

theorem tailTrace_4096154 : CollatzResearch.WordTrace tailWord_4096154 prefixEnd_4096154 2103295836836872012337137 := by
  unfold tailWord_4096154
  simp only [CollatzResearch.WordTrace]
  refine ⟨37349752500585275063225879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99599340001560733501935677 37349752500585275063225879)
  ·
    refine ⟨56024628750877912594838819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37349752500585275063225879 56024628750877912594838819)
    ·
      refine ⟨84036943126316868892258229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56024628750877912594838819 84036943126316868892258229)
      ·
        refine ⟨7878463418092206458649209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84036943126316868892258229 7878463418092206458649209)
        ·
          refine ⟨5908847563569154843986907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7878463418092206458649209 5908847563569154843986907)
          ·
            refine ⟨8863271345353732265980361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5908847563569154843986907 8863271345353732265980361)
            ·
              refine ⟨6647453509015299199485271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8863271345353732265980361 6647453509015299199485271)
              ·
                refine ⟨9971180263522948799227907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6647453509015299199485271 9971180263522948799227907)
                ·
                  refine ⟨14956770395284423198841861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9971180263522948799227907 14956770395284423198841861)
                  ·
                    refine ⟨2804394449115829349782849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14956770395284423198841861 2804394449115829349782849)
                    ·
                      refine ⟨2103295836836872012337137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804394449115829349782849 2103295836836872012337137)
                      ·
                        rfl

theorem cell23_4096154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_4096154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096154 prefixEnd_4096154 := by exact prefixLift 4096154
  have htrace : WordTrace (prefixWord ++ tailWord_4096154) baseStart_4096154 baseEnd_4096154 := by
    simpa [prefixWord, tailWord_4096154, baseEnd_4096154] using wordTrace_append hprefix tailTrace_4096154
  have hstable : (prefixWord ++ tailWord_4096154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096154).length < 2 ^ (prefixWord ++ tailWord_4096154).sum := by decide
  have hdescent : baseEnd_4096154 < baseStart_4096154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096188 : List Nat := [2, 2, 2, 3, 4, 1, 1, 2, 2, 2, 2]
def baseStart_4096188 : Nat := 118140960795 + 4096188 * 2 ^ 59
def prefixEnd_4096188 : Nat := 4983230072969 + 3 ^ 40 * 4096188 * 2
def baseEnd_4096188 : Nat := 2103313295179124879311981

theorem tailTrace_4096188 : CollatzResearch.WordTrace tailWord_4096188 prefixEnd_4096188 2103313295179124879311981 := by
  unfold tailWord_4096188
  simp only [CollatzResearch.WordTrace]
  refine ⟨74700125042108962029820609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99600166722811949373094145 74700125042108962029820609)
  ·
    refine ⟨56025093781581721522365457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74700125042108962029820609 56025093781581721522365457)
    ·
      refine ⟨42018820336186291141774093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56025093781581721522365457 42018820336186291141774093)
      ·
        refine ⟨15757057626069859178165285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42018820336186291141774093 15757057626069859178165285)
        ·
          refine ⟨2954448304888098595905991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15757057626069859178165285 2954448304888098595905991)
          ·
            refine ⟨4431672457332147893858987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954448304888098595905991 4431672457332147893858987)
            ·
              refine ⟨6647508685998221840788481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4431672457332147893858987 6647508685998221840788481)
              ·
                refine ⟨4985631514498666380591361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6647508685998221840788481 4985631514498666380591361)
                ·
                  refine ⟨3739223635873999785443521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4985631514498666380591361 3739223635873999785443521)
                  ·
                    refine ⟨2804417726905499839082641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3739223635873999785443521 2804417726905499839082641)
                    ·
                      refine ⟨2103313295179124879311981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804417726905499839082641 2103313295179124879311981)
                      ·
                        rfl

theorem cell23_4096188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_4096188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096188 prefixEnd_4096188 := by exact prefixLift 4096188
  have htrace : WordTrace (prefixWord ++ tailWord_4096188) baseStart_4096188 baseEnd_4096188 := by
    simpa [prefixWord, tailWord_4096188, baseEnd_4096188] using wordTrace_append hprefix tailTrace_4096188
  have hstable : (prefixWord ++ tailWord_4096188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096188).length < 2 ^ (prefixWord ++ tailWord_4096188).sum := by decide
  have hdescent : baseEnd_4096188 < baseStart_4096188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096194 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 7]
def baseStart_4096194 : Nat := 118140960795 + 4096194 * 2 ^ 59
def prefixEnd_4096194 : Nat := 4983230072969 + 3 ^ 40 * 4096194 * 2
def baseEnd_4096194 : Nat := 233701819562561317315217

theorem tailTrace_4096194 : CollatzResearch.WordTrace tailWord_4096194 prefixEnd_4096194 233701819562561317315217 := by
  unfold tailWord_4096194
  simp only [CollatzResearch.WordTrace]
  refine ⟨37350117230549046771089909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99600312614797458056239757 37350117230549046771089909)
  ·
    refine ⟨3501573490363973134789679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37350117230549046771089909 3501573490363973134789679)
    ·
      refine ⟨5252360235545959702184519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3501573490363973134789679 5252360235545959702184519)
      ·
        refine ⟨7878540353318939553276779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5252360235545959702184519 7878540353318939553276779)
        ·
          refine ⟨11817810529978409329915169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7878540353318939553276779 11817810529978409329915169)
          ·
            refine ⟨8863357897483806997436377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11817810529978409329915169 8863357897483806997436377)
            ·
              refine ⟨6647518423112855248077283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8863357897483806997436377 6647518423112855248077283)
              ·
                refine ⟨9971277634669282872115925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6647518423112855248077283 9971277634669282872115925)
                ·
                  refine ⟨233701819562561317315217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9971277634669282872115925 233701819562561317315217)
                  ·
                    rfl

theorem cell23_4096194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_4096194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096194 prefixEnd_4096194 := by exact prefixLift 4096194
  have htrace : WordTrace (prefixWord ++ tailWord_4096194) baseStart_4096194 baseEnd_4096194 := by
    simpa [prefixWord, tailWord_4096194, baseEnd_4096194] using wordTrace_append hprefix tailTrace_4096194
  have hstable : (prefixWord ++ tailWord_4096194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096194).length < 2 ^ (prefixWord ++ tailWord_4096194).sum := by decide
  have hdescent : baseEnd_4096194 < baseStart_4096194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096210 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_4096210 : Nat := 118140960795 + 4096210 * 2 ^ 59
def prefixEnd_4096210 : Nat := 4983230072969 + 3 ^ 40 * 4096210 * 2
def baseEnd_4096210 : Nat := 2103324591753523793236879

theorem tailTrace_4096210 : CollatzResearch.WordTrace tailWord_4096210 prefixEnd_4096210 2103324591753523793236879 := by
  unfold tailWord_4096210
  simp only [CollatzResearch.WordTrace]
  refine ⟨37350263122534555454235521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99600701660092147877961389 37350263122534555454235521)
  ·
    refine ⟨28012697341900916590676641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37350263122534555454235521 28012697341900916590676641)
    ·
      refine ⟨21009523006425687443007481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28012697341900916590676641 21009523006425687443007481)
      ·
        refine ⟨15757142254819265582255611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21009523006425687443007481 15757142254819265582255611)
        ·
          refine ⟨23635713382228898373383417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15757142254819265582255611 23635713382228898373383417)
          ·
            refine ⟨17726785036671673780037563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23635713382228898373383417 17726785036671673780037563)
            ·
              refine ⟨26590177555007510670056345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17726785036671673780037563 26590177555007510670056345)
              ·
                refine ⟨19942633166255633002542259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26590177555007510670056345 19942633166255633002542259)
                ·
                  refine ⟨29913949749383449503813389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19942633166255633002542259 29913949749383449503813389)
                  ·
                    refine ⟨11217731156018793563930021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29913949749383449503813389 11217731156018793563930021)
                    ·
                      refine ⟨2103324591753523793236879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11217731156018793563930021 2103324591753523793236879)
                      ·
                        rfl

theorem cell23_4096210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_4096210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096210 prefixEnd_4096210 := by exact prefixLift 4096210
  have htrace : WordTrace (prefixWord ++ tailWord_4096210) baseStart_4096210 baseEnd_4096210 := by
    simpa [prefixWord, tailWord_4096210, baseEnd_4096210] using wordTrace_append hprefix tailTrace_4096210
  have hstable : (prefixWord ++ tailWord_4096210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096210).length < 2 ^ (prefixWord ++ tailWord_4096210).sum := by decide
  have hdescent : baseEnd_4096210 < baseStart_4096210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096223 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 4]
def baseStart_4096223 : Nat := 118140960795 + 4096223 * 2 ^ 59
def prefixEnd_4096223 : Nat := 4983230072969 + 3 ^ 40 * 4096223 * 2
def baseEnd_4096223 : Nat := 2103331267002032242374319

theorem tailTrace_4096223 : CollatzResearch.WordTrace tailWord_4096223 prefixEnd_4096223 2103331267002032242374319 := by
  unfold tailWord_4096223
  simp only [CollatzResearch.WordTrace]
  refine ⟨149401526639091125037165323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99601017759394083358110215 149401526639091125037165323)
  ·
    refine ⟨224102289958636687555747985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149401526639091125037165323 224102289958636687555747985)
    ·
      refine ⟨168076717468977515666810989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224102289958636687555747985 168076717468977515666810989)
      ·
        refine ⟨63028769050866568375054121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168076717468977515666810989 63028769050866568375054121)
        ·
          refine ⟨47271576788149926281290591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63028769050866568375054121 47271576788149926281290591)
          ·
            refine ⟨70907365182224889421935887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47271576788149926281290591 70907365182224889421935887)
            ·
              refine ⟨106361047773337334132903831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70907365182224889421935887 106361047773337334132903831)
              ·
                refine ⟨159541571660006001199355747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106361047773337334132903831 159541571660006001199355747)
                ·
                  refine ⟨239312357490009001799033621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159541571660006001199355747 239312357490009001799033621)
                  ·
                    refine ⟨11217766757344171959329701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 239312357490009001799033621 11217766757344171959329701)
                    ·
                      refine ⟨2103331267002032242374319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11217766757344171959329701 2103331267002032242374319)
                      ·
                        rfl

theorem cell23_4096223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_4096223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096223 prefixEnd_4096223 := by exact prefixLift 4096223
  have htrace : WordTrace (prefixWord ++ tailWord_4096223) baseStart_4096223 baseEnd_4096223 := by
    simpa [prefixWord, tailWord_4096223, baseEnd_4096223] using wordTrace_append hprefix tailTrace_4096223
  have hstable : (prefixWord ++ tailWord_4096223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096223).length < 2 ^ (prefixWord ++ tailWord_4096223).sum := by decide
  have hdescent : baseEnd_4096223 < baseStart_4096223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096253 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_4096253 : Nat := 118140960795 + 4096253 * 2 ^ 59
def prefixEnd_4096253 : Nat := 4983230072969 + 3 ^ 40 * 4096253 * 2
def baseEnd_4096253 : Nat := 2103346671421667124999181

theorem tailTrace_4096253 : CollatzResearch.WordTrace tailWord_4096253 prefixEnd_4096253 2103346671421667124999181 := by
  unfold tailWord_4096253
  simp only [CollatzResearch.WordTrace]
  refine ⟨149402620828982440160757413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99601747219321626773838275 149402620828982440160757413)
  ·
    refine ⟨28012991405434207530142015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149402620828982440160757413 28012991405434207530142015)
    ·
      refine ⟨42019487108151311295213023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28012991405434207530142015 42019487108151311295213023)
      ·
        refine ⟨63029230662226966942819535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42019487108151311295213023 63029230662226966942819535)
        ·
          refine ⟨94543845993340450414229303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63029230662226966942819535 94543845993340450414229303)
          ·
            refine ⟨141815768990010675621343955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94543845993340450414229303 141815768990010675621343955)
            ·
              refine ⟨212723653485016013432015933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141815768990010675621343955 212723653485016013432015933)
              ·
                refine ⟨79771370056881005037005975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212723653485016013432015933 79771370056881005037005975)
                ·
                  refine ⟨119657055085321507555508963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79771370056881005037005975 119657055085321507555508963)
                  ·
                    refine ⟨179485582627982261333263445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119657055085321507555508963 179485582627982261333263445)
                    ·
                      refine ⟨2103346671421667124999181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 179485582627982261333263445 2103346671421667124999181)
                      ·
                        rfl

theorem cell23_4096253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_4096253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096253 prefixEnd_4096253 := by exact prefixLift 4096253
  have htrace : WordTrace (prefixWord ++ tailWord_4096253) baseStart_4096253 baseEnd_4096253 := by
    simpa [prefixWord, tailWord_4096253, baseEnd_4096253] using wordTrace_append hprefix tailTrace_4096253
  have hstable : (prefixWord ++ tailWord_4096253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096253).length < 2 ^ (prefixWord ++ tailWord_4096253).sum := by decide
  have hdescent : baseEnd_4096253 < baseStart_4096253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096277 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 3, 1, 3]
def baseStart_4096277 : Nat := 118140960795 + 4096277 * 2 ^ 59
def prefixEnd_4096277 : Nat := 4983230072969 + 3 ^ 40 * 4096277 * 2
def baseEnd_4096277 : Nat := 2103358994957375031099071

theorem tailTrace_4096277 : CollatzResearch.WordTrace tailWord_4096277 prefixEnd_4096277 2103358994957375031099071 := by
  unfold tailWord_4096277
  simp only [CollatzResearch.WordTrace]
  refine ⟨149403496180895492259631085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99602330787263661506420723 149403496180895492259631085)
  ·
    refine ⟨56026311067835809597361657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149403496180895492259631085 56026311067835809597361657)
    ·
      refine ⟨42019733300876857198021243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56026311067835809597361657 42019733300876857198021243)
      ·
        refine ⟨63029599951315285797031865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42019733300876857198021243 63029599951315285797031865)
        ·
          refine ⟨47272199963486464347773899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63029599951315285797031865 47272199963486464347773899)
          ·
            refine ⟨70908299945229696521660849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47272199963486464347773899 70908299945229696521660849)
            ·
              refine ⟨53181224958922272391245637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70908299945229696521660849 53181224958922272391245637)
              ·
                refine ⟨9971479679797926073358557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53181224958922272391245637 9971479679797926073358557)
                ·
                  refine ⟨3739304879924222277509459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9971479679797926073358557 3739304879924222277509459)
                  ·
                    refine ⟨5608957319886333416264189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3739304879924222277509459 5608957319886333416264189)
                    ·
                      refine ⟨2103358994957375031099071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5608957319886333416264189 2103358994957375031099071)
                      ·
                        rfl

theorem cell23_4096277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_4096277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096277 prefixEnd_4096277 := by exact prefixLift 4096277
  have htrace : WordTrace (prefixWord ++ tailWord_4096277) baseStart_4096277 baseEnd_4096277 := by
    simpa [prefixWord, tailWord_4096277, baseEnd_4096277] using wordTrace_append hprefix tailTrace_4096277
  have hstable : (prefixWord ++ tailWord_4096277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096277).length < 2 ^ (prefixWord ++ tailWord_4096277).sum := by decide
  have hdescent : baseEnd_4096277 < baseStart_4096277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096280 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 3, 5]
def baseStart_4096280 : Nat := 118140960795 + 4096280 * 2 ^ 59
def prefixEnd_4096280 : Nat := 4983230072969 + 3 ^ 40 * 4096280 * 2
def baseEnd_4096280 : Nat := 701120178466446173120519

theorem tailTrace_4096280 : CollatzResearch.WordTrace tailWord_4096280 prefixEnd_4096280 701120178466446173120519 := by
  unfold tailWord_4096280
  simp only [CollatzResearch.WordTrace]
  refine ⟨74701802799942311885995147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99602403733256415847993529 74701802799942311885995147)
  ·
    refine ⟨112052704199913467828992721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74701802799942311885995147 112052704199913467828992721)
    ·
      refine ⟨84039528149935100871744541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112052704199913467828992721 84039528149935100871744541)
      ·
        refine ⟨31514823056225662826904203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84039528149935100871744541 31514823056225662826904203)
        ·
          refine ⟨47272234584338494240356305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31514823056225662826904203 47272234584338494240356305)
          ·
            refine ⟨35454175938253870680267229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47272234584338494240356305 35454175938253870680267229)
            ·
              refine ⟨13295315976845201505100211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35454175938253870680267229 13295315976845201505100211)
              ·
                refine ⟨19942973965267802257650317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13295315976845201505100211 19942973965267802257650317)
                ·
                  refine ⟨7478615236975425846618869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19942973965267802257650317 7478615236975425846618869)
                  ·
                    refine ⟨701120178466446173120519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7478615236975425846618869 701120178466446173120519)
                    ·
                      rfl

theorem cell23_4096280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_4096280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096280 prefixEnd_4096280 := by exact prefixLift 4096280
  have htrace : WordTrace (prefixWord ++ tailWord_4096280) baseStart_4096280 baseEnd_4096280 := by
    simpa [prefixWord, tailWord_4096280, baseEnd_4096280] using wordTrace_append hprefix tailTrace_4096280
  have hstable : (prefixWord ++ tailWord_4096280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096280).length < 2 ^ (prefixWord ++ tailWord_4096280).sum := by decide
  have hdescent : baseEnd_4096280 < baseStart_4096280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096327 : List Nat := [1, 1, 4, 1, 2, 2, 1, 5, 2, 4]
def baseStart_4096327 : Nat := 118140960795 + 4096327 * 2 ^ 59
def prefixEnd_4096327 : Nat := 4983230072969 + 3 ^ 40 * 4096327 * 2
def baseEnd_4096327 : Nat := 701128222996699945157947

theorem tailTrace_4096327 : CollatzResearch.WordTrace tailWord_4096327 prefixEnd_4096327 701128222996699945157947 := by
  unfold tailWord_4096327
  simp only [CollatzResearch.WordTrace]
  refine ⟨149405319830714350798951235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99603546553809567199300823 149405319830714350798951235)
  ·
    refine ⟨224107979746071526198426853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149405319830714350798951235 224107979746071526198426853)
    ·
      refine ⟨42020246202388411162205035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224107979746071526198426853 42020246202388411162205035)
      ·
        refine ⟨63030369303582616743307553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42020246202388411162205035 63030369303582616743307553)
        ·
          refine ⟨47272776977686962557480665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63030369303582616743307553 47272776977686962557480665)
          ·
            refine ⟨35454582733265221918110499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47272776977686962557480665 35454582733265221918110499)
            ·
              refine ⟨53181874099897832877165749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35454582733265221918110499 53181874099897832877165749)
              ·
                refine ⟨4985800696865421832234289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53181874099897832877165749 4985800696865421832234289)
                ·
                  refine ⟨3739350522649066374175717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4985800696865421832234289 3739350522649066374175717)
                  ·
                    refine ⟨701128222996699945157947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3739350522649066374175717 701128222996699945157947)
                    ·
                      rfl

theorem cell23_4096327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_4096327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096327 prefixEnd_4096327 := by exact prefixLift 4096327
  have htrace : WordTrace (prefixWord ++ tailWord_4096327) baseStart_4096327 baseEnd_4096327 := by
    simpa [prefixWord, tailWord_4096327, baseEnd_4096327] using wordTrace_append hprefix tailTrace_4096327
  have hstable : (prefixWord ++ tailWord_4096327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096327).length < 2 ^ (prefixWord ++ tailWord_4096327).sum := by decide
  have hdescent : baseEnd_4096327 < baseStart_4096327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096337 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 3, 2, 3]
def baseStart_4096337 : Nat := 118140960795 + 4096337 * 2 ^ 59
def prefixEnd_4096337 : Nat := 4983230072969 + 3 ^ 40 * 4096337 * 2
def baseEnd_4096337 : Nat := 2103389803796644796348795

theorem tailTrace_4096337 : CollatzResearch.WordTrace tailWord_4096337 prefixEnd_4096337 2103389803796644796348795 := by
  unfold tailWord_4096337
  simp only [CollatzResearch.WordTrace]
  refine ⟨149405684560678122506815265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99603789707118748337876843 149405684560678122506815265)
  ·
    refine ⟨112054263420508591880111449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149405684560678122506815265 112054263420508591880111449)
    ·
      refine ⟨84040697565381443910083587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112054263420508591880111449 84040697565381443910083587)
      ·
        refine ⟨126061046348072165865125381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84040697565381443910083587 126061046348072165865125381)
        ·
          refine ⟨23636446190263531099711009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126061046348072165865125381 23636446190263531099711009)
          ·
            refine ⟨17727334642697648324783257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23636446190263531099711009 17727334642697648324783257)
            ·
              refine ⟨13295500982023236243587443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17727334642697648324783257 13295500982023236243587443)
              ·
                refine ⟨19943251473034854365381165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13295500982023236243587443 19943251473034854365381165)
                ·
                  refine ⟨7478719302388070387017937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19943251473034854365381165 7478719302388070387017937)
                  ·
                    refine ⟨5609039476791052790263453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7478719302388070387017937 5609039476791052790263453)
                    ·
                      refine ⟨2103389803796644796348795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5609039476791052790263453 2103389803796644796348795)
                      ·
                        rfl

theorem cell23_4096337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_4096337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096337 prefixEnd_4096337 := by exact prefixLift 4096337
  have htrace : WordTrace (prefixWord ++ tailWord_4096337) baseStart_4096337 baseEnd_4096337 := by
    simpa [prefixWord, tailWord_4096337, baseEnd_4096337] using wordTrace_append hprefix tailTrace_4096337
  have hstable : (prefixWord ++ tailWord_4096337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096337).length < 2 ^ (prefixWord ++ tailWord_4096337).sum := by decide
  have hdescent : baseEnd_4096337 < baseStart_4096337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096348 : List Nat := [2, 2, 4, 3, 1, 2, 2, 1, 1, 5]
def baseStart_4096348 : Nat := 118140960795 + 4096348 * 2 ^ 59
def prefixEnd_4096348 : Nat := 4983230072969 + 3 ^ 40 * 4096348 * 2
def baseEnd_4096348 : Nat := 701131817361281417770415

theorem tailTrace_4096348 : CollatzResearch.WordTrace tailWord_4096348 prefixEnd_4096348 701131817361281417770415 := by
  unfold tailWord_4096348
  simp only [CollatzResearch.WordTrace]
  refine ⟨74703042881819135692732849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99604057175758847590310465 74703042881819135692732849)
  ·
    refine ⟨56027282161364351769549637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74703042881819135692732849 56027282161364351769549637)
    ·
      refine ⟨10505115405255815956790557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56027282161364351769549637 10505115405255815956790557)
      ·
        refine ⟨3939418276970930983796459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10505115405255815956790557 3939418276970930983796459)
        ·
          refine ⟨5909127415456396475694689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3939418276970930983796459 5909127415456396475694689)
          ·
            refine ⟨4431845561592297356771017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5909127415456396475694689 4431845561592297356771017)
            ·
              refine ⟨3323884171194223017578263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4431845561592297356771017 3323884171194223017578263)
              ·
                refine ⟨4985826256791334526367395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3323884171194223017578263 4985826256791334526367395)
                ·
                  refine ⟨7478739385187001789551093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4985826256791334526367395 7478739385187001789551093)
                  ·
                    refine ⟨701131817361281417770415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7478739385187001789551093 701131817361281417770415)
                    ·
                      rfl

theorem cell23_4096348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_4096348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096348 prefixEnd_4096348 := by exact prefixLift 4096348
  have htrace : WordTrace (prefixWord ++ tailWord_4096348) baseStart_4096348 baseEnd_4096348 := by
    simpa [prefixWord, tailWord_4096348, baseEnd_4096348] using wordTrace_append hprefix tailTrace_4096348
  have hstable : (prefixWord ++ tailWord_4096348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096348).length < 2 ^ (prefixWord ++ tailWord_4096348).sum := by decide
  have hdescent : baseEnd_4096348 < baseStart_4096348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096351 : List Nat := [1, 1, 2, 3, 1, 2, 3, 5, 1, 2, 2]
def baseStart_4096351 : Nat := 118140960795 + 4096351 * 2 ^ 59
def prefixEnd_4096351 : Nat := 4983230072969 + 3 ^ 40 * 4096351 * 2
def baseEnd_4096351 : Nat := 2103396992525807741573731

theorem tailTrace_4096351 : CollatzResearch.WordTrace tailWord_4096351 prefixEnd_4096351 2103396992525807741573731 := by
  unfold tailWord_4096351
  simp only [CollatzResearch.WordTrace]
  refine ⟨149406195182627402897824907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99604130121751601931883271 149406195182627402897824907)
  ·
    refine ⟨224109292773941104346737361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149406195182627402897824907 224109292773941104346737361)
    ·
      refine ⟨168081969580455828260053021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224109292773941104346737361 168081969580455828260053021)
      ·
        refine ⟨63030738592670935597519883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168081969580455828260053021 63030738592670935597519883)
        ·
          refine ⟨94546107889006403396279825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63030738592670935597519883 94546107889006403396279825)
          ·
            refine ⟨70909580916754802547209869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94546107889006403396279825 70909580916754802547209869)
            ·
              refine ⟨26591092843783050955203701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70909580916754802547209869 26591092843783050955203701)
              ·
                refine ⟨2492914954104661027050347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26591092843783050955203701 2492914954104661027050347)
                ·
                  refine ⟨3739372431156991540575521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492914954104661027050347 3739372431156991540575521)
                  ·
                    refine ⟨2804529323367743655431641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3739372431156991540575521 2804529323367743655431641)
                    ·
                      refine ⟨2103396992525807741573731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804529323367743655431641 2103396992525807741573731)
                      ·
                        rfl

theorem cell23_4096351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_4096351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096351 prefixEnd_4096351 := by exact prefixLift 4096351
  have htrace : WordTrace (prefixWord ++ tailWord_4096351) baseStart_4096351 baseEnd_4096351 := by
    simpa [prefixWord, tailWord_4096351, baseEnd_4096351] using wordTrace_append hprefix tailTrace_4096351
  have hstable : (prefixWord ++ tailWord_4096351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096351).length < 2 ^ (prefixWord ++ tailWord_4096351).sum := by decide
  have hdescent : baseEnd_4096351 < baseStart_4096351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096487 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_4096487 : Nat := 118140960795 + 4096487 * 2 ^ 59
def prefixEnd_4096487 : Nat := 4983230072969 + 3 ^ 40 * 4096487 * 2
def baseEnd_4096487 : Nat := 2103466825894819209473105

theorem tailTrace_4096487 : CollatzResearch.WordTrace tailWord_4096487 prefixEnd_4096487 2103466825894819209473105 := by
  unfold tailWord_4096487
  simp only [CollatzResearch.WordTrace]
  refine ⟨149411155510134698124775715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99607437006756465416517143 149411155510134698124775715)
  ·
    refine ⟨224116733265202047187163573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149411155510134698124775715 224116733265202047187163573)
    ·
      refine ⟨21010943743612691923796585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224116733265202047187163573 21010943743612691923796585)
      ·
        refine ⟨15758207807709518942847439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21010943743612691923796585 15758207807709518942847439)
        ·
          refine ⟨23637311711564278414271159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15758207807709518942847439 23637311711564278414271159)
          ·
            refine ⟨35455967567346417621406739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23637311711564278414271159 35455967567346417621406739)
            ·
              refine ⟨53183951351019626432110109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35455967567346417621406739 53183951351019626432110109)
              ·
                refine ⟨19943981756632359912041291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53183951351019626432110109 19943981756632359912041291)
                ·
                  refine ⟨29915972634948539868061937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19943981756632359912041291 29915972634948539868061937)
                  ·
                    refine ⟨22436979476211404901046453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29915972634948539868061937 22436979476211404901046453)
                    ·
                      refine ⟨2103466825894819209473105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22436979476211404901046453 2103466825894819209473105)
                      ·
                        rfl

theorem cell23_4096487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_4096487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096487 prefixEnd_4096487 := by exact prefixLift 4096487
  have htrace : WordTrace (prefixWord ++ tailWord_4096487) baseStart_4096487 baseEnd_4096487 := by
    simpa [prefixWord, tailWord_4096487, baseEnd_4096487] using wordTrace_append hprefix tailTrace_4096487
  have hstable : (prefixWord ++ tailWord_4096487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096487).length < 2 ^ (prefixWord ++ tailWord_4096487).sum := by decide
  have hdescent : baseEnd_4096487 < baseStart_4096487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096497 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 1, 3, 4]
def baseStart_4096497 : Nat := 118140960795 + 4096497 * 2 ^ 59
def prefixEnd_4096497 : Nat := 4983230072969 + 3 ^ 40 * 4096497 * 2
def baseEnd_4096497 : Nat := 2103471960701364170348059

theorem tailTrace_4096497 : CollatzResearch.WordTrace tailWord_4096497 prefixEnd_4096497 2103471960701364170348059 := by
  unfold tailWord_4096497
  simp only [CollatzResearch.WordTrace]
  refine ⟨149411520240098469832639745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99607680160065646555093163 149411520240098469832639745)
  ·
    refine ⟨112058640180073852374479809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149411520240098469832639745 112058640180073852374479809)
    ·
      refine ⟨84043980135055389280859857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112058640180073852374479809 84043980135055389280859857)
      ·
        refine ⟨63032985101291541960644893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84043980135055389280859857 63032985101291541960644893)
        ·
          refine ⟨23637369412984328235241835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63032985101291541960644893 23637369412984328235241835)
          ·
            refine ⟨35456054119476492352862753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23637369412984328235241835 35456054119476492352862753)
            ·
              refine ⟨26592040589607369264647065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35456054119476492352862753 26592040589607369264647065)
              ·
                refine ⟨19944030442205526948485299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26592040589607369264647065 19944030442205526948485299)
                ·
                  refine ⟨29916045663308290422727949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19944030442205526948485299 29916045663308290422727949)
                  ·
                    refine ⟨11218517123740608908522981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29916045663308290422727949 11218517123740608908522981)
                    ·
                      refine ⟨2103471960701364170348059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11218517123740608908522981 2103471960701364170348059)
                      ·
                        rfl

theorem cell23_4096497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_4096497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096497 prefixEnd_4096497 := by exact prefixLift 4096497
  have htrace : WordTrace (prefixWord ++ tailWord_4096497) baseStart_4096497 baseEnd_4096497 := by
    simpa [prefixWord, tailWord_4096497, baseEnd_4096497] using wordTrace_append hprefix tailTrace_4096497
  have hstable : (prefixWord ++ tailWord_4096497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096497).length < 2 ^ (prefixWord ++ tailWord_4096497).sum := by decide
  have hdescent : baseEnd_4096497 < baseStart_4096497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096541 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 3, 4]
def baseStart_4096541 : Nat := 118140960795 + 4096541 * 2 ^ 59
def prefixEnd_4096541 : Nat := 4983230072969 + 3 ^ 40 * 4096541 * 2
def baseEnd_4096541 : Nat := 701164851283387332732619

theorem tailTrace_4096541 : CollatzResearch.WordTrace tailWord_4096541 prefixEnd_4096541 701164851283387332732619 := by
  unfold tailWord_4096541
  simp only [CollatzResearch.WordTrace]
  refine ⟨149413125051939065347241477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99608750034626043564827651 149413125051939065347241477)
  ·
    refine ⟨28014960947238574752607777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149413125051939065347241477 28014960947238574752607777)
    ·
      refine ⟨21011220710428931064455833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28014960947238574752607777 21011220710428931064455833)
      ·
        refine ⟨15758415532821698298341875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21011220710428931064455833 15758415532821698298341875)
        ·
          refine ⟨23637623299232547447512813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15758415532821698298341875 23637623299232547447512813)
          ·
            refine ⟨8864108737212205292817305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23637623299232547447512813 8864108737212205292817305)
            ·
              refine ⟨6648081552909153969612979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8864108737212205292817305 6648081552909153969612979)
              ·
                refine ⟨9972122329363730954419469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6648081552909153969612979 9972122329363730954419469)
                ·
                  refine ⟨3739545873511399107907301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9972122329363730954419469 3739545873511399107907301)
                  ·
                    refine ⟨701164851283387332732619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3739545873511399107907301 701164851283387332732619)
                    ·
                      rfl

theorem cell23_4096541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_4096541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096541 prefixEnd_4096541 := by exact prefixLift 4096541
  have htrace : WordTrace (prefixWord ++ tailWord_4096541) baseStart_4096541 baseEnd_4096541 := by
    simpa [prefixWord, tailWord_4096541, baseEnd_4096541] using wordTrace_append hprefix tailTrace_4096541
  have hstable : (prefixWord ++ tailWord_4096541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096541).length < 2 ^ (prefixWord ++ tailWord_4096541).sum := by decide
  have hdescent : baseEnd_4096541 < baseStart_4096541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096621 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_4096621 : Nat := 118140960795 + 4096621 * 2 ^ 59
def prefixEnd_4096621 : Nat := 4983230072969 + 3 ^ 40 * 4096621 * 2
def baseEnd_4096621 : Nat := 2103535632302521685197489

theorem tailTrace_4096621 : CollatzResearch.WordTrace tailWord_4096621 prefixEnd_4096621 2103535632302521685197489 := by
  unfold tailWord_4096621
  simp only [CollatzResearch.WordTrace]
  refine ⟨149416042891649239010153717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99610695261099492673435811 149416042891649239010153717)
  ·
    refine ⟨14007754021092116157201911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149416042891649239010153717 14007754021092116157201911)
    ·
      refine ⟨21011631031638174235802867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14007754021092116157201911 21011631031638174235802867)
      ·
        refine ⟨31517446547457261353704301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21011631031638174235802867 31517446547457261353704301)
        ·
          refine ⟨11819042455296473007639113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31517446547457261353704301 11819042455296473007639113)
          ·
            refine ⟨8864281841472354755729335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11819042455296473007639113 8864281841472354755729335)
            ·
              refine ⟨13296422762208532133594003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8864281841472354755729335 13296422762208532133594003)
              ·
                refine ⟨19944634143312798200391005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13296422762208532133594003 19944634143312798200391005)
                ·
                  refine ⟨7479237803742299325146627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19944634143312798200391005 7479237803742299325146627)
                  ·
                    refine ⟨11218856705613448987719941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7479237803742299325146627 11218856705613448987719941)
                    ·
                      refine ⟨2103535632302521685197489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11218856705613448987719941 2103535632302521685197489)
                      ·
                        rfl

theorem cell23_4096621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_4096621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096621 prefixEnd_4096621 := by exact prefixLift 4096621
  have htrace : WordTrace (prefixWord ++ tailWord_4096621) baseStart_4096621 baseEnd_4096621 := by
    simpa [prefixWord, tailWord_4096621, baseEnd_4096621] using wordTrace_append hprefix tailTrace_4096621
  have hstable : (prefixWord ++ tailWord_4096621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096621).length < 2 ^ (prefixWord ++ tailWord_4096621).sum := by decide
  have hdescent : baseEnd_4096621 < baseStart_4096621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096689 : List Nat := [1, 2, 2, 6, 1, 1, 2, 3, 1, 2, 2]
def baseStart_4096689 : Nat := 118140960795 + 4096689 * 2 ^ 59
def prefixEnd_4096689 : Nat := 4983230072969 + 3 ^ 40 * 4096689 * 2
def baseEnd_4096689 : Nat := 2103570548987027419147177

theorem tailTrace_4096689 : CollatzResearch.WordTrace tailWord_4096689 prefixEnd_4096689 2103570548987027419147177 := by
  unfold tailWord_4096689
  simp only [CollatzResearch.WordTrace]
  refine ⟨149418523055402886623629121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99612348703601924415752747 149418523055402886623629121)
  ·
    refine ⟨112063892291552164967721841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149418523055402886623629121 112063892291552164967721841)
    ·
      refine ⟨84047919218664123725791381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112063892291552164967721841 84047919218664123725791381)
      ·
        refine ⟨3939746213374880799646471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84047919218664123725791381 3939746213374880799646471)
        ·
          refine ⟨5909619320062321199469707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3939746213374880799646471 5909619320062321199469707)
          ·
            refine ⟨8864428980093481799204561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5909619320062321199469707 8864428980093481799204561)
            ·
              refine ⟨6648321735070111349403421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8864428980093481799204561 6648321735070111349403421)
              ·
                refine ⟨2493120650651291756026283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6648321735070111349403421 2493120650651291756026283)
                ·
                  refine ⟨3739680975976937634039425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2493120650651291756026283 3739680975976937634039425)
                  ·
                    refine ⟨2804760731982703225529569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3739680975976937634039425 2804760731982703225529569)
                    ·
                      refine ⟨2103570548987027419147177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804760731982703225529569 2103570548987027419147177)
                      ·
                        rfl

theorem cell23_4096689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_4096689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096689 prefixEnd_4096689 := by exact prefixLift 4096689
  have htrace : WordTrace (prefixWord ++ tailWord_4096689) baseStart_4096689 baseEnd_4096689 := by
    simpa [prefixWord, tailWord_4096689, baseEnd_4096689] using wordTrace_append hprefix tailTrace_4096689
  have hstable : (prefixWord ++ tailWord_4096689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096689).length < 2 ^ (prefixWord ++ tailWord_4096689).sum := by decide
  have hdescent : baseEnd_4096689 < baseStart_4096689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096698 : List Nat := [3, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2]
def baseStart_4096698 : Nat := 118140960795 + 4096698 * 2 ^ 59
def prefixEnd_4096698 : Nat := 4983230072969 + 3 ^ 40 * 4096698 * 2
def baseEnd_4096698 : Nat := 2103575170312917883934635

theorem tailTrace_4096698 : CollatzResearch.WordTrace tailWord_4096698 prefixEnd_4096698 2103575170312917883934635 := by
  unfold tailWord_4096698
  simp only [CollatzResearch.WordTrace]
  refine ⟨37354712828092570290176687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99612567541580187440471165 37354712828092570290176687)
  ·
    refine ⟨56032069242138855435265031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37354712828092570290176687 56032069242138855435265031)
    ·
      refine ⟨84048103863208283152897547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56032069242138855435265031 84048103863208283152897547)
      ·
        refine ⟨126072155794812424729346321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84048103863208283152897547 126072155794812424729346321)
        ·
          refine ⟨94554116846109318547009741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126072155794812424729346321 94554116846109318547009741)
          ·
            refine ⟨35457793817290994455128653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94554116846109318547009741 35457793817290994455128653)
            ·
              refine ⟨13296672681484122920673245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35457793817290994455128653 13296672681484122920673245)
              ·
                refine ⟨4986252255556546095252467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13296672681484122920673245 4986252255556546095252467)
                ·
                  refine ⟨7479378383334819142878701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4986252255556546095252467 7479378383334819142878701)
                  ·
                    refine ⟨2804766893750557178579513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7479378383334819142878701 2804766893750557178579513)
                    ·
                      refine ⟨2103575170312917883934635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804766893750557178579513 2103575170312917883934635)
                      ·
                        rfl

theorem cell23_4096698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2].length) (baseStart_4096698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096698 prefixEnd_4096698 := by exact prefixLift 4096698
  have htrace : WordTrace (prefixWord ++ tailWord_4096698) baseStart_4096698 baseEnd_4096698 := by
    simpa [prefixWord, tailWord_4096698, baseEnd_4096698] using wordTrace_append hprefix tailTrace_4096698
  have hstable : (prefixWord ++ tailWord_4096698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096698).length < 2 ^ (prefixWord ++ tailWord_4096698).sum := by decide
  have hdescent : baseEnd_4096698 < baseStart_4096698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096704 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 2, 6]
def baseStart_4096704 : Nat := 118140960795 + 4096704 * 2 ^ 59
def prefixEnd_4096704 : Nat := 4983230072969 + 3 ^ 40 * 4096704 * 2
def baseEnd_4096704 : Nat := 701192750398948286819869

theorem tailTrace_4096704 : CollatzResearch.WordTrace tailWord_4096704 prefixEnd_4096704 701192750398948286819869 := by
  unfold tailWord_4096704
  simp only [CollatzResearch.WordTrace]
  refine ⟨74709535075174272092712583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99612713433565696123616777 74709535075174272092712583)
  ·
    refine ⟨112064302612761408139068875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74709535075174272092712583 112064302612761408139068875)
    ·
      refine ⟨168096453919142112208603313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112064302612761408139068875 168096453919142112208603313)
      ·
        refine ⟨126072340439356584156452485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168096453919142112208603313 126072340439356584156452485)
        ·
          refine ⟨23638563832379359529334841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126072340439356584156452485 23638563832379359529334841)
          ·
            refine ⟨17728922874284519647001131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23638563832379359529334841 17728922874284519647001131)
            ·
              refine ⟨26593384311426779470501697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17728922874284519647001131 26593384311426779470501697)
              ·
                refine ⟨19945038233570084602876273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26593384311426779470501697 19945038233570084602876273)
                ·
                  refine ⟨14958778675177563452157205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19945038233570084602876273 14958778675177563452157205)
                  ·
                    refine ⟨701192750398948286819869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14958778675177563452157205 701192750398948286819869)
                    ·
                      rfl

theorem cell23_4096704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 2, 6].length) (baseStart_4096704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096704 prefixEnd_4096704 := by exact prefixLift 4096704
  have htrace : WordTrace (prefixWord ++ tailWord_4096704) baseStart_4096704 baseEnd_4096704 := by
    simpa [prefixWord, tailWord_4096704, baseEnd_4096704] using wordTrace_append hprefix tailTrace_4096704
  have hstable : (prefixWord ++ tailWord_4096704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096704).length < 2 ^ (prefixWord ++ tailWord_4096704).sum := by decide
  have hdescent : baseEnd_4096704 < baseStart_4096704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096722 : List Nat := [3, 2, 2, 2, 3, 1, 3, 1, 2, 1, 3]
def baseStart_4096722 : Nat := 118140960795 + 4096722 * 2 ^ 59
def prefixEnd_4096722 : Nat := 4983230072969 + 3 ^ 40 * 4096722 * 2
def baseEnd_4096722 : Nat := 2103587493848625790034525

theorem tailTrace_4096722 : CollatzResearch.WordTrace tailWord_4096722 prefixEnd_4096722 2103587493848625790034525 := by
  unfold tailWord_4096722
  simp only [CollatzResearch.WordTrace]
  refine ⟨37354931666070833314895105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99613151109522222173053613 37354931666070833314895105)
  ·
    refine ⟨28016198749553124986171329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37354931666070833314895105 28016198749553124986171329)
    ·
      refine ⟨21012149062164843739628497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28016198749553124986171329 21012149062164843739628497)
      ·
        refine ⟨15759111796623632804721373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21012149062164843739628497 15759111796623632804721373)
        ·
          refine ⟨5909666923733862301770515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15759111796623632804721373 5909666923733862301770515)
          ·
            refine ⟨8864500385600793452655773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5909666923733862301770515 8864500385600793452655773)
            ·
              refine ⟨3324187644600297544745915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8864500385600793452655773 3324187644600297544745915)
              ·
                refine ⟨4986281466900446317118873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3324187644600297544745915 4986281466900446317118873)
                ·
                  refine ⟨3739711100175334737839155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4986281466900446317118873 3739711100175334737839155)
                  ·
                    refine ⟨5609566650263002106758733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3739711100175334737839155 5609566650263002106758733)
                    ·
                      refine ⟨2103587493848625790034525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5609566650263002106758733 2103587493848625790034525)
                      ·
                        rfl

theorem cell23_4096722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_4096722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096722 prefixEnd_4096722 := by exact prefixLift 4096722
  have htrace : WordTrace (prefixWord ++ tailWord_4096722) baseStart_4096722 baseEnd_4096722 := by
    simpa [prefixWord, tailWord_4096722, baseEnd_4096722] using wordTrace_append hprefix tailTrace_4096722
  have hstable : (prefixWord ++ tailWord_4096722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096722).length < 2 ^ (prefixWord ++ tailWord_4096722).sum := by decide
  have hdescent : baseEnd_4096722 < baseStart_4096722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096728 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 1, 4, 2]
def baseStart_4096728 : Nat := 118140960795 + 4096728 * 2 ^ 59
def prefixEnd_4096728 : Nat := 4983230072969 + 3 ^ 40 * 4096728 * 2
def baseEnd_4096728 : Nat := 2103590574732552766559497

theorem tailTrace_4096728 : CollatzResearch.WordTrace tailWord_4096728 prefixEnd_4096728 2103590574732552766559497 := by
  unfold tailWord_4096728
  simp only [CollatzResearch.WordTrace]
  refine ⟨74709972751130798142149419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99613297001507730856199225 74709972751130798142149419)
  ·
    refine ⟨112064959126696197213224129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74709972751130798142149419 112064959126696197213224129)
    ·
      refine ⟨84048719345022147909918097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112064959126696197213224129 84048719345022147909918097)
      ·
        refine ⟨63036539508766610932438573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84048719345022147909918097 63036539508766610932438573)
        ·
          refine ⟨23638702315787479099664465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63036539508766610932438573 23638702315787479099664465)
          ·
            refine ⟨17729026736840609324748349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23638702315787479099664465 17729026736840609324748349)
            ·
              refine ⟨6648385026315228496780631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17729026736840609324748349 6648385026315228496780631)
              ·
                refine ⟨9972577539472842745170947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6648385026315228496780631 9972577539472842745170947)
                ·
                  refine ⟨14958866309209264117756421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9972577539472842745170947 14958866309209264117756421)
                  ·
                    refine ⟨2804787432976737022079329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14958866309209264117756421 2804787432976737022079329)
                    ·
                      refine ⟨2103590574732552766559497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804787432976737022079329 2103590574732552766559497)
                      ·
                        rfl

theorem cell23_4096728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_4096728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096728 prefixEnd_4096728 := by exact prefixLift 4096728
  have htrace : WordTrace (prefixWord ++ tailWord_4096728) baseStart_4096728 baseEnd_4096728 := by
    simpa [prefixWord, tailWord_4096728, baseEnd_4096728] using wordTrace_append hprefix tailTrace_4096728
  have hstable : (prefixWord ++ tailWord_4096728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096728).length < 2 ^ (prefixWord ++ tailWord_4096728).sum := by decide
  have hdescent : baseEnd_4096728 < baseStart_4096728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096732 : List Nat := [2, 2, 5, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_4096732 : Nat := 118140960795 + 4096732 * 2 ^ 59
def prefixEnd_4096732 : Nat := 4983230072969 + 3 ^ 40 * 4096732 * 2
def baseEnd_4096732 : Nat := 2103592628655170750909479

theorem tailTrace_4096732 : CollatzResearch.WordTrace tailWord_4096732 prefixEnd_4096732 2103592628655170750909479 := by
  unfold tailWord_4096732
  simp only [CollatzResearch.WordTrace]
  refine ⟨74710045697123552483722225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99613394262831403311629633 74710045697123552483722225)
  ·
    refine ⟨56032534272842664362791669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74710045697123552483722225 56032534272842664362791669)
    ·
      refine ⟨5253050088078999784011719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56032534272842664362791669 5253050088078999784011719)
      ·
        refine ⟨7879575132118499676017579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5253050088078999784011719 7879575132118499676017579)
        ·
          refine ⟨11819362698177749514026369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7879575132118499676017579 11819362698177749514026369)
          ·
            refine ⟨8864522023633312135519777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11819362698177749514026369 8864522023633312135519777)
            ·
              refine ⟨6648391517724984101639833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8864522023633312135519777 6648391517724984101639833)
              ·
                refine ⟨4986293638293738076229875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6648391517724984101639833 4986293638293738076229875)
                ·
                  refine ⟨7479440457440607114344813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4986293638293738076229875 7479440457440607114344813)
                  ·
                    refine ⟨2804790171540227667879305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7479440457440607114344813 2804790171540227667879305)
                    ·
                      refine ⟨2103592628655170750909479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804790171540227667879305 2103592628655170750909479)
                      ·
                        rfl

theorem cell23_4096732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_4096732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096732 prefixEnd_4096732 := by exact prefixLift 4096732
  have htrace : WordTrace (prefixWord ++ tailWord_4096732) baseStart_4096732 baseEnd_4096732 := by
    simpa [prefixWord, tailWord_4096732, baseEnd_4096732] using wordTrace_append hprefix tailTrace_4096732
  have hstable : (prefixWord ++ tailWord_4096732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096732).length < 2 ^ (prefixWord ++ tailWord_4096732).sum := by decide
  have hdescent : baseEnd_4096732 < baseStart_4096732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096771 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 2, 5, 2]
def baseStart_4096771 : Nat := 118140960795 + 4096771 * 2 ^ 59
def prefixEnd_4096771 : Nat := 4983230072969 + 3 ^ 40 * 4096771 * 2
def baseEnd_4096771 : Nat := 2103612654400696098321799

theorem tailTrace_4096771 : CollatzResearch.WordTrace tailWord_4096771 prefixEnd_4096771 2103612654400696098321799 := by
  unfold tailWord_4096771
  simp only [CollatzResearch.WordTrace]
  refine ⟨149421513841105814628114167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99614342560737209752076111 149421513841105814628114167)
  ·
    refine ⟨224132270761658721942171251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149421513841105814628114167 224132270761658721942171251)
    ·
      refine ⟨336198406142488082913256877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224132270761658721942171251 336198406142488082913256877)
      ·
        refine ⟨126074402303433031092471329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336198406142488082913256877 126074402303433031092471329)
        ·
          refine ⟨94555801727574773319353497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126074402303433031092471329 94555801727574773319353497)
          ·
            refine ⟨70916851295681079989515123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94555801727574773319353497 70916851295681079989515123)
            ·
              refine ⟨106375276943521619984272685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70916851295681079989515123 106375276943521619984272685)
              ·
                refine ⟨39890728853820607494102257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106375276943521619984272685 39890728853820607494102257)
                ·
                  refine ⟨29918046640365455620576693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39890728853820607494102257 29918046640365455620576693)
                  ·
                    refine ⟨2804816872534261464429065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29918046640365455620576693 2804816872534261464429065)
                    ·
                      refine ⟨2103612654400696098321799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804816872534261464429065 2103612654400696098321799)
                      ·
                        rfl

theorem cell23_4096771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 5, 2].length) (baseStart_4096771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096771 prefixEnd_4096771 := by exact prefixLift 4096771
  have htrace : WordTrace (prefixWord ++ tailWord_4096771) baseStart_4096771 baseEnd_4096771 := by
    simpa [prefixWord, tailWord_4096771, baseEnd_4096771] using wordTrace_append hprefix tailTrace_4096771
  have hstable : (prefixWord ++ tailWord_4096771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096771).length < 2 ^ (prefixWord ++ tailWord_4096771).sum := by decide
  have hdescent : baseEnd_4096771 < baseStart_4096771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096818 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2]
def baseStart_4096818 : Nat := 118140960795 + 4096818 * 2 ^ 59
def prefixEnd_4096818 : Nat := 4983230072969 + 3 ^ 40 * 4096818 * 2
def baseEnd_4096818 : Nat := 2103636787991457414434083

theorem tailTrace_4096818 : CollatzResearch.WordTrace tailWord_4096818 prefixEnd_4096818 2103636787991457414434083 := by
  unfold tailWord_4096818
  simp only [CollatzResearch.WordTrace]
  refine ⟨37355807017983885413768777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99615485381290361103383405 37355807017983885413768777)
  ·
    refine ⟨28016855263487914060326583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37355807017983885413768777 28016855263487914060326583)
    ·
      refine ⟨42025282895231871090489875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28016855263487914060326583 42025282895231871090489875)
      ·
        refine ⟨63037924342847806635734813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42025282895231871090489875 63037924342847806635734813)
        ·
          refine ⟨23639221628567927488400555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63037924342847806635734813 23639221628567927488400555)
          ·
            refine ⟨35458832442851891232600833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23639221628567927488400555 35458832442851891232600833)
            ·
              refine ⟨26594124332138918424450625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35458832442851891232600833 26594124332138918424450625)
              ·
                refine ⟨19945593249104188818337969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26594124332138918424450625 19945593249104188818337969)
                ·
                  refine ⟨14959194936828141613753477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19945593249104188818337969 14959194936828141613753477)
                  ·
                    refine ⟨2804849050655276552578777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14959194936828141613753477 2804849050655276552578777)
                    ·
                      refine ⟨2103636787991457414434083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2804849050655276552578777 2103636787991457414434083)
                      ·
                        rfl

theorem cell23_4096818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_4096818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096818 prefixEnd_4096818 := by exact prefixLift 4096818
  have htrace : WordTrace (prefixWord ++ tailWord_4096818) baseStart_4096818 baseEnd_4096818 := by
    simpa [prefixWord, tailWord_4096818, baseEnd_4096818] using wordTrace_append hprefix tailTrace_4096818
  have hstable : (prefixWord ++ tailWord_4096818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096818).length < 2 ^ (prefixWord ++ tailWord_4096818).sum := by decide
  have hdescent : baseEnd_4096818 < baseStart_4096818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096841 : List Nat := [1, 2, 1, 1, 2, 5, 2, 3, 6]
def baseStart_4096841 : Nat := 118140960795 + 4096841 * 2 ^ 59
def prefixEnd_4096841 : Nat := 4983230072969 + 3 ^ 40 * 4096841 * 2
def baseEnd_4096841 : Nat := 233738733116278980494053

theorem tailTrace_4096841 : CollatzResearch.WordTrace tailWord_4096841 prefixEnd_4096841 233738733116278980494053 := by
  unfold tailWord_4096841
  simp only [CollatzResearch.WordTrace]
  refine ⟨149424066950852216583162377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99616044633901477722108251 149424066950852216583162377)
  ·
    refine ⟨112068050213139162437371783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149424066950852216583162377 112068050213139162437371783)
    ·
      refine ⟨168102075319708743656057675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112068050213139162437371783 168102075319708743656057675)
      ·
        refine ⟨252153112979563115484086513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168102075319708743656057675 252153112979563115484086513)
        ·
          refine ⟨189114834734672336613064885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252153112979563115484086513 189114834734672336613064885)
          ·
            refine ⟨17729515756375531557474833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189114834734672336613064885 17729515756375531557474833)
            ·
              refine ⟨13297136817281648668106125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17729515756375531557474833 13297136817281648668106125)
              ·
                refine ⟨4986426306480618250539797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13297136817281648668106125 4986426306480618250539797)
                ·
                  refine ⟨233738733116278980494053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4986426306480618250539797 233738733116278980494053)
                  ·
                    rfl

theorem cell23_4096841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 6].length) (baseStart_4096841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096841 prefixEnd_4096841 := by exact prefixLift 4096841
  have htrace : WordTrace (prefixWord ++ tailWord_4096841) baseStart_4096841 baseEnd_4096841 := by
    simpa [prefixWord, tailWord_4096841, baseEnd_4096841] using wordTrace_append hprefix tailTrace_4096841
  have hstable : (prefixWord ++ tailWord_4096841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096841).length < 2 ^ (prefixWord ++ tailWord_4096841).sum := by decide
  have hdescent : baseEnd_4096841 < baseStart_4096841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096852 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 2, 1, 4]
def baseStart_4096852 : Nat := 118140960795 + 4096852 * 2 ^ 59
def prefixEnd_4096852 : Nat := 4983230072969 + 3 ^ 40 * 4096852 * 2
def baseEnd_4096852 : Nat := 2103654246333710281408927

theorem tailTrace_4096852 : CollatzResearch.WordTrace tailWord_4096852 prefixEnd_4096852 2103654246333710281408927 := by
  unfold tailWord_4096852
  simp only [CollatzResearch.WordTrace]
  refine ⟨74712234076906182730906405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99616312102541576974541873 74712234076906182730906405)
  ·
    refine ⟨14008543889419909262044951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74712234076906182730906405 14008543889419909262044951)
    ·
      refine ⟨21012815834129863893067427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14008543889419909262044951 21012815834129863893067427)
      ·
        refine ⟨31519223751194795839601141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21012815834129863893067427 31519223751194795839601141)
        ·
          refine ⟨2954927226674512109962607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31519223751194795839601141 2954927226674512109962607)
          ·
            refine ⟨4432390840011768164943911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954927226674512109962607 4432390840011768164943911)
            ·
              refine ⟨6648586260017652247415867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4432390840011768164943911 6648586260017652247415867)
              ·
                refine ⟨9972879390026478371123801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6648586260017652247415867 9972879390026478371123801)
                ·
                  refine ⟨7479659542519858778342851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9972879390026478371123801 7479659542519858778342851)
                  ·
                    refine ⟨11219489313779788167514277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7479659542519858778342851 11219489313779788167514277)
                    ·
                      refine ⟨2103654246333710281408927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11219489313779788167514277 2103654246333710281408927)
                      ·
                        rfl

theorem cell23_4096852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_4096852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096852 prefixEnd_4096852 := by exact prefixLift 4096852
  have htrace : WordTrace (prefixWord ++ tailWord_4096852) baseStart_4096852 baseEnd_4096852 := by
    simpa [prefixWord, tailWord_4096852, baseEnd_4096852] using wordTrace_append hprefix tailTrace_4096852
  have hstable : (prefixWord ++ tailWord_4096852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096852).length < 2 ^ (prefixWord ++ tailWord_4096852).sum := by decide
  have hdescent : baseEnd_4096852 < baseStart_4096852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096855 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 2, 2, 3]
def baseStart_4096855 : Nat := 118140960795 + 4096855 * 2 ^ 59
def prefixEnd_4096855 : Nat := 4983230072969 + 3 ^ 40 * 4096855 * 2
def baseEnd_4096855 : Nat := 2103655786775673769671413

theorem tailTrace_4096855 : CollatzResearch.WordTrace tailWord_4096855 prefixEnd_4096855 2103655786775673769671413 := by
  unfold tailWord_4096855
  simp only [CollatzResearch.WordTrace]
  refine ⟨149424577572801496974172019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99616385048534331316114679 149424577572801496974172019)
  ·
    refine ⟨224136866359202245461258029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149424577572801496974172019 224136866359202245461258029)
    ·
      refine ⟨84051324884700842047971761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224136866359202245461258029 84051324884700842047971761)
      ·
        refine ⟨63038493663525631535978821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84051324884700842047971761 63038493663525631535978821)
        ·
          refine ⟨11819717561911055912996029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63038493663525631535978821 11819717561911055912996029)
          ·
            refine ⟨4432394085716645967373511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11819717561911055912996029 4432394085716645967373511)
            ·
              refine ⟨6648591128574968951060267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4432394085716645967373511 6648591128574968951060267)
              ·
                refine ⟨9972886692862453426590401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6648591128574968951060267 9972886692862453426590401)
                ·
                  refine ⟨7479665019646840069942801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9972886692862453426590401 7479665019646840069942801)
                  ·
                    refine ⟨5609748764735130052457101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7479665019646840069942801 5609748764735130052457101)
                    ·
                      refine ⟨2103655786775673769671413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5609748764735130052457101 2103655786775673769671413)
                      ·
                        rfl

theorem cell23_4096855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_4096855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096855 prefixEnd_4096855 := by exact prefixLift 4096855
  have htrace : WordTrace (prefixWord ++ tailWord_4096855) baseStart_4096855 baseEnd_4096855 := by
    simpa [prefixWord, tailWord_4096855, baseEnd_4096855] using wordTrace_append hprefix tailTrace_4096855
  have hstable : (prefixWord ++ tailWord_4096855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096855).length < 2 ^ (prefixWord ++ tailWord_4096855).sum := by decide
  have hdescent : baseEnd_4096855 < baseStart_4096855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096885 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_4096885 : Nat := 118140960795 + 4096885 * 2 ^ 59
def prefixEnd_4096885 : Nat := 4983230072969 + 3 ^ 40 * 4096885 * 2
def baseEnd_4096885 : Nat := 2103671191195308652296275

theorem tailTrace_4096885 : CollatzResearch.WordTrace tailWord_4096885 prefixEnd_4096885 2103671191195308652296275 := by
  unfold tailWord_4096885
  simp only [CollatzResearch.WordTrace]
  refine ⟨149425671762692812097764109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99617114508461874731842739 149425671762692812097764109)
  ·
    refine ⟨56034626911009804536661541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149425671762692812097764109 56034626911009804536661541)
    ·
      refine ⟨10506492545814338350624039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56034626911009804536661541 10506492545814338350624039)
      ·
        refine ⟨15759738818721507525936059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10506492545814338350624039 15759738818721507525936059)
        ·
          refine ⟨23639608228082261288904089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15759738818721507525936059 23639608228082261288904089)
          ·
            refine ⟨17729706171061695966678067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23639608228082261288904089 17729706171061695966678067)
            ·
              refine ⟨26594559256592543950017101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17729706171061695966678067 26594559256592543950017101)
              ·
                refine ⟨9972959721222203981256413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26594559256592543950017101 9972959721222203981256413)
                ·
                  refine ⟨3739859895458326492971155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9972959721222203981256413 3739859895458326492971155)
                  ·
                    refine ⟨5609789843187489739456733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3739859895458326492971155 5609789843187489739456733)
                    ·
                      refine ⟨2103671191195308652296275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5609789843187489739456733 2103671191195308652296275)
                      ·
                        rfl

theorem cell23_4096885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_4096885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096885 prefixEnd_4096885 := by exact prefixLift 4096885
  have htrace : WordTrace (prefixWord ++ tailWord_4096885) baseStart_4096885 baseEnd_4096885 := by
    simpa [prefixWord, tailWord_4096885, baseEnd_4096885] using wordTrace_append hprefix tailTrace_4096885
  have hstable : (prefixWord ++ tailWord_4096885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096885).length < 2 ^ (prefixWord ++ tailWord_4096885).sum := by decide
  have hdescent : baseEnd_4096885 < baseStart_4096885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096891 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 4]
def baseStart_4096891 : Nat := 118140960795 + 4096891 * 2 ^ 59
def prefixEnd_4096891 : Nat := 4983230072969 + 3 ^ 40 * 4096891 * 2
def baseEnd_4096891 : Nat := 2103674272079235628821247

theorem tailTrace_4096891 : CollatzResearch.WordTrace tailWord_4096891 prefixEnd_4096891 2103674272079235628821247 := by
  unfold tailWord_4096891
  simp only [CollatzResearch.WordTrace]
  refine ⟨149425890600671075122482527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99617260400447383414988351 149425890600671075122482527)
  ·
    refine ⟨224138835901006612683723791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149425890600671075122482527 224138835901006612683723791)
    ·
      refine ⟨336208253851509919025585687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224138835901006612683723791 336208253851509919025585687)
      ·
        refine ⟨504312380777264878538378531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336208253851509919025585687 504312380777264878538378531)
        ·
          refine ⟨756468571165897317807567797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504312380777264878538378531 756468571165897317807567797)
          ·
            refine ⟨70918928546802873544459481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 756468571165897317807567797 70918928546802873544459481)
            ·
              refine ⟨53189196410102155158344611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70918928546802873544459481 53189196410102155158344611)
              ·
                refine ⟨79783794615153232737516917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53189196410102155158344611 79783794615153232737516917)
                ·
                  refine ⟨7479730745170615569142211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79783794615153232737516917 7479730745170615569142211)
                  ·
                    refine ⟨11219596117755923353713317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7479730745170615569142211 11219596117755923353713317)
                    ·
                      refine ⟨2103674272079235628821247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11219596117755923353713317 2103674272079235628821247)
                      ·
                        rfl

theorem cell23_4096891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 4].length) (baseStart_4096891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096891 prefixEnd_4096891 := by exact prefixLift 4096891
  have htrace : WordTrace (prefixWord ++ tailWord_4096891) baseStart_4096891 baseEnd_4096891 := by
    simpa [prefixWord, tailWord_4096891, baseEnd_4096891] using wordTrace_append hprefix tailTrace_4096891
  have hstable : (prefixWord ++ tailWord_4096891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096891).length < 2 ^ (prefixWord ++ tailWord_4096891).sum := by decide
  have hdescent : baseEnd_4096891 < baseStart_4096891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096908 : List Nat := [2, 2, 1, 2, 1, 2, 3, 4, 1, 1, 4]
def baseStart_4096908 : Nat := 118140960795 + 4096908 * 2 ^ 59
def prefixEnd_4096908 : Nat := 4983230072969 + 3 ^ 40 * 4096908 * 2
def baseEnd_4096908 : Nat := 2103683001250362062308669

theorem tailTrace_4096908 : CollatzResearch.WordTrace tailWord_4096908 prefixEnd_4096908 2103683001250362062308669 := by
  unfold tailWord_4096908
  simp only [CollatzResearch.WordTrace]
  refine ⟨74713255320804743512925689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99617673761072991350567585 74713255320804743512925689)
  ·
    refine ⟨56034941490603557634694267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74713255320804743512925689 56034941490603557634694267)
    ·
      refine ⟨84052412235905336452041401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56034941490603557634694267 84052412235905336452041401)
      ·
        refine ⟨63039309176929002339031051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84052412235905336452041401 63039309176929002339031051)
        ·
          refine ⟨94558963765393503508546577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63039309176929002339031051 94558963765393503508546577)
          ·
            refine ⟨70919222824045127631409933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94558963765393503508546577 70919222824045127631409933)
            ·
              refine ⟨26594708559016922861778725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70919222824045127631409933 26594708559016922861778725)
              ·
                refine ⟨4986507854815673036583511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26594708559016922861778725 4986507854815673036583511)
                ·
                  refine ⟨7479761782223509554875267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4986507854815673036583511 7479761782223509554875267)
                  ·
                    refine ⟨11219642673335264332312901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7479761782223509554875267 11219642673335264332312901)
                    ·
                      refine ⟨2103683001250362062308669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11219642673335264332312901 2103683001250362062308669)
                      ·
                        rfl

theorem cell23_4096908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_4096908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096908 prefixEnd_4096908 := by exact prefixLift 4096908
  have htrace : WordTrace (prefixWord ++ tailWord_4096908) baseStart_4096908 baseEnd_4096908 := by
    simpa [prefixWord, tailWord_4096908, baseEnd_4096908] using wordTrace_append hprefix tailTrace_4096908
  have hstable : (prefixWord ++ tailWord_4096908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096908).length < 2 ^ (prefixWord ++ tailWord_4096908).sum := by decide
  have hdescent : baseEnd_4096908 < baseStart_4096908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096921 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 3, 2, 4]
def baseStart_4096921 : Nat := 118140960795 + 4096921 * 2 ^ 59
def prefixEnd_4096921 : Nat := 4983230072969 + 3 ^ 40 * 4096921 * 2
def baseEnd_4096921 : Nat := 2103689676498870511446109

theorem tailTrace_4096921 : CollatzResearch.WordTrace tailWord_4096921 prefixEnd_4096921 2103689676498870511446109 := by
  unfold tailWord_4096921
  simp only [CollatzResearch.WordTrace]
  refine ⟨149426984790562390246074617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99617989860374926830716411 149426984790562390246074617)
  ·
    refine ⟨112070238592921792684555963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149426984790562390246074617 112070238592921792684555963)
    ·
      refine ⟨168105357889382689026833945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112070238592921792684555963 168105357889382689026833945)
      ·
        refine ⟨126079018417037016770125459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168105357889382689026833945 126079018417037016770125459)
        ·
          refine ⟨189118527625555525155188189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126079018417037016770125459 189118527625555525155188189)
          ·
            refine ⟨70919447859583321933195571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189118527625555525155188189 70919447859583321933195571)
            ·
              refine ⟨106379171789374982899793357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70919447859583321933195571 106379171789374982899793357)
              ·
                refine ⟨39892189421015618587422509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106379171789374982899793357 39892189421015618587422509)
                ·
                  refine ⟨14959571032880856970283441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39892189421015618587422509 14959571032880856970283441)
                  ·
                    refine ⟨11219678274660642727712581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14959571032880856970283441 11219678274660642727712581)
                    ·
                      refine ⟨2103689676498870511446109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11219678274660642727712581 2103689676498870511446109)
                      ·
                        rfl

theorem cell23_4096921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_4096921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096921 prefixEnd_4096921 := by exact prefixLift 4096921
  have htrace : WordTrace (prefixWord ++ tailWord_4096921) baseStart_4096921 baseEnd_4096921 := by
    simpa [prefixWord, tailWord_4096921, baseEnd_4096921] using wordTrace_append hprefix tailTrace_4096921
  have hstable : (prefixWord ++ tailWord_4096921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096921).length < 2 ^ (prefixWord ++ tailWord_4096921).sum := by decide
  have hdescent : baseEnd_4096921 < baseStart_4096921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4096952 : List Nat := [2, 1, 2, 1, 2, 6, 2, 1, 2, 4]
def baseStart_4096952 : Nat := 118140960795 + 4096952 * 2 ^ 59
def prefixEnd_4096952 : Nat := 4983230072969 + 3 ^ 40 * 4096952 * 2
def baseEnd_4096952 : Nat := 701235198133053296719489

theorem tailTrace_4096952 : CollatzResearch.WordTrace tailWord_4096952 prefixEnd_4096952 701235198133053296719489 := by
  unfold tailWord_4096952
  simp only [CollatzResearch.WordTrace]
  refine ⟨74714057726725041270226555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99618743635633388360302073 74714057726725041270226555)
  ·
    refine ⟨112071086590087561905339833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74714057726725041270226555 112071086590087561905339833)
    ·
      refine ⟨84053314942565671429004875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112071086590087561905339833 84053314942565671429004875)
      ·
        refine ⟨126079972413848507143507313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84053314942565671429004875 126079972413848507143507313)
        ·
          refine ⟨94559979310386380357630485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126079972413848507143507313 94559979310386380357630485)
          ·
            refine ⟨4432499030174361579263929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94559979310386380357630485 4432499030174361579263929)
            ·
              refine ⟨3324374272630771184447947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4432499030174361579263929 3324374272630771184447947)
              ·
                refine ⟨4986561408946156776671921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3324374272630771184447947 4986561408946156776671921)
                ·
                  refine ⟨3739921056709617582503941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4986561408946156776671921 3739921056709617582503941)
                  ·
                    refine ⟨701235198133053296719489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3739921056709617582503941 701235198133053296719489)
                    ·
                      rfl

theorem cell23_4096952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_4096952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4096952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4096952 prefixEnd_4096952 := by exact prefixLift 4096952
  have htrace : WordTrace (prefixWord ++ tailWord_4096952) baseStart_4096952 baseEnd_4096952 := by
    simpa [prefixWord, tailWord_4096952, baseEnd_4096952] using wordTrace_append hprefix tailTrace_4096952
  have hstable : (prefixWord ++ tailWord_4096952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4096952).length < 2 ^ (prefixWord ++ tailWord_4096952).sum := by decide
  have hdescent : baseEnd_4096952 < baseStart_4096952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4096952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097055 : List Nat := [1, 1, 2, 4, 1, 3, 2, 4, 5]
def baseStart_4097055 : Nat := 118140960795 + 4097055 * 2 ^ 59
def prefixEnd_4097055 : Nat := 4983230072969 + 3 ^ 40 * 4097055 * 2
def baseEnd_4097055 : Nat := 233750942545174776352277

theorem tailTrace_4097055 : CollatzResearch.WordTrace tailWord_4097055 prefixEnd_4097055 233750942545174776352277 := by
  unfold tailWord_4097055
  simp only [CollatzResearch.WordTrace]
  refine ⟨149431872172076931131452619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99621248114717954087635079 149431872172076931131452619)
  ·
    refine ⟨224147808258115396697178929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149431872172076931131452619 224147808258115396697178929)
    ·
      refine ⟨168110856193586547522884197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224147808258115396697178929 168110856193586547522884197)
      ·
        refine ⟨31520785536297477660540787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168110856193586547522884197 31520785536297477660540787)
        ·
          refine ⟨47281178304446216490811181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31520785536297477660540787 47281178304446216490811181)
          ·
            refine ⟨17730441864167331184054193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47281178304446216490811181 17730441864167331184054193)
            ·
              refine ⟨13297831398125498388040645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17730441864167331184054193 13297831398125498388040645)
              ·
                refine ⟨2493343387148530947757621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13297831398125498388040645 2493343387148530947757621)
                ·
                  refine ⟨233750942545174776352277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2493343387148530947757621 233750942545174776352277)
                  ·
                    rfl

theorem cell23_4097055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 5].length) (baseStart_4097055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097055 prefixEnd_4097055 := by exact prefixLift 4097055
  have htrace : WordTrace (prefixWord ++ tailWord_4097055) baseStart_4097055 baseEnd_4097055 := by
    simpa [prefixWord, tailWord_4097055, baseEnd_4097055] using wordTrace_append hprefix tailTrace_4097055
  have hstable : (prefixWord ++ tailWord_4097055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097055).length < 2 ^ (prefixWord ++ tailWord_4097055).sum := by decide
  have hdescent : baseEnd_4097055 < baseStart_4097055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097066 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_4097066 : Nat := 118140960795 + 4097066 * 2 ^ 59
def prefixEnd_4097066 : Nat := 4983230072969 + 3 ^ 40 * 4097066 * 2
def baseEnd_4097066 : Nat := 2103764131193772444132943

theorem tailTrace_4097066 : CollatzResearch.WordTrace tailWord_4097066 prefixEnd_4097066 2103764131193772444132943 := by
  unfold tailWord_4097066
  simp only [CollatzResearch.WordTrace]
  refine ⟨37358068343759270002525763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99621515583358053340068701 37358068343759270002525763)
  ·
    refine ⟨56037102515638905003788645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37358068343759270002525763 56037102515638905003788645)
    ·
      refine ⟨10506956721682294688210371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56037102515638905003788645 10506956721682294688210371)
      ·
        refine ⟨15760435082523442032315557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10506956721682294688210371 15760435082523442032315557)
        ·
          refine ⟨2955081577973145381059167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15760435082523442032315557 2955081577973145381059167)
          ·
            refine ⟨4432622366959718071588751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2955081577973145381059167 4432622366959718071588751)
            ·
              refine ⟨6648933550439577107383127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4432622366959718071588751 6648933550439577107383127)
              ·
                refine ⟨9973400325659365661074691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6648933550439577107383127 9973400325659365661074691)
                ·
                  refine ⟨14960100488489048491612037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9973400325659365661074691 14960100488489048491612037)
                  ·
                    refine ⟨2805018841591696592177257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14960100488489048491612037 2805018841591696592177257)
                    ·
                      refine ⟨2103764131193772444132943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2805018841591696592177257 2103764131193772444132943)
                      ·
                        rfl

theorem cell23_4097066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_4097066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097066 prefixEnd_4097066 := by exact prefixLift 4097066
  have htrace : WordTrace (prefixWord ++ tailWord_4097066) baseStart_4097066 baseEnd_4097066 := by
    simpa [prefixWord, tailWord_4097066, baseEnd_4097066] using wordTrace_append hprefix tailTrace_4097066
  have hstable : (prefixWord ++ tailWord_4097066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097066).length < 2 ^ (prefixWord ++ tailWord_4097066).sum := by decide
  have hdescent : baseEnd_4097066 < baseStart_4097066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097088 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 4]
def baseStart_4097088 : Nat := 118140960795 + 4097088 * 2 ^ 59
def prefixEnd_4097088 : Nat := 4983230072969 + 3 ^ 40 * 4097088 * 2
def baseEnd_4097088 : Nat := 2103775427768171358057841

theorem tailTrace_4097088 : CollatzResearch.WordTrace tailWord_4097088 prefixEnd_4097088 2103775427768171358057841 := by
  unfold tailWord_4097088
  simp only [CollatzResearch.WordTrace]
  refine ⟨74716537890478688883701959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99622050520638251844935945 74716537890478688883701959)
  ·
    refine ⟨112074806835718033325552939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74716537890478688883701959 112074806835718033325552939)
    ·
      refine ⟨168112210253577049988329409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112074806835718033325552939 168112210253577049988329409)
      ·
        refine ⟨126084157690182787491247057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168112210253577049988329409 126084157690182787491247057)
        ·
          refine ⟨94563118267637090618435293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126084157690182787491247057 94563118267637090618435293)
          ·
            refine ⟨35461169350363908981913235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94563118267637090618435293 35461169350363908981913235)
            ·
              refine ⟨53191754025545863472869853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35461169350363908981913235 53191754025545863472869853)
              ·
                refine ⟨19946907759579698802326195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53191754025545863472869853 19946907759579698802326195)
                ·
                  refine ⟨29920361639369548203489293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19946907759579698802326195 29920361639369548203489293)
                  ·
                    refine ⟨11220135614763580576308485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29920361639369548203489293 11220135614763580576308485)
                    ·
                      refine ⟨2103775427768171358057841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11220135614763580576308485 2103775427768171358057841)
                      ·
                        rfl

theorem cell23_4097088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_4097088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097088 prefixEnd_4097088 := by exact prefixLift 4097088
  have htrace : WordTrace (prefixWord ++ tailWord_4097088) baseStart_4097088 baseEnd_4097088 := by
    simpa [prefixWord, tailWord_4097088, baseEnd_4097088] using wordTrace_append hprefix tailTrace_4097088
  have hstable : (prefixWord ++ tailWord_4097088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097088).length < 2 ^ (prefixWord ++ tailWord_4097088).sum := by decide
  have hdescent : baseEnd_4097088 < baseStart_4097088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097089 : List Nat := [1, 2, 5, 1, 3, 2, 1, 3, 5]
def baseStart_4097089 : Nat := 118140960795 + 4097089 * 2 ^ 59
def prefixEnd_4097089 : Nat := 4983230072969 + 3 ^ 40 * 4097089 * 2
def baseEnd_4097089 : Nat := 233752882360980650460593

theorem tailTrace_4097089 : CollatzResearch.WordTrace tailWord_4097089 prefixEnd_4097089 233752882360980650460593 := by
  unfold tailWord_4097089
  simp only [CollatzResearch.WordTrace]
  refine ⟨149433112253953754938190321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99622074835969169958793547 149433112253953754938190321)
  ·
    refine ⟨112074834190465316203642741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149433112253953754938190321 112074834190465316203642741)
    ·
      refine ⟨10507015705356123394091507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112074834190465316203642741 10507015705356123394091507)
      ·
        refine ⟨15760523558034185091137261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10507015705356123394091507 15760523558034185091137261)
        ·
          refine ⟨5910196334262819409176473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15760523558034185091137261 5910196334262819409176473)
          ·
            refine ⟨4432647250697114556882355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5910196334262819409176473 4432647250697114556882355)
            ·
              refine ⟨6648970876045671835323533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4432647250697114556882355 6648970876045671835323533)
              ·
                refine ⟨2493364078517126938246325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6648970876045671835323533 2493364078517126938246325)
                ·
                  refine ⟨233752882360980650460593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2493364078517126938246325 233752882360980650460593)
                  ·
                    rfl

theorem cell23_4097089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 5].length) (baseStart_4097089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097089 prefixEnd_4097089 := by exact prefixLift 4097089
  have htrace : WordTrace (prefixWord ++ tailWord_4097089) baseStart_4097089 baseEnd_4097089 := by
    simpa [prefixWord, tailWord_4097089, baseEnd_4097089] using wordTrace_append hprefix tailTrace_4097089
  have hstable : (prefixWord ++ tailWord_4097089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097089).length < 2 ^ (prefixWord ++ tailWord_4097089).sum := by decide
  have hdescent : baseEnd_4097089 < baseStart_4097089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097105 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 4, 4, 2]
def baseStart_4097105 : Nat := 118140960795 + 4097105 * 2 ^ 59
def prefixEnd_4097105 : Nat := 4983230072969 + 3 ^ 40 * 4097105 * 2
def baseEnd_4097105 : Nat := 2103784156939297791545263

theorem tailTrace_4097105 : CollatzResearch.WordTrace tailWord_4097105 prefixEnd_4097105 2103784156939297791545263 := by
  unfold tailWord_4097105
  simp only [CollatzResearch.WordTrace]
  refine ⟨149433695821895789670772769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99622463881263859780515179 149433695821895789670772769)
  ·
    refine ⟨112075271866421842253079577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149433695821895789670772769 112075271866421842253079577)
    ·
      refine ⟨84056453899816381689809683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112075271866421842253079577 84056453899816381689809683)
      ·
        refine ⟨126084680849724572534714525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84056453899816381689809683 126084680849724572534714525)
        ·
          refine ⟨47281755318646714700517947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126084680849724572534714525 47281755318646714700517947)
          ·
            refine ⟨70922632977970072050776921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47281755318646714700517947 70922632977970072050776921)
            ·
              refine ⟨53191974733477554038082691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70922632977970072050776921 53191974733477554038082691)
              ·
                refine ⟨79787962100216331057124037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53191974733477554038082691 79787962100216331057124037)
                ·
                  refine ⟨14960242893790562073210757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79787962100216331057124037 14960242893790562073210757)
                  ·
                    refine ⟨2805045542585730388727017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14960242893790562073210757 2805045542585730388727017)
                    ·
                      refine ⟨2103784156939297791545263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2805045542585730388727017 2103784156939297791545263)
                      ·
                        rfl

theorem cell23_4097105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 4, 2].length) (baseStart_4097105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097105 prefixEnd_4097105 := by exact prefixLift 4097105
  have htrace : WordTrace (prefixWord ++ tailWord_4097105) baseStart_4097105 baseEnd_4097105 := by
    simpa [prefixWord, tailWord_4097105, baseEnd_4097105] using wordTrace_append hprefix tailTrace_4097105
  have hstable : (prefixWord ++ tailWord_4097105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097105).length < 2 ^ (prefixWord ++ tailWord_4097105).sum := by decide
  have hdescent : baseEnd_4097105 < baseStart_4097105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097125 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 4, 2, 3]
def baseStart_4097125 : Nat := 118140960795 + 4097125 * 2 ^ 59
def prefixEnd_4097125 : Nat := 4983230072969 + 3 ^ 40 * 4097125 * 2
def baseEnd_4097125 : Nat := 2103794426552387713295171

theorem tailTrace_4097125 : CollatzResearch.WordTrace tailWord_4097125 prefixEnd_4097125 2103794426552387713295171 := by
  unfold tailWord_4097125
  simp only [CollatzResearch.WordTrace]
  refine ⟨149434425281823333086500829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99622950187882222057667219 149434425281823333086500829)
  ·
    refine ⟨56037909480683749907437811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149434425281823333086500829 56037909480683749907437811)
    ·
      refine ⟨84056864221025624861156717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56037909480683749907437811 84056864221025624861156717)
      ·
        refine ⟨31521324082884609322933769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84056864221025624861156717 31521324082884609322933769)
        ·
          refine ⟨23640993062163456992200327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31521324082884609322933769 23640993062163456992200327)
          ·
            refine ⟨35461489593245185488300491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23640993062163456992200327 35461489593245185488300491)
            ·
              refine ⟨53192234389867778232450737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35461489593245185488300491 53192234389867778232450737)
              ·
                refine ⟨39894175792400833674338053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53192234389867778232450737 39894175792400833674338053)
                ·
                  refine ⟨7480157961075156313938385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39894175792400833674338053 7480157961075156313938385)
                  ·
                    refine ⟨5610118470806367235453789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7480157961075156313938385 5610118470806367235453789)
                    ·
                      refine ⟨2103794426552387713295171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5610118470806367235453789 2103794426552387713295171)
                      ·
                        rfl

theorem cell23_4097125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_4097125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097125 prefixEnd_4097125 := by exact prefixLift 4097125
  have htrace : WordTrace (prefixWord ++ tailWord_4097125) baseStart_4097125 baseEnd_4097125 := by
    simpa [prefixWord, tailWord_4097125, baseEnd_4097125] using wordTrace_append hprefix tailTrace_4097125
  have hstable : (prefixWord ++ tailWord_4097125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097125).length < 2 ^ (prefixWord ++ tailWord_4097125).sum := by decide
  have hdescent : baseEnd_4097125 < baseStart_4097125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097166 : List Nat := [4, 1, 1, 3, 2, 1, 4, 2, 1, 4]
def baseStart_4097166 : Nat := 118140960795 + 4097166 * 2 ^ 59
def prefixEnd_4097166 : Nat := 4983230072969 + 3 ^ 40 * 4097166 * 2
def baseEnd_4097166 : Nat := 701271826419740684294161

theorem tailTrace_4097166 : CollatzResearch.WordTrace tailWord_4097166 prefixEnd_4097166 701271826419740684294161 := by
  unfold tailWord_4097166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18679490084334349636092919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99623947116449864725828901 18679490084334349636092919)
  ·
    refine ⟨28019235126501524454139379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18679490084334349636092919 28019235126501524454139379)
    ·
      refine ⟨42028852689752286681209069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28019235126501524454139379 42028852689752286681209069)
      ·
        refine ⟨15760819758657107505453401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42028852689752286681209069 15760819758657107505453401)
        ·
          refine ⟨11820614818992830629090051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15760819758657107505453401 11820614818992830629090051)
          ·
            refine ⟨17730922228489245943635077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11820614818992830629090051 17730922228489245943635077)
            ·
              refine ⟨3324547917841733614431577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17730922228489245943635077 3324547917841733614431577)
              ·
                refine ⟨2493410938381300210823683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3324547917841733614431577 2493410938381300210823683)
                ·
                  refine ⟨3740116407571950316235525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2493410938381300210823683 3740116407571950316235525)
                  ·
                    refine ⟨701271826419740684294161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3740116407571950316235525 701271826419740684294161)
                    ·
                      rfl

theorem cell23_4097166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_4097166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097166 prefixEnd_4097166 := by exact prefixLift 4097166
  have htrace : WordTrace (prefixWord ++ tailWord_4097166) baseStart_4097166 baseEnd_4097166 := by
    simpa [prefixWord, tailWord_4097166, baseEnd_4097166] using wordTrace_append hprefix tailTrace_4097166
  have hstable : (prefixWord ++ tailWord_4097166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097166).length < 2 ^ (prefixWord ++ tailWord_4097166).sum := by decide
  have hdescent : baseEnd_4097166 < baseStart_4097166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097175 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 3, 5]
def baseStart_4097175 : Nat := 118140960795 + 4097175 * 2 ^ 59
def prefixEnd_4097175 : Nat := 4983230072969 + 3 ^ 40 * 4097175 * 2
def baseEnd_4097175 : Nat := 701273366861704172556647

theorem tailTrace_4097175 : CollatzResearch.WordTrace tailWord_4097175 prefixEnd_4097175 701273366861704172556647 := by
  unfold tailWord_4097175
  simp only [CollatzResearch.WordTrace]
  refine ⟨149436248931642191625820979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99624165954428127750547319 149436248931642191625820979)
  ·
    refine ⟨224154373397463287438731469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149436248931642191625820979 224154373397463287438731469)
    ·
      refine ⟨84057890024048732789524301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224154373397463287438731469 84057890024048732789524301)
      ·
        refine ⟨31521708759018274796071613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84057890024048732789524301 31521708759018274796071613)
        ·
          refine ⟨11820640784631853048526855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31521708759018274796071613 11820640784631853048526855)
          ·
            refine ⟨17730961176947779572790283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11820640784631853048526855 17730961176947779572790283)
            ·
              refine ⟨26596441765421669359185425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17730961176947779572790283 26596441765421669359185425)
              ·
                refine ⟨19947331324066252019389069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26596441765421669359185425 19947331324066252019389069)
                ·
                  refine ⟨7480249246524844507270901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19947331324066252019389069 7480249246524844507270901)
                  ·
                    refine ⟨701273366861704172556647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7480249246524844507270901 701273366861704172556647)
                    ·
                      rfl

theorem cell23_4097175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_4097175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097175 prefixEnd_4097175 := by exact prefixLift 4097175
  have htrace : WordTrace (prefixWord ++ tailWord_4097175) baseStart_4097175 baseEnd_4097175 := by
    simpa [prefixWord, tailWord_4097175, baseEnd_4097175] using wordTrace_append hprefix tailTrace_4097175
  have hstable : (prefixWord ++ tailWord_4097175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097175).length < 2 ^ (prefixWord ++ tailWord_4097175).sum := by decide
  have hdescent : baseEnd_4097175 < baseStart_4097175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097209 : List Nat := [1, 2, 1, 4, 1, 5, 2, 1, 1, 5]
def baseStart_4097209 : Nat := 118140960795 + 4097209 * 2 ^ 59
def prefixEnd_4097209 : Nat := 4983230072969 + 3 ^ 40 * 4097209 * 2
def baseEnd_4097209 : Nat := 701279186309121794881595

theorem tailTrace_4097209 : CollatzResearch.WordTrace tailWord_4097209 prefixEnd_4097209 701279186309121794881595 := by
  unfold tailWord_4097209
  simp only [CollatzResearch.WordTrace]
  refine ⟨149437489013519015432558681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99624992675679343621705787 149437489013519015432558681)
  ·
    refine ⟨112078116760139261574419011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149437489013519015432558681 112078116760139261574419011)
    ·
      refine ⟨168117175140208892361628517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112078116760139261574419011 168117175140208892361628517)
      ·
        refine ⟨31521970338789167317805347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168117175140208892361628517 31521970338789167317805347)
        ·
          refine ⟨47282955508183750976708021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31521970338789167317805347 47282955508183750976708021)
          ·
            refine ⟨4432777078892226654066377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47282955508183750976708021 4432777078892226654066377)
            ·
              refine ⟨3324582809169169990549783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4432777078892226654066377 3324582809169169990549783)
              ·
                refine ⟨4986874213753754985824675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3324582809169169990549783 4986874213753754985824675)
                ·
                  refine ⟨7480311320630632478737013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4986874213753754985824675 7480311320630632478737013)
                  ·
                    refine ⟨701279186309121794881595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7480311320630632478737013 701279186309121794881595)
                    ·
                      rfl

theorem cell23_4097209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 1, 5].length) (baseStart_4097209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097209 prefixEnd_4097209 := by exact prefixLift 4097209
  have htrace : WordTrace (prefixWord ++ tailWord_4097209) baseStart_4097209 baseEnd_4097209 := by
    simpa [prefixWord, tailWord_4097209, baseEnd_4097209] using wordTrace_append hprefix tailTrace_4097209
  have hstable : (prefixWord ++ tailWord_4097209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097209).length < 2 ^ (prefixWord ++ tailWord_4097209).sum := by decide
  have hdescent : baseEnd_4097209 < baseStart_4097209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097249 : List Nat := [1, 2, 3, 1, 3, 3, 2, 2, 1, 2, 3]
def baseStart_4097249 : Nat := 118140960795 + 4097249 * 2 ^ 59
def prefixEnd_4097249 : Nat := 4983230072969 + 3 ^ 40 * 4097249 * 2
def baseEnd_4097249 : Nat := 2103858098153545228144601

theorem tailTrace_4097249 : CollatzResearch.WordTrace tailWord_4097249 prefixEnd_4097249 2103858098153545228144601 := by
  unfold tailWord_4097249
  simp only [CollatzResearch.WordTrace]
  refine ⟨149438947933374102264014801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99625965288916068176009867 149438947933374102264014801)
  ·
    refine ⟨112079210950030576698011101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149438947933374102264014801 112079210950030576698011101)
    ·
      refine ⟨42029704106261466261754163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112079210950030576698011101 42029704106261466261754163)
      ·
        refine ⟨63044556159392199392631245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42029704106261466261754163 63044556159392199392631245)
        ·
          refine ⟨23641708559772074772236717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63044556159392199392631245 23641708559772074772236717)
          ·
            refine ⟨8865640709914528039588769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23641708559772074772236717 8865640709914528039588769)
            ·
              refine ⟨6649230532435896029691577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8865640709914528039588769 6649230532435896029691577)
              ·
                refine ⟨4986922899326922022268683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6649230532435896029691577 4986922899326922022268683)
                ·
                  refine ⟨7480384348990383033403025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4986922899326922022268683 7480384348990383033403025)
                  ·
                    refine ⟨5610288261742787275052269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7480384348990383033403025 5610288261742787275052269)
                    ·
                      refine ⟨2103858098153545228144601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5610288261742787275052269 2103858098153545228144601)
                      ·
                        rfl

theorem cell23_4097249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_4097249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097249 prefixEnd_4097249 := by exact prefixLift 4097249
  have htrace : WordTrace (prefixWord ++ tailWord_4097249) baseStart_4097249 baseEnd_4097249 := by
    simpa [prefixWord, tailWord_4097249, baseEnd_4097249] using wordTrace_append hprefix tailTrace_4097249
  have hstable : (prefixWord ++ tailWord_4097249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097249).length < 2 ^ (prefixWord ++ tailWord_4097249).sum := by decide
  have hdescent : baseEnd_4097249 < baseStart_4097249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097262 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_4097262 : Nat := 118140960795 + 4097262 * 2 ^ 59
def prefixEnd_4097262 : Nat := 4983230072969 + 3 ^ 40 * 4097262 * 2
def baseEnd_4097262 : Nat := 2103864773402053677282041

theorem tailTrace_4097262 : CollatzResearch.WordTrace tailWord_4097262 prefixEnd_4097262 2103864773402053677282041 := by
  unfold tailWord_4097262
  simp only [CollatzResearch.WordTrace]
  refine ⟨18679927760290875685529755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99626281388218003656158693 18679927760290875685529755)
  ·
    refine ⟨28019891640436313528294633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18679927760290875685529755 28019891640436313528294633)
    ·
      refine ⟨21014918730327235146220975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28019891640436313528294633 21014918730327235146220975)
      ·
        refine ⟨31522378095490852719331463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21014918730327235146220975 31522378095490852719331463)
        ·
          refine ⟨47283567143236279078997195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31522378095490852719331463 47283567143236279078997195)
          ·
            refine ⟨70925350714854418618495793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47283567143236279078997195 70925350714854418618495793)
            ·
              refine ⟨53194013036140813963871845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70925350714854418618495793 53194013036140813963871845)
              ·
                refine ⟨9973877444276402618225971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53194013036140813963871845 9973877444276402618225971)
                ·
                  refine ⟨14960816166414603927338957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9973877444276402618225971 14960816166414603927338957)
                  ·
                    refine ⟨5610306062405476472752109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14960816166414603927338957 5610306062405476472752109)
                    ·
                      refine ⟨2103864773402053677282041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5610306062405476472752109 2103864773402053677282041)
                      ·
                        rfl

theorem cell23_4097262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_4097262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097262 prefixEnd_4097262 := by exact prefixLift 4097262
  have htrace : WordTrace (prefixWord ++ tailWord_4097262) baseStart_4097262 baseEnd_4097262 := by
    simpa [prefixWord, tailWord_4097262, baseEnd_4097262] using wordTrace_append hprefix tailTrace_4097262
  have hstable : (prefixWord ++ tailWord_4097262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097262).length < 2 ^ (prefixWord ++ tailWord_4097262).sum := by decide
  have hdescent : baseEnd_4097262 < baseStart_4097262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097272 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 7, 3, 2]
def baseStart_4097272 : Nat := 118140960795 + 4097272 * 2 ^ 59
def prefixEnd_4097272 : Nat := 4983230072969 + 3 ^ 40 * 4097272 * 2
def baseEnd_4097272 : Nat := 2103869908208598638156995

theorem tailTrace_4097272 : CollatzResearch.WordTrace tailWord_4097272 prefixEnd_4097272 2103869908208598638156995 := by
  unfold tailWord_4097272
  simp only [CollatzResearch.WordTrace]
  refine ⟨74719893406145388596051035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99626524541527184794734713 74719893406145388596051035)
  ·
    refine ⟨112079840109218082894076553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74719893406145388596051035 112079840109218082894076553)
    ·
      refine ⟨84059880081913562170557415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112079840109218082894076553 84059880081913562170557415)
      ·
        refine ⟨126089820122870343255836123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84059880081913562170557415 126089820122870343255836123)
        ·
          refine ⟨189134730184305514883754185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126089820122870343255836123 189134730184305514883754185)
          ·
            refine ⟨141851047638229136162815639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189134730184305514883754185 141851047638229136162815639)
            ·
              refine ⟨212776571457343704244223459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141851047638229136162815639 212776571457343704244223459)
              ·
                refine ⟨319164857186015556366335189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212776571457343704244223459 319164857186015556366335189)
                ·
                  refine ⟨7480426340297239602335981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 319164857186015556366335189 7480426340297239602335981)
                  ·
                    refine ⟨2805159877611464850875993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7480426340297239602335981 2805159877611464850875993)
                    ·
                      refine ⟨2103869908208598638156995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2805159877611464850875993 2103869908208598638156995)
                      ·
                        rfl

theorem cell23_4097272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 7, 3, 2].length) (baseStart_4097272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097272 prefixEnd_4097272 := by exact prefixLift 4097272
  have htrace : WordTrace (prefixWord ++ tailWord_4097272) baseStart_4097272 baseEnd_4097272 := by
    simpa [prefixWord, tailWord_4097272, baseEnd_4097272] using wordTrace_append hprefix tailTrace_4097272
  have hstable : (prefixWord ++ tailWord_4097272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097272).length < 2 ^ (prefixWord ++ tailWord_4097272).sum := by decide
  have hdescent : baseEnd_4097272 < baseStart_4097272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097285 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 2, 3, 4]
def baseStart_4097285 : Nat := 118140960795 + 4097285 * 2 ^ 59
def prefixEnd_4097285 : Nat := 4983230072969 + 3 ^ 40 * 4097285 * 2
def baseEnd_4097285 : Nat := 2103876583457107087294435

theorem tailTrace_4097285 : CollatzResearch.WordTrace tailWord_4097285 prefixEnd_4097285 2103876583457107087294435 := by
  unfold tailWord_4097285
  simp only [CollatzResearch.WordTrace]
  refine ⟨149440260961243680412325309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99626840640829120274883539 149440260961243680412325309)
  ·
    refine ⟨56040097860466380154621991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149440260961243680412325309 56040097860466380154621991)
    ·
      refine ⟨84060146790699570231932987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56040097860466380154621991 84060146790699570231932987)
      ·
        refine ⟨126090220186049355347899481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84060146790699570231932987 126090220186049355347899481)
        ·
          refine ⟨94567665139537016510924611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126090220186049355347899481 94567665139537016510924611)
          ·
            refine ⟨141851497709305524766386917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94567665139537016510924611 141851497709305524766386917)
            ·
              refine ⟨26597155820494785893697547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141851497709305524766386917 26597155820494785893697547)
              ·
                refine ⟨39895733730742178840546321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26597155820494785893697547 39895733730742178840546321)
                ·
                  refine ⟨29921800298056634130409741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39895733730742178840546321 29921800298056634130409741)
                  ·
                    refine ⟨11220675111771237798903653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29921800298056634130409741 11220675111771237798903653)
                    ·
                      refine ⟨2103876583457107087294435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11220675111771237798903653 2103876583457107087294435)
                      ·
                        rfl

theorem cell23_4097285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_4097285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097285 prefixEnd_4097285 := by exact prefixLift 4097285
  have htrace : WordTrace (prefixWord ++ tailWord_4097285) baseStart_4097285 baseEnd_4097285 := by
    simpa [prefixWord, tailWord_4097285, baseEnd_4097285] using wordTrace_append hprefix tailTrace_4097285
  have hstable : (prefixWord ++ tailWord_4097285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097285).length < 2 ^ (prefixWord ++ tailWord_4097285).sum := by decide
  have hdescent : baseEnd_4097285 < baseStart_4097285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097306 : List Nat := [3, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2]
def baseStart_4097306 : Nat := 118140960795 + 4097306 * 2 ^ 59
def prefixEnd_4097306 : Nat := 4983230072969 + 3 ^ 40 * 4097306 * 2
def baseEnd_4097306 : Nat := 2103887366550851505131839

theorem tailTrace_4097306 : CollatzResearch.WordTrace tailWord_4097306 prefixEnd_4097306 2103887366550851505131839 := by
  unfold tailWord_4097306
  simp only [CollatzResearch.WordTrace]
  refine ⟨37360256723541900249709943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99627351262778400665893181 37360256723541900249709943)
  ·
    refine ⟨56040385085312850374564915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37360256723541900249709943 56040385085312850374564915)
    ·
      refine ⟨84060577627969275561847373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56040385085312850374564915 84060577627969275561847373)
      ·
        refine ⟨31522716610488478335692765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84060577627969275561847373 31522716610488478335692765)
        ·
          refine ⟨11821018728933179375884787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31522716610488478335692765 11821018728933179375884787)
          ·
            refine ⟨17731528093399769063827181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11821018728933179375884787 17731528093399769063827181)
            ·
              refine ⟨6649323035024913398935193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17731528093399769063827181 6649323035024913398935193)
              ·
                refine ⟨4986992276268685049201395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6649323035024913398935193 4986992276268685049201395)
                ·
                  refine ⟨7480488414403027573802093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4986992276268685049201395 7480488414403027573802093)
                  ·
                    refine ⟨2805183155401135340175785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7480488414403027573802093 2805183155401135340175785)
                    ·
                      refine ⟨2103887366550851505131839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2805183155401135340175785 2103887366550851505131839)
                      ·
                        rfl

theorem cell23_4097306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_4097306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097306 prefixEnd_4097306 := by exact prefixLift 4097306
  have htrace : WordTrace (prefixWord ++ tailWord_4097306) baseStart_4097306 baseEnd_4097306 := by
    simpa [prefixWord, tailWord_4097306, baseEnd_4097306] using wordTrace_append hprefix tailTrace_4097306
  have hstable : (prefixWord ++ tailWord_4097306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097306).length < 2 ^ (prefixWord ++ tailWord_4097306).sum := by decide
  have hdescent : baseEnd_4097306 < baseStart_4097306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097342 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 7]
def baseStart_4097342 : Nat := 118140960795 + 4097342 * 2 ^ 59
def prefixEnd_4097342 : Nat := 4983230072969 + 3 ^ 40 * 4097342 * 2
def baseEnd_4097342 : Nat := 233767316872712596031297

theorem tailTrace_4097342 : CollatzResearch.WordTrace tailWord_4097342 prefixEnd_4097342 233767316872712596031297 := by
  unfold tailWord_4097342
  simp only [CollatzResearch.WordTrace]
  refine ⟨18680292490254647393393785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99628226614691452764766853 18680292490254647393393785)
  ·
    refine ⟨14010219367690985545045339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18680292490254647393393785 14010219367690985545045339)
    ·
      refine ⟨21015329051536478317568009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14010219367690985545045339 21015329051536478317568009)
      ·
        refine ⟨15761496788652358738176007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21015329051536478317568009 15761496788652358738176007)
        ·
          refine ⟨23642245182978538107264011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15761496788652358738176007 23642245182978538107264011)
          ·
            refine ⟨35463367774467807160896017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23642245182978538107264011 35463367774467807160896017)
            ·
              refine ⟨26597525830850855370672013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35463367774467807160896017 26597525830850855370672013)
              ·
                refine ⟨9974072186569070764002005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26597525830850855370672013 9974072186569070764002005)
                ·
                  refine ⟨233767316872712596031297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9974072186569070764002005 233767316872712596031297)
                  ·
                    rfl

theorem cell23_4097342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_4097342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097342 prefixEnd_4097342 := by exact prefixLift 4097342
  have htrace : WordTrace (prefixWord ++ tailWord_4097342) baseStart_4097342 baseEnd_4097342 := by
    simpa [prefixWord, tailWord_4097342, baseEnd_4097342] using wordTrace_append hprefix tailTrace_4097342
  have hstable : (prefixWord ++ tailWord_4097342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097342).length < 2 ^ (prefixWord ++ tailWord_4097342).sum := by decide
  have hdescent : baseEnd_4097342 < baseStart_4097342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097392 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 4]
def baseStart_4097392 : Nat := 118140960795 + 4097392 * 2 ^ 59
def prefixEnd_4097392 : Nat := 4983230072969 + 3 ^ 40 * 4097392 * 2
def baseEnd_4097392 : Nat := 2103931525887138168656443

theorem tailTrace_4097392 : CollatzResearch.WordTrace tailWord_4097392 prefixEnd_4097392 2103931525887138168656443 := by
  unfold tailWord_4097392
  simp only [CollatzResearch.WordTrace]
  refine ⟨74722081785928018843235215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99629442381237358457646953 74722081785928018843235215)
  ·
    refine ⟨112083122678892028264852823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74722081785928018843235215 112083122678892028264852823)
    ·
      refine ⟨168124684018338042397279235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112083122678892028264852823 168124684018338042397279235)
      ·
        refine ⟨252187026027507063595918853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168124684018338042397279235 252187026027507063595918853)
        ·
          refine ⟨47285067380157574424234785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252187026027507063595918853 47285067380157574424234785)
          ·
            refine ⟨35463800535118180818176089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47285067380157574424234785 35463800535118180818176089)
            ·
              refine ⟨26597850401338635613632067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35463800535118180818176089 26597850401338635613632067)
              ·
                refine ⟨39896775602007953420448101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26597850401338635613632067 39896775602007953420448101)
                ·
                  refine ⟨7480645425376491266334019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39896775602007953420448101 7480645425376491266334019)
                  ·
                    refine ⟨11220968138064736899501029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7480645425376491266334019 11220968138064736899501029)
                    ·
                      refine ⟨2103931525887138168656443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11220968138064736899501029 2103931525887138168656443)
                      ·
                        rfl

theorem cell23_4097392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 4].length) (baseStart_4097392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097392 prefixEnd_4097392 := by exact prefixLift 4097392
  have htrace : WordTrace (prefixWord ++ tailWord_4097392) baseStart_4097392 baseEnd_4097392 := by
    simpa [prefixWord, tailWord_4097392, baseEnd_4097392] using wordTrace_append hprefix tailTrace_4097392
  have hstable : (prefixWord ++ tailWord_4097392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097392).length < 2 ^ (prefixWord ++ tailWord_4097392).sum := by decide
  have hdescent : baseEnd_4097392 < baseStart_4097392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097402 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 7, 4]
def baseStart_4097402 : Nat := 118140960795 + 4097402 * 2 ^ 59
def prefixEnd_4097402 : Nat := 4983230072969 + 3 ^ 40 * 4097402 * 2
def baseEnd_4097402 : Nat := 701312220231227709843799

theorem tailTrace_4097402 : CollatzResearch.WordTrace tailWord_4097402 prefixEnd_4097402 701312220231227709843799 := by
  unfold tailWord_4097402
  simp only [CollatzResearch.WordTrace]
  refine ⟨37361132075454952348583615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99629685534546539596222973 37361132075454952348583615)
  ·
    refine ⟨56041698113182428522875423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37361132075454952348583615 56041698113182428522875423)
    ·
      refine ⟨84062547169773642784313135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56041698113182428522875423 84062547169773642784313135)
      ·
        refine ⟨126093820754660464176469703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84062547169773642784313135 126093820754660464176469703)
        ·
          refine ⟨189140731131990696264704555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126093820754660464176469703 189140731131990696264704555)
          ·
            refine ⟨283711096697986044397056833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189140731131990696264704555 283711096697986044397056833)
            ·
              refine ⟨212783322523489533297792625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283711096697986044397056833 212783322523489533297792625)
              ·
                refine ⟨159587491892617149973344469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212783322523489533297792625 159587491892617149973344469)
                ·
                  refine ⟨3740331841233214452500261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 159587491892617149973344469 3740331841233214452500261)
                  ·
                    refine ⟨701312220231227709843799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3740331841233214452500261 701312220231227709843799)
                    ·
                      rfl

theorem cell23_4097402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_4097402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097402 prefixEnd_4097402 := by exact prefixLift 4097402
  have htrace : WordTrace (prefixWord ++ tailWord_4097402) baseStart_4097402 baseEnd_4097402 := by
    simpa [prefixWord, tailWord_4097402, baseEnd_4097402] using wordTrace_append hprefix tailTrace_4097402
  have hstable : (prefixWord ++ tailWord_4097402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097402).length < 2 ^ (prefixWord ++ tailWord_4097402).sum := by decide
  have hdescent : baseEnd_4097402 < baseStart_4097402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097453 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_4097453 : Nat := 118140960795 + 4097453 * 2 ^ 59
def prefixEnd_4097453 : Nat := 4983230072969 + 3 ^ 40 * 4097453 * 2
def baseEnd_4097453 : Nat := 701320949402354143331221

theorem tailTrace_4097453 : CollatzResearch.WordTrace tailWord_4097453 prefixEnd_4097453 701320949402354143331221 := by
  unfold tailWord_4097453
  simp only [CollatzResearch.WordTrace]
  refine ⟨149446388424635045104441013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99630925616423363402960675 149446388424635045104441013)
  ·
    refine ⟨14010598914809535478541345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149446388424635045104441013 14010598914809535478541345)
    ·
      refine ⟨10507949186107151608906009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14010598914809535478541345 10507949186107151608906009)
      ·
        refine ⟨7880961889580363706679507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10507949186107151608906009 7880961889580363706679507)
        ·
          refine ⟨11821442834370545560019261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7880961889580363706679507 11821442834370545560019261)
          ·
            refine ⟨4433041062888954585007223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11821442834370545560019261 4433041062888954585007223)
            ·
              refine ⟨6649561594333431877510835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4433041062888954585007223 6649561594333431877510835)
              ·
                refine ⟨9974342391500147816266253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6649561594333431877510835 9974342391500147816266253)
                ·
                  refine ⟨3740378396812555431099845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9974342391500147816266253 3740378396812555431099845)
                  ·
                    refine ⟨701320949402354143331221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3740378396812555431099845 701320949402354143331221)
                    ·
                      rfl

theorem cell23_4097453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_4097453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097453 prefixEnd_4097453 := by exact prefixLift 4097453
  have htrace : WordTrace (prefixWord ++ tailWord_4097453) baseStart_4097453 baseEnd_4097453 := by
    simpa [prefixWord, tailWord_4097453, baseEnd_4097453] using wordTrace_append hprefix tailTrace_4097453
  have hstable : (prefixWord ++ tailWord_4097453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097453).length < 2 ^ (prefixWord ++ tailWord_4097453).sum := by decide
  have hdescent : baseEnd_4097453 < baseStart_4097453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097486 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2]
def baseStart_4097486 : Nat := 118140960795 + 4097486 * 2 ^ 59
def prefixEnd_4097486 : Nat := 4983230072969 + 3 ^ 40 * 4097486 * 2
def baseEnd_4097486 : Nat := 2103979793068660800881011

theorem tailTrace_4097486 : CollatzResearch.WordTrace tailWord_4097486 prefixEnd_4097486 2103979793068660800881011 := by
  unfold tailWord_4097486
  simp only [CollatzResearch.WordTrace]
  refine ⟨18680949004189436467549039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99631728022343661160261541 18680949004189436467549039)
  ·
    refine ⟨28021423506284154701323559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18680949004189436467549039 28021423506284154701323559)
    ·
      refine ⟨42032135259426232051985339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28021423506284154701323559 42032135259426232051985339)
      ·
        refine ⟨63048202889139348077978009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42032135259426232051985339 63048202889139348077978009)
        ·
          refine ⟨47286152166854511058483507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63048202889139348077978009 47286152166854511058483507)
          ·
            refine ⟨70929228250281766587725261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47286152166854511058483507 70929228250281766587725261)
            ·
              refine ⟨26598460593855662470396973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70929228250281766587725261 26598460593855662470396973)
              ·
                refine ⟨9974422722695873426398865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26598460593855662470396973 9974422722695873426398865)
                ·
                  refine ⟨7480817042021905069799149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9974422722695873426398865 7480817042021905069799149)
                  ·
                    refine ⟨2805306390758214401174681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7480817042021905069799149 2805306390758214401174681)
                    ·
                      refine ⟨2103979793068660800881011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2805306390758214401174681 2103979793068660800881011)
                      ·
                        rfl

theorem cell23_4097486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_4097486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097486 prefixEnd_4097486 := by exact prefixLift 4097486
  have htrace : WordTrace (prefixWord ++ tailWord_4097486) baseStart_4097486 baseEnd_4097486 := by
    simpa [prefixWord, tailWord_4097486, baseEnd_4097486] using wordTrace_append hprefix tailTrace_4097486
  have hstable : (prefixWord ++ tailWord_4097486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097486).length < 2 ^ (prefixWord ++ tailWord_4097486).sum := by decide
  have hdescent : baseEnd_4097486 < baseStart_4097486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097493 : List Nat := [1, 3, 2, 3, 1, 1, 2, 5, 1, 1, 3]
def baseStart_4097493 : Nat := 118140960795 + 4097493 * 2 ^ 59
def prefixEnd_4097493 : Nat := 4983230072969 + 3 ^ 40 * 4097493 * 2
def baseEnd_4097493 : Nat := 2103983387433242273493479

theorem tailTrace_4097493 : CollatzResearch.WordTrace tailWord_4097493 prefixEnd_4097493 2103983387433242273493479 := by
  unfold tailWord_4097493
  simp only [CollatzResearch.WordTrace]
  refine ⟨149447847344490131935897133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99631898229660087957264755 149447847344490131935897133)
  ·
    refine ⟨56042942754183799475961425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149447847344490131935897133 56042942754183799475961425)
    ·
      refine ⟨42032207065637849606971069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56042942754183799475961425 42032207065637849606971069)
      ·
        refine ⟨15762077649614193602614151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42032207065637849606971069 15762077649614193602614151)
        ·
          refine ⟨23643116474421290403921227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15762077649614193602614151 23643116474421290403921227)
          ·
            refine ⟨35464674711631935605881841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23643116474421290403921227 35464674711631935605881841)
            ·
              refine ⟨26598506033723951704411381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35464674711631935605881841 26598506033723951704411381)
              ·
                refine ⟨2493609940661620472288567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26598506033723951704411381 2493609940661620472288567)
                ·
                  refine ⟨3740414910992430708432851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2493609940661620472288567 3740414910992430708432851)
                  ·
                    refine ⟨5610622366488646062649277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3740414910992430708432851 5610622366488646062649277)
                    ·
                      refine ⟨2103983387433242273493479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5610622366488646062649277 2103983387433242273493479)
                      ·
                        rfl

theorem cell23_4097493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_4097493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097493 prefixEnd_4097493 := by exact prefixLift 4097493
  have htrace : WordTrace (prefixWord ++ tailWord_4097493) baseStart_4097493 baseEnd_4097493 := by
    simpa [prefixWord, tailWord_4097493, baseEnd_4097493] using wordTrace_append hprefix tailTrace_4097493
  have hstable : (prefixWord ++ tailWord_4097493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097493).length < 2 ^ (prefixWord ++ tailWord_4097493).sum := by decide
  have hdescent : baseEnd_4097493 < baseStart_4097493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097519 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 3]
def baseStart_4097519 : Nat := 118140960795 + 4097519 * 2 ^ 59
def prefixEnd_4097519 : Nat := 4983230072969 + 3 ^ 40 * 4097519 * 2
def baseEnd_4097519 : Nat := 2103996737930259171768359

theorem tailTrace_4097519 : CollatzResearch.WordTrace tailWord_4097519 prefixEnd_4097519 2103996737930259171768359 := by
  unfold tailWord_4097519
  simp only [CollatzResearch.WordTrace]
  refine ⟨149448795642395938376343611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99632530428263958917562407 149448795642395938376343611)
  ·
    refine ⟨224173193463593907564515417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149448795642395938376343611 224173193463593907564515417)
    ·
      refine ⟨168129895097695430673386563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224173193463593907564515417 168129895097695430673386563)
      ·
        refine ⟨252194842646543146010079845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168129895097695430673386563 252194842646543146010079845)
        ·
          refine ⟨47286532996226839876889971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252194842646543146010079845 47286532996226839876889971)
          ·
            refine ⟨70929799494340259815334957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47286532996226839876889971 70929799494340259815334957)
            ·
              refine ⟨26598674810377597430750609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70929799494340259815334957 26598674810377597430750609)
              ·
                refine ⟨19949006107783198073062957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26598674810377597430750609 19949006107783198073062957)
                ·
                  refine ⟨7480877290418699277398609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19949006107783198073062957 7480877290418699277398609)
                  ·
                    refine ⟨5610657967814024458048957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7480877290418699277398609 5610657967814024458048957)
                    ·
                      refine ⟨2103996737930259171768359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5610657967814024458048957 2103996737930259171768359)
                      ·
                        rfl

theorem cell23_4097519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 3].length) (baseStart_4097519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097519 prefixEnd_4097519 := by exact prefixLift 4097519
  have htrace : WordTrace (prefixWord ++ tailWord_4097519) baseStart_4097519 baseEnd_4097519 := by
    simpa [prefixWord, tailWord_4097519, baseEnd_4097519] using wordTrace_append hprefix tailTrace_4097519
  have hstable : (prefixWord ++ tailWord_4097519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097519).length < 2 ^ (prefixWord ++ tailWord_4097519).sum := by decide
  have hdescent : baseEnd_4097519 < baseStart_4097519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097526 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_4097526 : Nat := 118140960795 + 4097526 * 2 ^ 59
def prefixEnd_4097526 : Nat := 4983230072969 + 3 ^ 40 * 4097526 * 2
def baseEnd_4097526 : Nat := 701333444098280214793609

theorem tailTrace_4097526 : CollatzResearch.WordTrace tailWord_4097526 prefixEnd_4097526 701333444098280214793609 := by
  unfold tailWord_4097526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9340565684585661160740527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99632700635580385714565621 9340565684585661160740527)
  ·
    refine ⟨14010848526878491741110791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9340565684585661160740527 14010848526878491741110791)
    ·
      refine ⟨21016272790317737611666187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14010848526878491741110791 21016272790317737611666187)
      ·
        refine ⟨31524409185476606417499281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21016272790317737611666187 31524409185476606417499281)
        ·
          refine ⟨23643306889107454813124461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31524409185476606417499281 23643306889107454813124461)
          ·
            refine ⟨8866240083415295554921673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23643306889107454813124461 8866240083415295554921673)
            ·
              refine ⟨6649680062561471666191255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8866240083415295554921673 6649680062561471666191255)
              ·
                refine ⟨9974520093842207499286883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6649680062561471666191255 9974520093842207499286883)
                ·
                  refine ⟨14961780140763311248930325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9974520093842207499286883 14961780140763311248930325)
                  ·
                    refine ⟨701333444098280214793609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14961780140763311248930325 701333444098280214793609)
                    ·
                      rfl

theorem cell23_4097526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_4097526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097526 prefixEnd_4097526 := by exact prefixLift 4097526
  have htrace : WordTrace (prefixWord ++ tailWord_4097526) baseStart_4097526 baseEnd_4097526 := by
    simpa [prefixWord, tailWord_4097526, baseEnd_4097526] using wordTrace_append hprefix tailTrace_4097526
  have hstable : (prefixWord ++ tailWord_4097526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097526).length < 2 ^ (prefixWord ++ tailWord_4097526).sum := by decide
  have hdescent : baseEnd_4097526 < baseStart_4097526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097533 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 3, 2, 2]
def baseStart_4097533 : Nat := 118140960795 + 4097533 * 2 ^ 59
def prefixEnd_4097533 : Nat := 4983230072969 + 3 ^ 40 * 4097533 * 2
def baseEnd_4097533 : Nat := 2104003926659422116993295

theorem tailTrace_4097533 : CollatzResearch.WordTrace tailWord_4097533 prefixEnd_4097533 2104003926659422116993295 := by
  unfold tailWord_4097533
  simp only [CollatzResearch.WordTrace]
  refine ⟨149449306264345218767353253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99632870842896812511568835 149449306264345218767353253)
  ·
    refine ⟨28021744924564728518878735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149449306264345218767353253 28021744924564728518878735)
    ·
      refine ⟨42032617386847092778318103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28021744924564728518878735 42032617386847092778318103)
      ·
        refine ⟨63048926080270639167477155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42032617386847092778318103 63048926080270639167477155)
        ·
          refine ⟨94573389120405958751215733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63048926080270639167477155 94573389120405958751215733)
          ·
            refine ⟨8866255230038058632926475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94573389120405958751215733 8866255230038058632926475)
            ·
              refine ⟨13299382845057087949389713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8866255230038058632926475 13299382845057087949389713)
              ·
                refine ⟨9974537133792815962042285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13299382845057087949389713 9974537133792815962042285)
                ·
                  refine ⟨3740451425172305985765857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9974537133792815962042285 3740451425172305985765857)
                  ·
                    refine ⟨2805338568879229489324393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3740451425172305985765857 2805338568879229489324393)
                    ·
                      refine ⟨2104003926659422116993295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2805338568879229489324393 2104003926659422116993295)
                      ·
                        rfl

theorem cell23_4097533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_4097533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097533 prefixEnd_4097533 := by exact prefixLift 4097533
  have htrace : WordTrace (prefixWord ++ tailWord_4097533) baseStart_4097533 baseEnd_4097533 := by
    simpa [prefixWord, tailWord_4097533, baseEnd_4097533] using wordTrace_append hprefix tailTrace_4097533
  have hstable : (prefixWord ++ tailWord_4097533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097533).length < 2 ^ (prefixWord ++ tailWord_4097533).sum := by decide
  have hdescent : baseEnd_4097533 < baseStart_4097533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097550 : List Nat := [4, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4]
def baseStart_4097550 : Nat := 118140960795 + 4097550 * 2 ^ 59
def prefixEnd_4097550 : Nat := 4983230072969 + 3 ^ 40 * 4097550 * 2
def baseEnd_4097550 : Nat := 2104012655830548550480717

theorem tailTrace_4097550 : CollatzResearch.WordTrace tailWord_4097550 prefixEnd_4097550 2104012655830548550480717 := by
  unfold tailWord_4097550
  simp only [CollatzResearch.WordTrace]
  refine ⟨18681240788160453833840263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99633284203522420447148069 18681240788160453833840263)
  ·
    refine ⟨28021861182240680750760395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18681240788160453833840263 28021861182240680750760395)
    ·
      refine ⟨42032791773361021126140593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28021861182240680750760395 42032791773361021126140593)
      ·
        refine ⟨31524593830020765844605445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42032791773361021126140593 31524593830020765844605445)
        ·
          refine ⟨5910861343128893595863521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31524593830020765844605445 5910861343128893595863521)
          ·
            refine ⟨4433146007346670196897641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5910861343128893595863521 4433146007346670196897641)
            ·
              refine ⟨3324859505510002647673231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4433146007346670196897641 3324859505510002647673231)
              ·
                refine ⟨4987289258265003971509847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3324859505510002647673231 4987289258265003971509847)
                ·
                  refine ⟨7480933887397505957264771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4987289258265003971509847 7480933887397505957264771)
                  ·
                    refine ⟨11221400831096258935897157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7480933887397505957264771 11221400831096258935897157)
                    ·
                      refine ⟨2104012655830548550480717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11221400831096258935897157 2104012655830548550480717)
                      ·
                        rfl

theorem cell23_4097550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_4097550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097550 prefixEnd_4097550 := by exact prefixLift 4097550
  have htrace : WordTrace (prefixWord ++ tailWord_4097550) baseStart_4097550 baseEnd_4097550 := by
    simpa [prefixWord, tailWord_4097550, baseEnd_4097550] using wordTrace_append hprefix tailTrace_4097550
  have hstable : (prefixWord ++ tailWord_4097550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097550).length < 2 ^ (prefixWord ++ tailWord_4097550).sum := by decide
  have hdescent : baseEnd_4097550 < baseStart_4097550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097556 : List Nat := [2, 4, 3, 1, 2, 1, 10]
def baseStart_4097556 : Nat := 118140960795 + 4097556 * 2 ^ 59
def prefixEnd_4097556 : Nat := 4983230072969 + 3 ^ 40 * 4097556 * 2
def baseEnd_4097556 : Nat := 25975502922400932432169

theorem tailTrace_4097556 : CollatzResearch.WordTrace tailWord_4097556 prefixEnd_4097556 25975502922400932432169 := by
  unfold tailWord_4097556
  simp only [CollatzResearch.WordTrace]
  refine ⟨74725072571630946847720261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99633430095507929130293681 74725072571630946847720261)
  ·
    refine ⟨14010951107180802533947549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74725072571630946847720261 14010951107180802533947549)
    ·
      refine ⟨5254106665192800950230331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14010951107180802533947549 5254106665192800950230331)
      ·
        refine ⟨7881159997789201425345497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5254106665192800950230331 7881159997789201425345497)
        ·
          refine ⟨5910869998341901069009123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7881159997789201425345497 5910869998341901069009123)
          ·
            refine ⟨8866304997512851603513685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5910869998341901069009123 8866304997512851603513685)
            ·
              refine ⟨25975502922400932432169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8866304997512851603513685 25975502922400932432169)
              ·
                rfl

theorem cell23_4097556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 10].length) (baseStart_4097556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097556 prefixEnd_4097556 := by exact prefixLift 4097556
  have htrace : WordTrace (prefixWord ++ tailWord_4097556) baseStart_4097556 baseEnd_4097556 := by
    simpa [prefixWord, tailWord_4097556, baseEnd_4097556] using wordTrace_append hprefix tailTrace_4097556
  have hstable : (prefixWord ++ tailWord_4097556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097556).length < 2 ^ (prefixWord ++ tailWord_4097556).sum := by decide
  have hdescent : baseEnd_4097556 < baseStart_4097556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097560 : List Nat := [2, 1, 2, 3, 5, 1, 1, 2, 2, 4]
def baseStart_4097560 : Nat := 118140960795 + 4097560 * 2 ^ 59
def prefixEnd_4097560 : Nat := 4983230072969 + 3 ^ 40 * 4097560 * 2
def baseEnd_4097560 : Nat := 701339263545697837118557

theorem tailTrace_4097560 : CollatzResearch.WordTrace tailWord_4097560 prefixEnd_4097560 701339263545697837118557 := by
  unfold tailWord_4097560
  simp only [CollatzResearch.WordTrace]
  refine ⟨74725145517623701189293067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99633527356831601585724089 74725145517623701189293067)
  ·
    refine ⟨112087718276435551783939601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74725145517623701189293067 112087718276435551783939601)
    ·
      refine ⟨84065788707326663837954701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112087718276435551783939601 84065788707326663837954701)
      ·
        refine ⟨31524670765247498939233013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84065788707326663837954701 31524670765247498939233013)
        ·
          refine ⟨2955437884241953025553095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31524670765247498939233013 2955437884241953025553095)
          ·
            refine ⟨4433156826362929538329643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2955437884241953025553095 4433156826362929538329643)
            ·
              refine ⟨6649735239544394307494465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4433156826362929538329643 6649735239544394307494465)
              ·
                refine ⟨4987301429658295730620849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6649735239544394307494465 4987301429658295730620849)
                ·
                  refine ⟨3740476072243721797965637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4987301429658295730620849 3740476072243721797965637)
                  ·
                    refine ⟨701339263545697837118557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3740476072243721797965637 701339263545697837118557)
                    ·
                      rfl

theorem cell23_4097560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_4097560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097560 prefixEnd_4097560 := by exact prefixLift 4097560
  have htrace : WordTrace (prefixWord ++ tailWord_4097560) baseStart_4097560 baseEnd_4097560 := by
    simpa [prefixWord, tailWord_4097560, baseEnd_4097560] using wordTrace_append hprefix tailTrace_4097560
  have hstable : (prefixWord ++ tailWord_4097560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097560).length < 2 ^ (prefixWord ++ tailWord_4097560).sum := by decide
  have hdescent : baseEnd_4097560 < baseStart_4097560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097590 : List Nat := [5, 1, 2, 1, 4, 1, 2, 7]
def baseStart_4097590 : Nat := 118140960795 + 4097590 * 2 ^ 59
def prefixEnd_4097590 : Nat := 4983230072969 + 3 ^ 40 * 4097590 * 2
def baseEnd_4097590 : Nat := 77927155372471421999279

theorem tailTrace_4097590 : CollatzResearch.WordTrace tailWord_4097590 prefixEnd_4097590 77927155372471421999279 := by
  unfold tailWord_4097590
  simp only [CollatzResearch.WordTrace]
  refine ⟨9340711576571169843886139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99634256816759145001452149 9340711576571169843886139)
  ·
    refine ⟨14011067364856754765829209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9340711576571169843886139 14011067364856754765829209)
    ·
      refine ⟨10508300523642566074371907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14011067364856754765829209 10508300523642566074371907)
      ·
        refine ⟨15762450785463849111557861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10508300523642566074371907 15762450785463849111557861)
        ·
          refine ⟨2955459522274471708417099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15762450785463849111557861 2955459522274471708417099)
          ·
            refine ⟨4433189283411707562625649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2955459522274471708417099 4433189283411707562625649)
            ·
              refine ⟨3324891962558780671969237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4433189283411707562625649 3324891962558780671969237)
              ·
                refine ⟨77927155372471421999279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3324891962558780671969237 77927155372471421999279)
                ·
                  rfl

theorem cell23_4097590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_4097590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097590 prefixEnd_4097590 := by exact prefixLift 4097590
  have htrace : WordTrace (prefixWord ++ tailWord_4097590) baseStart_4097590 baseEnd_4097590 := by
    simpa [prefixWord, tailWord_4097590, baseEnd_4097590] using wordTrace_append hprefix tailTrace_4097590
  have hstable : (prefixWord ++ tailWord_4097590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097590).length < 2 ^ (prefixWord ++ tailWord_4097590).sum := by decide
  have hdescent : baseEnd_4097590 < baseStart_4097590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097593 : List Nat := [1, 2, 1, 5, 1, 2, 1, 4, 1, 3, 2]
def baseStart_4097593 : Nat := 118140960795 + 4097593 * 2 ^ 59
def prefixEnd_4097593 : Nat := 4983230072969 + 3 ^ 40 * 4097593 * 2
def baseEnd_4097593 : Nat := 2104034735498691882243019

theorem tailTrace_4097593 : CollatzResearch.WordTrace tailWord_4097593 prefixEnd_4097593 2104034735498691882243019 := by
  unfold tailWord_4097593
  simp only [CollatzResearch.WordTrace]
  refine ⟨149451494644127849014537433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99634329762751899343024955 149451494644127849014537433)
  ·
    refine ⟨112088620983095886760903075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149451494644127849014537433 112088620983095886760903075)
    ·
      refine ⟨168132931474643830141354613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112088620983095886760903075 168132931474643830141354613)
      ·
        refine ⟨15762462325747859075751995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168132931474643830141354613 15762462325747859075751995)
        ·
          refine ⟨23643693488621788613627993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15762462325747859075751995 23643693488621788613627993)
          ·
            refine ⟨17732770116466341460220995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23643693488621788613627993 17732770116466341460220995)
            ·
              refine ⟨26599155174699512190331493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17732770116466341460220995 26599155174699512190331493)
              ·
                refine ⟨4987341595256158535687155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26599155174699512190331493 4987341595256158535687155)
                ·
                  refine ⟨7481012392884237803530733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4987341595256158535687155 7481012392884237803530733)
                  ·
                    refine ⟨2805379647331589176324025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7481012392884237803530733 2805379647331589176324025)
                    ·
                      refine ⟨2104034735498691882243019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2805379647331589176324025 2104034735498691882243019)
                      ·
                        rfl

theorem cell23_4097593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_4097593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097593 prefixEnd_4097593 := by exact prefixLift 4097593
  have htrace : WordTrace (prefixWord ++ tailWord_4097593) baseStart_4097593 baseEnd_4097593 := by
    simpa [prefixWord, tailWord_4097593, baseEnd_4097593] using wordTrace_append hprefix tailTrace_4097593
  have hstable : (prefixWord ++ tailWord_4097593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097593).length < 2 ^ (prefixWord ++ tailWord_4097593).sum := by decide
  have hdescent : baseEnd_4097593 < baseStart_4097593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097623 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 4, 2, 2]
def baseStart_4097623 : Nat := 118140960795 + 4097623 * 2 ^ 59
def prefixEnd_4097623 : Nat := 4983230072969 + 3 ^ 40 * 4097623 * 2
def baseEnd_4097623 : Nat := 2104050139918326764867881

theorem tailTrace_4097623 : CollatzResearch.WordTrace tailWord_4097623 prefixEnd_4097623 2104050139918326764867881 := by
  unfold tailWord_4097623
  simp only [CollatzResearch.WordTrace]
  refine ⟨149452588834019164138129523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99635059222679442758753015 149452588834019164138129523)
  ·
    refine ⟨224178883251028746207194285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149452588834019164138129523 224178883251028746207194285)
    ·
      refine ⟨84067081219135779827697857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224178883251028746207194285 84067081219135779827697857)
      ·
        refine ⟨63050310914351834870773393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84067081219135779827697857 63050310914351834870773393)
        ·
          refine ⟨47287733185763876153080045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63050310914351834870773393 47287733185763876153080045)
          ·
            refine ⟨17732899944661453557405017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47287733185763876153080045 17732899944661453557405017)
            ·
              refine ⟨13299674958496090168053763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17732899944661453557405017 13299674958496090168053763)
              ·
                refine ⟨19949512437744135252080645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13299674958496090168053763 19949512437744135252080645)
                ·
                  refine ⟨3740533582077025359765121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19949512437744135252080645 3740533582077025359765121)
                  ·
                    refine ⟨2805400186557769019823841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3740533582077025359765121 2805400186557769019823841)
                    ·
                      refine ⟨2104050139918326764867881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2805400186557769019823841 2104050139918326764867881)
                      ·
                        rfl

theorem cell23_4097623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_4097623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097623 prefixEnd_4097623 := by exact prefixLift 4097623
  have htrace : WordTrace (prefixWord ++ tailWord_4097623) baseStart_4097623 baseEnd_4097623 := by
    simpa [prefixWord, tailWord_4097623, baseEnd_4097623] using wordTrace_append hprefix tailTrace_4097623
  have hstable : (prefixWord ++ tailWord_4097623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097623).length < 2 ^ (prefixWord ++ tailWord_4097623).sum := by decide
  have hdescent : baseEnd_4097623 < baseStart_4097623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097669 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 3, 2, 5]
def baseStart_4097669 : Nat := 118140960795 + 4097669 * 2 ^ 59
def prefixEnd_4097669 : Nat := 4983230072969 + 3 ^ 40 * 4097669 * 2
def baseEnd_4097669 : Nat := 2104073760028433584892669

theorem tailTrace_4097669 : CollatzResearch.WordTrace tailWord_4097669 prefixEnd_4097669 2104073760028433584892669 := by
  unfold tailWord_4097669
  simp only [CollatzResearch.WordTrace]
  refine ⟨149454266591852513994304061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99636177727901675996202707 149454266591852513994304061)
  ·
    refine ⟨56045349971944692747864023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149454266591852513994304061 56045349971944692747864023)
    ·
      refine ⟨84068024957917039121796035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56045349971944692747864023 84068024957917039121796035)
      ·
        refine ⟨126102037436875558682694053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84068024957917039121796035 126102037436875558682694053)
        ·
          refine ⟨23644132019414167253005135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126102037436875558682694053 23644132019414167253005135)
          ·
            refine ⟨35466198029121250879507703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23644132019414167253005135 35466198029121250879507703)
            ·
              refine ⟨53199297043681876319261555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35466198029121250879507703 53199297043681876319261555)
              ·
                refine ⟨79798945565522814478892333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53199297043681876319261555 79798945565522814478892333)
                ·
                  refine ⟨29924604587071055429584625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79798945565522814478892333 29924604587071055429584625)
                  ·
                    refine ⟨22443453440303291572188469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29924604587071055429584625 22443453440303291572188469)
                    ·
                      refine ⟨2104073760028433584892669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22443453440303291572188469 2104073760028433584892669)
                      ·
                        rfl

theorem cell23_4097669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_4097669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097669 prefixEnd_4097669 := by exact prefixLift 4097669
  have htrace : WordTrace (prefixWord ++ tailWord_4097669) baseStart_4097669 baseEnd_4097669 := by
    simpa [prefixWord, tailWord_4097669, baseEnd_4097669] using wordTrace_append hprefix tailTrace_4097669
  have hstable : (prefixWord ++ tailWord_4097669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097669).length < 2 ^ (prefixWord ++ tailWord_4097669).sum := by decide
  have hdescent : baseEnd_4097669 < baseStart_4097669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097726 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_4097726 : Nat := 118140960795 + 4097726 * 2 ^ 59
def prefixEnd_4097726 : Nat := 4983230072969 + 3 ^ 40 * 4097726 * 2
def baseEnd_4097726 : Nat := 2104103028425739861879907

theorem tailTrace_4097726 : CollatzResearch.WordTrace tailWord_4097726 prefixEnd_4097726 2104103028425739861879907 := by
  unfold tailWord_4097726
  simp only [CollatzResearch.WordTrace]
  refine ⟨18682043194080751591141129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99637563701764008486086021 18682043194080751591141129)
  ·
    refine ⟨14011532395560563693355847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18682043194080751591141129 14011532395560563693355847)
    ·
      refine ⟨21017298593340845540033771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14011532395560563693355847 21017298593340845540033771)
      ·
        refine ⟨31525947890011268310050657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21017298593340845540033771 31525947890011268310050657)
        ·
          refine ⟨23644460917508451232537993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31525947890011268310050657 23644460917508451232537993)
          ·
            refine ⟨17733345688131338424403495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23644460917508451232537993 17733345688131338424403495)
            ·
              refine ⟨26600018532197007636605243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17733345688131338424403495 26600018532197007636605243)
              ·
                refine ⟨39900027798295511454907865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26600018532197007636605243 39900027798295511454907865)
                ·
                  refine ⟨29925020848721633591180899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39900027798295511454907865 29925020848721633591180899)
                  ·
                    refine ⟨44887531273082450386771349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29925020848721633591180899 44887531273082450386771349)
                    ·
                      refine ⟨2104103028425739861879907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44887531273082450386771349 2104103028425739861879907)
                      ·
                        rfl

theorem cell23_4097726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_4097726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097726 prefixEnd_4097726 := by exact prefixLift 4097726
  have htrace : WordTrace (prefixWord ++ tailWord_4097726) baseStart_4097726 baseEnd_4097726 := by
    simpa [prefixWord, tailWord_4097726, baseEnd_4097726] using wordTrace_append hprefix tailTrace_4097726
  have hstable : (prefixWord ++ tailWord_4097726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097726).length < 2 ^ (prefixWord ++ tailWord_4097726).sum := by decide
  have hdescent : baseEnd_4097726 < baseStart_4097726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097740 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 3, 4]
def baseStart_4097740 : Nat := 118140960795 + 4097740 * 2 ^ 59
def prefixEnd_4097740 : Nat := 4983230072969 + 3 ^ 40 * 4097740 * 2
def baseEnd_4097740 : Nat := 701370072384967602368281

theorem tailTrace_4097740 : CollatzResearch.WordTrace tailWord_4097740 prefixEnd_4097740 701370072384967602368281 := by
  unfold tailWord_4097740
  simp only [CollatzResearch.WordTrace]
  refine ⟨74728428087297646560069337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99637904116396862080092449 74728428087297646560069337)
  ·
    refine ⟨56046321065473234920052003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74728428087297646560069337 56046321065473234920052003)
    ·
      refine ⟨84069481598209852380078005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56046321065473234920052003 84069481598209852380078005)
      ·
        refine ⟨7881513899832173660632313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84069481598209852380078005 7881513899832173660632313)
        ·
          refine ⟨5911135424874130245474235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7881513899832173660632313 5911135424874130245474235)
          ·
            refine ⟨8866703137311195368211353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911135424874130245474235 8866703137311195368211353)
            ·
              refine ⟨6650027352983396526158515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8866703137311195368211353 6650027352983396526158515)
              ·
                refine ⟨9975041029475094789237773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6650027352983396526158515 9975041029475094789237773)
                ·
                  refine ⟨3740640386053160545964165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9975041029475094789237773 3740640386053160545964165)
                  ·
                    refine ⟨701370072384967602368281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3740640386053160545964165 701370072384967602368281)
                    ·
                      rfl

theorem cell23_4097740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_4097740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097740 prefixEnd_4097740 := by exact prefixLift 4097740
  have htrace : WordTrace (prefixWord ++ tailWord_4097740) baseStart_4097740 baseEnd_4097740 := by
    simpa [prefixWord, tailWord_4097740, baseEnd_4097740] using wordTrace_append hprefix tailTrace_4097740
  have hstable : (prefixWord ++ tailWord_4097740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097740).length < 2 ^ (prefixWord ++ tailWord_4097740).sum := by decide
  have hdescent : baseEnd_4097740 < baseStart_4097740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4097753 : List Nat := [1, 2, 1, 2, 3, 4, 3, 1, 6]
def baseStart_4097753 : Nat := 118140960795 + 4097753 * 2 ^ 59
def prefixEnd_4097753 : Nat := 4983230072969 + 3 ^ 40 * 4097753 * 2
def baseEnd_4097753 : Nat := 233790765822601250693587

theorem tailTrace_4097753 : CollatzResearch.WordTrace tailWord_4097753 prefixEnd_4097753 233790765822601250693587 := by
  unfold tailWord_4097753
  simp only [CollatzResearch.WordTrace]
  refine ⟨149457330323548196340361913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99638220215698797560241275 149457330323548196340361913)
  ·
    refine ⟨112092997742661147255271435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149457330323548196340361913 112092997742661147255271435)
    ·
      refine ⟨168139496613991720882907153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112092997742661147255271435 168139496613991720882907153)
      ·
        refine ⟨126104622460493790662180365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168139496613991720882907153 126104622460493790662180365)
        ·
          refine ⟨47289233422685171498317637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126104622460493790662180365 47289233422685171498317637)
          ·
            refine ⟨8866731266753469655934557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47289233422685171498317637 8866731266753469655934557)
            ·
              refine ⟨3325024225032551120975459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8866731266753469655934557 3325024225032551120975459)
              ·
                refine ⟨4987536337548826681463189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3325024225032551120975459 4987536337548826681463189)
                ·
                  refine ⟨233790765822601250693587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4987536337548826681463189 233790765822601250693587)
                  ·
                    rfl

theorem cell23_4097753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 6].length) (baseStart_4097753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4097753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4097753 prefixEnd_4097753 := by exact prefixLift 4097753
  have htrace : WordTrace (prefixWord ++ tailWord_4097753) baseStart_4097753 baseEnd_4097753 := by
    simpa [prefixWord, tailWord_4097753, baseEnd_4097753] using wordTrace_append hprefix tailTrace_4097753
  have hstable : (prefixWord ++ tailWord_4097753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4097753).length < 2 ^ (prefixWord ++ tailWord_4097753).sum := by decide
  have hdescent : baseEnd_4097753 < baseStart_4097753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4097753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
