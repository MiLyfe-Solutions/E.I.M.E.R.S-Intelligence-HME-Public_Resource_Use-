import V185TrunkScan21Chunk015

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_194623 : List Nat := [1, 1, 2, 2, 3, 1, 3, 8]
def baseStart_194623 : Nat := 118140960795 + 194623 * 2 ^ 59
def prefixEnd_194623 : Nat := 4983230072969 + 3 ^ 40 * 194623 * 2
def baseEnd_194623 : Nat := 14805206728903299306289

theorem tailTrace_194623 : CollatzResearch.WordTrace tailWord_194623 prefixEnd_194623 14805206728903299306289 := by
  unfold tailWord_194623
  simp only [CollatzResearch.WordTrace]
  refine ⟨7098483973921584807220523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4732322649281056538147015 7098483973921584807220523)
  ·
    refine ⟨10647725960882377210830785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7098483973921584807220523 10647725960882377210830785)
    ·
      refine ⟨7985794470661782908123089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10647725960882377210830785 7985794470661782908123089)
      ·
        refine ⟨5989345852996337181092317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7985794470661782908123089 5989345852996337181092317)
        ·
          refine ⟨2246004694873626442909619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5989345852996337181092317 2246004694873626442909619)
          ·
            refine ⟨3369007042310439664364429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2246004694873626442909619 3369007042310439664364429)
            ·
              refine ⟨1263377640866414874136661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3369007042310439664364429 1263377640866414874136661)
              ·
                refine ⟨14805206728903299306289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1263377640866414874136661 14805206728903299306289)
                ·
                  rfl

theorem cell21_194623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 8].length) (baseStart_194623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194623 prefixEnd_194623 := by exact prefixLift 194623
  have htrace : WordTrace (prefixWord ++ tailWord_194623) baseStart_194623 baseEnd_194623 := by
    simpa [prefixWord, tailWord_194623, baseEnd_194623] using wordTrace_append hprefix tailTrace_194623
  have hstable : (prefixWord ++ tailWord_194623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194623).length < 2 ^ (prefixWord ++ tailWord_194623).sum := by decide
  have hdescent : baseEnd_194623 < baseStart_194623 := by decide
  rcases family_descends (prefixWord ++ tailWord_194623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194719 : List Nat := [1, 1, 2, 6, 1, 3, 1, 2, 4]
def baseStart_194719 : Nat := 118140960795 + 194719 * 2 ^ 59
def prefixEnd_194719 : Nat := 4983230072969 + 3 ^ 40 * 194719 * 2
def baseEnd_194719 : Nat := 44437528694635064318671

theorem tailTrace_194719 : CollatzResearch.WordTrace tailWord_194719 prefixEnd_194719 44437528694635064318671 := by
  unfold tailWord_194719
  simp only [CollatzResearch.WordTrace]
  refine ⟨7101985381573793202715211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4734656921049195468476807 7101985381573793202715211)
  ·
    refine ⟨10652978072360689804072817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7101985381573793202715211 10652978072360689804072817)
    ·
      refine ⟨7989733554270517353054613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10652978072360689804072817 7989733554270517353054613)
      ·
        refine ⟨374518760356430500924435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7989733554270517353054613 374518760356430500924435)
        ·
          refine ⟨561778140534645751386653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374518760356430500924435 561778140534645751386653)
          ·
            refine ⟨210666802700492156769995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 561778140534645751386653 210666802700492156769995)
            ·
              refine ⟨316000204050738235154993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210666802700492156769995 316000204050738235154993)
              ·
                refine ⟨237000153038053676366245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316000204050738235154993 237000153038053676366245)
                ·
                  refine ⟨44437528694635064318671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237000153038053676366245 44437528694635064318671)
                  ·
                    rfl

theorem cell21_194719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 4].length) (baseStart_194719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194719 prefixEnd_194719 := by exact prefixLift 194719
  have htrace : WordTrace (prefixWord ++ tailWord_194719) baseStart_194719 baseEnd_194719 := by
    simpa [prefixWord, tailWord_194719, baseEnd_194719] using wordTrace_append hprefix tailTrace_194719
  have hstable : (prefixWord ++ tailWord_194719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194719).length < 2 ^ (prefixWord ++ tailWord_194719).sum := by decide
  have hdescent : baseEnd_194719 < baseStart_194719 := by decide
  rcases family_descends (prefixWord ++ tailWord_194719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194750 : List Nat := [4, 2, 1, 1, 4, 2, 2, 5]
def baseStart_194750 : Nat := 118140960795 + 194750 * 2 ^ 59
def prefixEnd_194750 : Nat := 4983230072969 + 3 ^ 40 * 194750 * 2
def baseEnd_194750 : Nat := 14814867772328633100647

theorem tailTrace_194750 : CollatzResearch.WordTrace tailWord_194750 prefixEnd_194750 14814867772328633100647 := by
  unfold tailWord_194750
  simp only [CollatzResearch.WordTrace]
  refine ⟨887889505557685687136713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4735410696307656998062469 887889505557685687136713)
  ·
    refine ⟨665917129168264265352535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 887889505557685687136713 665917129168264265352535)
    ·
      refine ⟨998875693752396398028803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 665917129168264265352535 998875693752396398028803)
      ·
        refine ⟨1498313540628594597043205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 998875693752396398028803 1498313540628594597043205)
        ·
          refine ⟨280933788867861486945601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1498313540628594597043205 280933788867861486945601)
          ·
            refine ⟨210700341650896115209201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280933788867861486945601 210700341650896115209201)
            ·
              refine ⟨158025256238172086406901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210700341650896115209201 158025256238172086406901)
              ·
                refine ⟨14814867772328633100647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158025256238172086406901 14814867772328633100647)
                ·
                  rfl

theorem cell21_194750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_194750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194750 prefixEnd_194750 := by exact prefixLift 194750
  have htrace : WordTrace (prefixWord ++ tailWord_194750) baseStart_194750 baseEnd_194750 := by
    simpa [prefixWord, tailWord_194750, baseEnd_194750] using wordTrace_append hprefix tailTrace_194750
  have hstable : (prefixWord ++ tailWord_194750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194750).length < 2 ^ (prefixWord ++ tailWord_194750).sum := by decide
  have hdescent : baseEnd_194750 < baseStart_194750 := by decide
  rcases family_descends (prefixWord ++ tailWord_194750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194792 : List Nat := [2, 1, 4, 1, 2, 3, 2, 6]
def baseStart_194792 : Nat := 118140960795 + 194792 * 2 ^ 59
def prefixEnd_194792 : Nat := 4983230072969 + 3 ^ 40 * 194792 * 2
def baseEnd_194792 : Nat := 14818062763067719867285

theorem tailTrace_194792 : CollatzResearch.WordTrace tailWord_194792 prefixEnd_194792 14818062763067719867285 := by
  unfold tailWord_194792
  simp only [CollatzResearch.WordTrace]
  refine ⟨3552323955154663335061315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4736431940206217780081753 3552323955154663335061315)
  ·
    refine ⟨5328485932731995002591973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3552323955154663335061315 5328485932731995002591973)
    ·
      refine ⟨999091112387249062985995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5328485932731995002591973 999091112387249062985995)
      ·
        refine ⟨1498636668580873594478993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 999091112387249062985995 1498636668580873594478993)
        ·
          refine ⟨1123977501435655195859245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1498636668580873594478993 1123977501435655195859245)
          ·
            refine ⟨421491563038370698447217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1123977501435655195859245 421491563038370698447217)
            ·
              refine ⟨316118672278778023835413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421491563038370698447217 316118672278778023835413)
              ·
                refine ⟨14818062763067719867285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 316118672278778023835413 14818062763067719867285)
                ·
                  rfl

theorem cell21_194792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 6].length) (baseStart_194792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194792 prefixEnd_194792 := by exact prefixLift 194792
  have htrace : WordTrace (prefixWord ++ tailWord_194792) baseStart_194792 baseEnd_194792 := by
    simpa [prefixWord, tailWord_194792, baseEnd_194792] using wordTrace_append hprefix tailTrace_194792
  have hstable : (prefixWord ++ tailWord_194792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194792).length < 2 ^ (prefixWord ++ tailWord_194792).sum := by decide
  have hdescent : baseEnd_194792 < baseStart_194792 := by decide
  rcases family_descends (prefixWord ++ tailWord_194792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194837 : List Nat := [1, 3, 2, 1, 2, 1, 3, 4, 4]
def baseStart_194837 : Nat := 118140960795 + 194837 * 2 ^ 59
def prefixEnd_194837 : Nat := 4983230072969 + 3 ^ 40 * 194837 * 2
def baseEnd_194837 : Nat := 44464457902293081351763

theorem tailTrace_194837 : CollatzResearch.WordTrace tailWord_194837 prefixEnd_194837 44464457902293081351763 := by
  unfold tailWord_194837
  simp only [CollatzResearch.WordTrace]
  refine ⟨7106289195146299355510765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4737526130097532903673843 7106289195146299355510765)
  ·
    refine ⟨2664858448179862258316537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7106289195146299355510765 2664858448179862258316537)
    ·
      refine ⟨1998643836134896693737403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2664858448179862258316537 1998643836134896693737403)
      ·
        refine ⟨2997965754202345040606105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1998643836134896693737403 2997965754202345040606105)
        ·
          refine ⟨2248474315651758780454579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2997965754202345040606105 2248474315651758780454579)
          ·
            refine ⟨3372711473477638170681869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248474315651758780454579 3372711473477638170681869)
            ·
              refine ⟨1264766802554114314005701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3372711473477638170681869 1264766802554114314005701)
              ·
                refine ⟨237143775478896433876069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1264766802554114314005701 237143775478896433876069)
                ·
                  refine ⟨44464457902293081351763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237143775478896433876069 44464457902293081351763)
                  ·
                    rfl

theorem cell21_194837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_194837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194837 prefixEnd_194837 := by exact prefixLift 194837
  have htrace : WordTrace (prefixWord ++ tailWord_194837) baseStart_194837 baseEnd_194837 := by
    simpa [prefixWord, tailWord_194837, baseEnd_194837] using wordTrace_append hprefix tailTrace_194837
  have hstable : (prefixWord ++ tailWord_194837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194837).length < 2 ^ (prefixWord ++ tailWord_194837).sum := by decide
  have hdescent : baseEnd_194837 < baseStart_194837 := by decide
  rcases family_descends (prefixWord ++ tailWord_194837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194933 : List Nat := [1, 3, 4, 1, 2, 3, 1, 3, 3]
def baseStart_194933 : Nat := 118140960795 + 194933 * 2 ^ 59
def prefixEnd_194933 : Nat := 4983230072969 + 3 ^ 40 * 194933 * 2
def baseEnd_194933 : Nat := 44486366410218247751567

theorem tailTrace_194933 : CollatzResearch.WordTrace tailWord_194933 prefixEnd_194933 44486366410218247751567 := by
  unfold tailWord_194933
  simp only [CollatzResearch.WordTrace]
  refine ⟨7109790602798507751005453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4739860401865671834003635 7109790602798507751005453)
  ·
    refine ⟨2666171476049440406627045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7109790602798507751005453 2666171476049440406627045)
    ·
      refine ⟨499907151759270076242571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2666171476049440406627045 499907151759270076242571)
      ·
        refine ⟨749860727638905114363857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499907151759270076242571 749860727638905114363857)
        ·
          refine ⟨562395545729178835772893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 749860727638905114363857 562395545729178835772893)
          ·
            refine ⟨210898329648442063414835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 562395545729178835772893 210898329648442063414835)
            ·
              refine ⟨316347494472663095122253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210898329648442063414835 316347494472663095122253)
              ·
                refine ⟨118630310427248660670845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316347494472663095122253 118630310427248660670845)
                ·
                  refine ⟨44486366410218247751567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118630310427248660670845 44486366410218247751567)
                  ·
                    rfl

theorem cell21_194933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_194933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194933 prefixEnd_194933 := by exact prefixLift 194933
  have htrace : WordTrace (prefixWord ++ tailWord_194933) baseStart_194933 baseEnd_194933 := by
    simpa [prefixWord, tailWord_194933, baseEnd_194933] using wordTrace_append hprefix tailTrace_194933
  have hstable : (prefixWord ++ tailWord_194933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194933).length < 2 ^ (prefixWord ++ tailWord_194933).sum := by decide
  have hdescent : baseEnd_194933 < baseStart_194933 := by decide
  rcases family_descends (prefixWord ++ tailWord_194933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194964 : List Nat := [2, 4, 2, 1, 3, 2, 2, 1, 4]
def baseStart_194964 : Nat := 118140960795 + 194964 * 2 ^ 59
def prefixEnd_194964 : Nat := 4983230072969 + 3 ^ 40 * 194964 * 2
def baseEnd_194964 : Nat := 44493441032569082734837

theorem tailTrace_194964 : CollatzResearch.WordTrace tailWord_194964 prefixEnd_194964 44493441032569082734837 := by
  unfold tailWord_194964
  simp only [CollatzResearch.WordTrace]
  refine ⟨3555460632843100022691973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4740614177124133363589297 3555460632843100022691973)
  ·
    refine ⟨666648868658081254254745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3555460632843100022691973 666648868658081254254745)
    ·
      refine ⟨499986651493560940691059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 666648868658081254254745 499986651493560940691059)
      ·
        refine ⟨749979977240341411036589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499986651493560940691059 749979977240341411036589)
        ·
          refine ⟨281242491465128029138721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 749979977240341411036589 281242491465128029138721)
          ·
            refine ⟨210931868598846021854041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281242491465128029138721 210931868598846021854041)
            ·
              refine ⟨158198901449134516390531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210931868598846021854041 158198901449134516390531)
              ·
                refine ⟨237298352173701774585797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158198901449134516390531 237298352173701774585797)
                ·
                  refine ⟨44493441032569082734837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237298352173701774585797 44493441032569082734837)
                  ·
                    rfl

theorem cell21_194964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_194964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194964 prefixEnd_194964 := by exact prefixLift 194964
  have htrace : WordTrace (prefixWord ++ tailWord_194964) baseStart_194964 baseEnd_194964 := by
    simpa [prefixWord, tailWord_194964, baseEnd_194964] using wordTrace_append hprefix tailTrace_194964
  have hstable : (prefixWord ++ tailWord_194964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194964).length < 2 ^ (prefixWord ++ tailWord_194964).sum := by decide
  have hdescent : baseEnd_194964 < baseStart_194964 := by decide
  rcases family_descends (prefixWord ++ tailWord_194964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195034 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 5]
def baseStart_195034 : Nat := 118140960795 + 195034 * 2 ^ 59
def prefixEnd_195034 : Nat := 4983230072969 + 3 ^ 40 * 195034 * 2
def baseEnd_195034 : Nat := 44509415986264516568027

theorem tailTrace_195034 : CollatzResearch.WordTrace tailWord_195034 prefixEnd_195034 44509415986264516568027 := by
  unfold tailWord_195034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1778368593858150500108039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4742316250288401333621437 1778368593858150500108039)
  ·
    refine ⟨2667552890787225750162059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1778368593858150500108039 2667552890787225750162059)
    ·
      refine ⟨4001329336180838625243089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2667552890787225750162059 4001329336180838625243089)
      ·
        refine ⟨3000997002135628968932317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4001329336180838625243089 3000997002135628968932317)
        ·
          refine ⟨1125373875800860863349619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3000997002135628968932317 1125373875800860863349619)
          ·
            refine ⟨1688060813701291295024429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125373875800860863349619 1688060813701291295024429)
            ·
              refine ⟨633022805137984235634161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1688060813701291295024429 633022805137984235634161)
              ·
                refine ⟨474767103853488176725621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 633022805137984235634161 474767103853488176725621)
                ·
                  refine ⟨44509415986264516568027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 474767103853488176725621 44509415986264516568027)
                  ·
                    rfl

theorem cell21_195034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_195034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195034 prefixEnd_195034 := by exact prefixLift 195034
  have htrace : WordTrace (prefixWord ++ tailWord_195034) baseStart_195034 baseEnd_195034 := by
    simpa [prefixWord, tailWord_195034, baseEnd_195034] using wordTrace_append hprefix tailTrace_195034
  have hstable : (prefixWord ++ tailWord_195034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195034).length < 2 ^ (prefixWord ++ tailWord_195034).sum := by decide
  have hdescent : baseEnd_195034 < baseStart_195034 := by decide
  rcases family_descends (prefixWord ++ tailWord_195034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195051 : List Nat := [1, 1, 1, 1, 2, 3, 6, 3, 3]
def baseStart_195051 : Nat := 118140960795 + 195051 * 2 ^ 59
def prefixEnd_195051 : Nat := 4983230072969 + 3 ^ 40 * 195051 * 2
def baseEnd_195051 : Nat := 44513295617876264784659

theorem tailTrace_195051 : CollatzResearch.WordTrace tailWord_195051 prefixEnd_195051 44513295617876264784659 := by
  unfold tailWord_195051
  simp only [CollatzResearch.WordTrace]
  refine ⟨7114094416371013903801007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4742729610914009269200671 7114094416371013903801007)
  ·
    refine ⟨10671141624556520855701511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7114094416371013903801007 10671141624556520855701511)
    ·
      refine ⟨16006712436834781283552267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10671141624556520855701511 16006712436834781283552267)
      ·
        refine ⟨24010068655252171925328401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16006712436834781283552267 24010068655252171925328401)
        ·
          refine ⟨18007551491439128943996301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24010068655252171925328401 18007551491439128943996301)
          ·
            refine ⟨6752831809289673353998613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18007551491439128943996301 6752831809289673353998613)
            ·
              refine ⟨316538991060453438468685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6752831809289673353998613 316538991060453438468685)
              ·
                refine ⟨118702121647670039425757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316538991060453438468685 118702121647670039425757)
                ·
                  refine ⟨44513295617876264784659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118702121647670039425757 44513295617876264784659)
                  ·
                    rfl

theorem cell21_195051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 3].length) (baseStart_195051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195051 prefixEnd_195051 := by exact prefixLift 195051
  have htrace : WordTrace (prefixWord ++ tailWord_195051) baseStart_195051 baseEnd_195051 := by
    simpa [prefixWord, tailWord_195051, baseEnd_195051] using wordTrace_append hprefix tailTrace_195051
  have hstable : (prefixWord ++ tailWord_195051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195051).length < 2 ^ (prefixWord ++ tailWord_195051).sum := by decide
  have hdescent : baseEnd_195051 < baseStart_195051 := by decide
  rcases family_descends (prefixWord ++ tailWord_195051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195065 : List Nat := [1, 2, 1, 3, 1, 2, 5, 2, 4]
def baseStart_195065 : Nat := 118140960795 + 195065 * 2 ^ 59
def prefixEnd_195065 : Nat := 4983230072969 + 3 ^ 40 * 195065 * 2
def baseEnd_195065 : Nat := 44516490608615351551297

theorem tailTrace_195065 : CollatzResearch.WordTrace tailWord_195065 prefixEnd_195065 44516490608615351551297 := by
  unfold tailWord_195065
  simp only [CollatzResearch.WordTrace]
  refine ⟨7114605038320294294810649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4743070025546862863207099 7114605038320294294810649)
  ·
    refine ⟨5335953778740220721107987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7114605038320294294810649 5335953778740220721107987)
    ·
      refine ⟨8003930668110331081661981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5335953778740220721107987 8003930668110331081661981)
      ·
        refine ⟨3001474000541374155623243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8003930668110331081661981 3001474000541374155623243)
        ·
          refine ⟨4502211000812061233434865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3001474000541374155623243 4502211000812061233434865)
          ·
            refine ⟨3376658250609045925076149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4502211000812061233434865 3376658250609045925076149)
            ·
              refine ⟨316561710994598055475889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3376658250609045925076149 316561710994598055475889)
              ·
                refine ⟨237421283245948541606917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316561710994598055475889 237421283245948541606917)
                ·
                  refine ⟨44516490608615351551297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237421283245948541606917 44516490608615351551297)
                  ·
                    rfl

theorem cell21_195065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_195065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195065 prefixEnd_195065 := by exact prefixLift 195065
  have htrace : WordTrace (prefixWord ++ tailWord_195065) baseStart_195065 baseEnd_195065 := by
    simpa [prefixWord, tailWord_195065, baseEnd_195065] using wordTrace_append hprefix tailTrace_195065
  have hstable : (prefixWord ++ tailWord_195065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195065).length < 2 ^ (prefixWord ++ tailWord_195065).sum := by decide
  have hdescent : baseEnd_195065 < baseStart_195065 := by decide
  rcases family_descends (prefixWord ++ tailWord_195065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195082 : List Nat := [3, 1, 2, 2, 2, 1, 5, 1, 4]
def baseStart_195082 : Nat := 118140960795 + 195082 * 2 ^ 59
def prefixEnd_195082 : Nat := 4983230072969 + 3 ^ 40 * 195082 * 2
def baseEnd_195082 : Nat := 44520370240227099767929

theorem tailTrace_195082 : CollatzResearch.WordTrace tailWord_195082 prefixEnd_195082 44520370240227099767929 := by
  unfold tailWord_195082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1778806269814676549544875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4743483386172470798786333 1778806269814676549544875)
  ·
    refine ⟨2668209404722014824317313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1778806269814676549544875 2668209404722014824317313)
    ·
      refine ⟨2001157053541511118237985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2668209404722014824317313 2001157053541511118237985)
      ·
        refine ⟨1500867790156133338678489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2001157053541511118237985 1500867790156133338678489)
        ·
          refine ⟨1125650842617100004008867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1500867790156133338678489 1125650842617100004008867)
          ·
            refine ⟨1688476263925650006013301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125650842617100004008867 1688476263925650006013301)
            ·
              refine ⟨158294649743029688063747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1688476263925650006013301 158294649743029688063747)
              ·
                refine ⟨237441974614544532095621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158294649743029688063747 237441974614544532095621)
                ·
                  refine ⟨44520370240227099767929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237441974614544532095621 44520370240227099767929)
                  ·
                    rfl

theorem cell21_195082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_195082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195082 prefixEnd_195082 := by exact prefixLift 195082
  have htrace : WordTrace (prefixWord ++ tailWord_195082) baseStart_195082 baseEnd_195082 := by
    simpa [prefixWord, tailWord_195082, baseEnd_195082] using wordTrace_append hprefix tailTrace_195082
  have hstable : (prefixWord ++ tailWord_195082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195082).length < 2 ^ (prefixWord ++ tailWord_195082).sum := by decide
  have hdescent : baseEnd_195082 < baseStart_195082 := by decide
  rcases family_descends (prefixWord ++ tailWord_195082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195096 : List Nat := [2, 1, 2, 3, 3, 1, 4, 5]
def baseStart_195096 : Nat := 118140960795 + 195096 * 2 ^ 59
def prefixEnd_195096 : Nat := 4983230072969 + 3 ^ 40 * 195096 * 2
def baseEnd_195096 : Nat := 14841188410322062178189

theorem tailTrace_195096 : CollatzResearch.WordTrace tailWord_195096 prefixEnd_195096 14841188410322062178189 := by
  unfold tailWord_195096
  simp only [CollatzResearch.WordTrace]
  refine ⟨3557867850603993294594571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4743823800805324392792761 3557867850603993294594571)
  ·
    refine ⟨5336801775905989941891857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3557867850603993294594571 5336801775905989941891857)
    ·
      refine ⟨4002601331929492456418893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5336801775905989941891857 4002601331929492456418893)
      ·
        refine ⟨1500975499473559671157085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4002601331929492456418893 1500975499473559671157085)
        ·
          refine ⟨562865812302584876683907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1500975499473559671157085 562865812302584876683907)
          ·
            refine ⟨844298718453877315025861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562865812302584876683907 844298718453877315025861)
            ·
              refine ⟨158306009710101996567349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 844298718453877315025861 158306009710101996567349)
              ·
                refine ⟨14841188410322062178189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158306009710101996567349 14841188410322062178189)
                ·
                  rfl

theorem cell21_195096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 5].length) (baseStart_195096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195096 prefixEnd_195096 := by exact prefixLift 195096
  have htrace : WordTrace (prefixWord ++ tailWord_195096) baseStart_195096 baseEnd_195096 := by
    simpa [prefixWord, tailWord_195096, baseEnd_195096] using wordTrace_append hprefix tailTrace_195096
  have hstable : (prefixWord ++ tailWord_195096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195096).length < 2 ^ (prefixWord ++ tailWord_195096).sum := by decide
  have hdescent : baseEnd_195096 < baseStart_195096 := by decide
  rcases family_descends (prefixWord ++ tailWord_195096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195141 : List Nat := [1, 3, 1, 1, 1, 6, 1, 3, 4]
def baseStart_195141 : Nat := 118140960795 + 195141 * 2 ^ 59
def prefixEnd_195141 : Nat := 4983230072969 + 3 ^ 40 * 195141 * 2
def baseEnd_195141 : Nat := 44533834844056108284475

theorem tailTrace_195141 : CollatzResearch.WordTrace tailWord_195141 prefixEnd_195141 44533834844056108284475 := by
  unfold tailWord_195141
  simp only [CollatzResearch.WordTrace]
  refine ⟨7117376986044959274577277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4744917990696639516384851 7117376986044959274577277)
  ·
    refine ⟨2669016369766859727966479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7117376986044959274577277 2669016369766859727966479)
    ·
      refine ⟨4003524554650289591949719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2669016369766859727966479 4003524554650289591949719)
      ·
        refine ⟨6005286831975434387924579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4003524554650289591949719 6005286831975434387924579)
        ·
          refine ⟨9007930247963151581886869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6005286831975434387924579 9007930247963151581886869)
          ·
            refine ⟨422246730373272730400947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9007930247963151581886869 422246730373272730400947)
            ·
              refine ⟨633370095559909095601421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422246730373272730400947 633370095559909095601421)
              ·
                refine ⟨237513785834965910850533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 633370095559909095601421 237513785834965910850533)
                ·
                  refine ⟨44533834844056108284475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237513785834965910850533 44533834844056108284475)
                  ·
                    rfl

theorem cell21_195141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_195141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195141 prefixEnd_195141 := by exact prefixLift 195141
  have htrace : WordTrace (prefixWord ++ tailWord_195141) baseStart_195141 baseEnd_195141 := by
    simpa [prefixWord, tailWord_195141, baseEnd_195141] using wordTrace_append hprefix tailTrace_195141
  have hstable : (prefixWord ++ tailWord_195141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195141).length < 2 ^ (prefixWord ++ tailWord_195141).sum := by decide
  have hdescent : baseEnd_195141 < baseStart_195141 := by decide
  rcases family_descends (prefixWord ++ tailWord_195141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195189 : List Nat := [1, 3, 4, 2, 2, 2, 1, 6]
def baseStart_195189 : Nat := 118140960795 + 195189 * 2 ^ 59
def prefixEnd_195189 : Nat := 4983230072969 + 3 ^ 40 * 195189 * 2
def baseEnd_195189 : Nat := 14848263032672897161459

theorem tailTrace_195189 : CollatzResearch.WordTrace tailWord_195189 prefixEnd_195189 14848263032672897161459 := by
  unfold tailWord_195189
  simp only [CollatzResearch.WordTrace]
  refine ⟨7119127689871063472324621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4746085126580708981549747 7119127689871063472324621)
  ·
    refine ⟨2669672883701648802121733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7119127689871063472324621 2669672883701648802121733)
    ·
      refine ⟨500563665694059150397825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2669672883701648802121733 500563665694059150397825)
      ·
        refine ⟨375422749270544362798369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500563665694059150397825 375422749270544362798369)
        ·
          refine ⟨281567061952908272098777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375422749270544362798369 281567061952908272098777)
          ·
            refine ⟨211175296464681204074083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281567061952908272098777 211175296464681204074083)
            ·
              refine ⟨316762944697021806111125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211175296464681204074083 316762944697021806111125)
              ·
                refine ⟨14848263032672897161459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 316762944697021806111125 14848263032672897161459)
                ·
                  rfl

theorem cell21_195189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 6].length) (baseStart_195189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195189 prefixEnd_195189 := by exact prefixLift 195189
  have htrace : WordTrace (prefixWord ++ tailWord_195189) baseStart_195189 baseEnd_195189 := by
    simpa [prefixWord, tailWord_195189, baseEnd_195189] using wordTrace_append hprefix tailTrace_195189
  have hstable : (prefixWord ++ tailWord_195189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195189).length < 2 ^ (prefixWord ++ tailWord_195189).sum := by decide
  have hdescent : baseEnd_195189 < baseStart_195189 := by decide
  rcases family_descends (prefixWord ++ tailWord_195189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195220 : List Nat := [2, 4, 2, 2, 1, 1, 1, 5, 3]
def baseStart_195220 : Nat := 118140960795 + 195220 * 2 ^ 59
def prefixEnd_195220 : Nat := 4983230072969 + 3 ^ 40 * 195220 * 2
def baseEnd_195220 : Nat := 44551863720369526467647

theorem tailTrace_195220 : CollatzResearch.WordTrace tailWord_195220 prefixEnd_195220 44551863720369526467647 := by
  unfold tailWord_195220
  simp only [CollatzResearch.WordTrace]
  refine ⟨3560129176379377883351557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4746838901839170511135409 3560129176379377883351557)
  ·
    refine ⟨667524220571133353128417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3560129176379377883351557 667524220571133353128417)
    ·
      refine ⟨500643165428350014846313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 667524220571133353128417 500643165428350014846313)
      ·
        refine ⟨375482374071262511134735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500643165428350014846313 375482374071262511134735)
        ·
          refine ⟨563223561106893766702103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375482374071262511134735 563223561106893766702103)
          ·
            refine ⟨844835341660340650053155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563223561106893766702103 844835341660340650053155)
            ·
              refine ⟨1267253012490510975079733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844835341660340650053155 1267253012490510975079733)
              ·
                refine ⟨118804969920985403913725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1267253012490510975079733 118804969920985403913725)
                ·
                  refine ⟨44551863720369526467647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118804969920985403913725 44551863720369526467647)
                  ·
                    rfl

theorem cell21_195220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_195220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195220 prefixEnd_195220 := by exact prefixLift 195220
  have htrace : WordTrace (prefixWord ++ tailWord_195220) baseStart_195220 baseEnd_195220 := by
    simpa [prefixWord, tailWord_195220, baseEnd_195220] using wordTrace_append hprefix tailTrace_195220
  have hstable : (prefixWord ++ tailWord_195220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195220).length < 2 ^ (prefixWord ++ tailWord_195220).sum := by decide
  have hdescent : baseEnd_195220 < baseStart_195220 := by decide
  rcases family_descends (prefixWord ++ tailWord_195220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195262 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_195262 : Nat := 118140960795 + 195262 * 2 ^ 59
def prefixEnd_195262 : Nat := 4983230072969 + 3 ^ 40 * 195262 * 2
def baseEnd_195262 : Nat := 44561448692586786767561

theorem tailTrace_195262 : CollatzResearch.WordTrace tailWord_195262 prefixEnd_195262 44561448692586786767561 := by
  unfold tailWord_195262
  simp only [CollatzResearch.WordTrace]
  refine ⟨890223777325824617466505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4747860145737731293154693 890223777325824617466505)
  ·
    refine ⟨667667832994368463099879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 890223777325824617466505 667667832994368463099879)
    ·
      refine ⟨1001501749491552694649819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 667667832994368463099879 1001501749491552694649819)
      ·
        refine ⟨1502252624237329041974729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1001501749491552694649819 1502252624237329041974729)
        ·
          refine ⟨1126689468177996781481047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1502252624237329041974729 1126689468177996781481047)
          ·
            refine ⟨1690034202266995172221571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126689468177996781481047 1690034202266995172221571)
            ·
              refine ⟨2535051303400492758332357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690034202266995172221571 2535051303400492758332357)
              ·
                refine ⟨475322119387592392187317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2535051303400492758332357 475322119387592392187317)
                ·
                  refine ⟨44561448692586786767561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 475322119387592392187317 44561448692586786767561)
                  ·
                    rfl

theorem cell21_195262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_195262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195262 prefixEnd_195262 := by exact prefixLift 195262
  have htrace : WordTrace (prefixWord ++ tailWord_195262) baseStart_195262 baseEnd_195262 := by
    simpa [prefixWord, tailWord_195262, baseEnd_195262] using wordTrace_append hprefix tailTrace_195262
  have hstable : (prefixWord ++ tailWord_195262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195262).length < 2 ^ (prefixWord ++ tailWord_195262).sum := by decide
  have hdescent : baseEnd_195262 < baseStart_195262 := by decide
  rcases family_descends (prefixWord ++ tailWord_195262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195265 : List Nat := [1, 2, 6, 2, 1, 1, 1, 7]
def baseStart_195265 : Nat := 118140960795 + 195265 * 2 ^ 59
def prefixEnd_195265 : Nat := 4983230072969 + 3 ^ 40 * 195265 * 2
def baseEnd_195265 : Nat := 14854044444486482739185

theorem tailTrace_195265 : CollatzResearch.WordTrace tailWord_195265 prefixEnd_195265 14854044444486482739185 := by
  unfold tailWord_195265
  simp only [CollatzResearch.WordTrace]
  refine ⟨7121899637595728452091249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4747933091730485634727499 7121899637595728452091249)
  ·
    refine ⟨5341424728196796339068437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7121899637595728452091249 5341424728196796339068437)
    ·
      refine ⟨250379284134224828393833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5341424728196796339068437 250379284134224828393833)
      ·
        refine ⟨187784463100668621295375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250379284134224828393833 187784463100668621295375)
        ·
          refine ⟨281676694651002931943063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187784463100668621295375 281676694651002931943063)
          ·
            refine ⟨422515041976504397914595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281676694651002931943063 422515041976504397914595)
            ·
              refine ⟨633772562964756596871893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422515041976504397914595 633772562964756596871893)
              ·
                refine ⟨14854044444486482739185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 633772562964756596871893 14854044444486482739185)
                ·
                  rfl

theorem cell21_195265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 7].length) (baseStart_195265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195265 prefixEnd_195265 := by exact prefixLift 195265
  have htrace : WordTrace (prefixWord ++ tailWord_195265) baseStart_195265 baseEnd_195265 := by
    simpa [prefixWord, tailWord_195265, baseEnd_195265] using wordTrace_append hprefix tailTrace_195265
  have hstable : (prefixWord ++ tailWord_195265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195265).length < 2 ^ (prefixWord ++ tailWord_195265).sum := by decide
  have hdescent : baseEnd_195265 < baseStart_195265 := by decide
  rcases family_descends (prefixWord ++ tailWord_195265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195310 : List Nat := [4, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_195310 : Nat := 118140960795 + 195310 * 2 ^ 59
def prefixEnd_195310 : Nat := 4983230072969 + 3 ^ 40 * 195310 * 2
def baseEnd_195310 : Nat := 44572402946549369967463

theorem tailTrace_195310 : CollatzResearch.WordTrace tailWord_195310 prefixEnd_195310 44572402946549369967463 := by
  unfold tailWord_195310
  simp only [CollatzResearch.WordTrace]
  refine ⟨890442615304087642184923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4749027281621800758319589 890442615304087642184923)
  ·
    refine ⟨1335663922956131463277385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 890442615304087642184923 1335663922956131463277385)
    ·
      refine ⟨1001747942217098597458039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1335663922956131463277385 1001747942217098597458039)
      ·
        refine ⟨1502621913325647896187059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1001747942217098597458039 1502621913325647896187059)
        ·
          refine ⟨2253932869988471844280589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1502621913325647896187059 2253932869988471844280589)
          ·
            refine ⟨845224826245676941605221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2253932869988471844280589 845224826245676941605221)
            ·
              refine ⟨158479654921064426550979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 845224826245676941605221 158479654921064426550979)
              ·
                refine ⟨237719482381596639826469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158479654921064426550979 237719482381596639826469)
                ·
                  refine ⟨44572402946549369967463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237719482381596639826469 44572402946549369967463)
                  ·
                    rfl

theorem cell21_195310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_195310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195310 prefixEnd_195310 := by exact prefixLift 195310
  have htrace : WordTrace (prefixWord ++ tailWord_195310) baseStart_195310 baseEnd_195310 := by
    simpa [prefixWord, tailWord_195310, baseEnd_195310] using wordTrace_append hprefix tailTrace_195310
  have hstable : (prefixWord ++ tailWord_195310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195310).length < 2 ^ (prefixWord ++ tailWord_195310).sum := by decide
  have hdescent : baseEnd_195310 < baseStart_195310 := by decide
  rcases family_descends (prefixWord ++ tailWord_195310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195321 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 5]
def baseStart_195321 : Nat := 118140960795 + 195321 * 2 ^ 59
def prefixEnd_195321 : Nat := 4983230072969 + 3 ^ 40 * 195321 * 2
def baseEnd_195321 : Nat := 44574913296415795284107

theorem tailTrace_195321 : CollatzResearch.WordTrace tailWord_195321 prefixEnd_195321 44574913296415795284107 := by
  unfold tailWord_195321
  simp only [CollatzResearch.WordTrace]
  refine ⟨7123942125392850016129817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4749294750261900010753211 7123942125392850016129817)
  ·
    refine ⟨5342956594044637512097363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7123942125392850016129817 5342956594044637512097363)
    ·
      refine ⟨8014434891066956268146045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5342956594044637512097363 8014434891066956268146045)
      ·
        refine ⟨3005413084150108600554767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8014434891066956268146045 3005413084150108600554767)
        ·
          refine ⟨4508119626225162900832151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3005413084150108600554767 4508119626225162900832151)
          ·
            refine ⟨6762179439337744351248227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508119626225162900832151 6762179439337744351248227)
            ·
              refine ⟨10143269159006616526872341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6762179439337744351248227 10143269159006616526872341)
              ·
                refine ⟨475465741828435149697141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10143269159006616526872341 475465741828435149697141)
                ·
                  refine ⟨44574913296415795284107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 475465741828435149697141 44574913296415795284107)
                  ·
                    rfl

theorem cell21_195321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_195321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195321 prefixEnd_195321 := by exact prefixLift 195321
  have htrace : WordTrace (prefixWord ++ tailWord_195321) baseStart_195321 baseEnd_195321 := by
    simpa [prefixWord, tailWord_195321, baseEnd_195321] using wordTrace_append hprefix tailTrace_195321
  have hstable : (prefixWord ++ tailWord_195321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195321).length < 2 ^ (prefixWord ++ tailWord_195321).sum := by decide
  have hdescent : baseEnd_195321 < baseStart_195321 := by decide
  rcases family_descends (prefixWord ++ tailWord_195321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195383 : List Nat := [1, 1, 3, 1, 2, 1, 7, 5]
def baseStart_195383 : Nat := 118140960795 + 195383 * 2 ^ 59
def prefixEnd_195383 : Nat := 4983230072969 + 3 ^ 40 * 195383 * 2
def baseEnd_195383 : Nat := 14863020847039155083549

theorem tailTrace_195383 : CollatzResearch.WordTrace tailWord_195383 prefixEnd_195383 14863020847039155083549 := by
  unfold tailWord_195383
  simp only [CollatzResearch.WordTrace]
  refine ⟨7126203451168234604886803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4750802300778823069924535 7126203451168234604886803)
  ·
    refine ⟨10689305176752351907330205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7126203451168234604886803 10689305176752351907330205)
    ·
      refine ⟨4008489441282131965248827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10689305176752351907330205 4008489441282131965248827)
      ·
        refine ⟨6012734161923197947873241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4008489441282131965248827 6012734161923197947873241)
        ·
          refine ⟨4509550621442398460904931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6012734161923197947873241 4509550621442398460904931)
          ·
            refine ⟨6764325932163597691357397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4509550621442398460904931 6764325932163597691357397)
            ·
              refine ⟨158538889035084320891189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6764325932163597691357397 158538889035084320891189)
              ·
                refine ⟨14863020847039155083549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158538889035084320891189 14863020847039155083549)
                ·
                  rfl

theorem cell21_195383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 5].length) (baseStart_195383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195383 prefixEnd_195383 := by exact prefixLift 195383
  have htrace : WordTrace (prefixWord ++ tailWord_195383) baseStart_195383 baseEnd_195383 := by
    simpa [prefixWord, tailWord_195383, baseEnd_195383] using wordTrace_append hprefix tailTrace_195383
  have hstable : (prefixWord ++ tailWord_195383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195383).length < 2 ^ (prefixWord ++ tailWord_195383).sum := by decide
  have hdescent : baseEnd_195383 < baseStart_195383 := by decide
  rcases family_descends (prefixWord ++ tailWord_195383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195510 : List Nat := [5, 1, 4, 1, 2, 8]
def baseStart_195510 : Nat := 118140960795 + 195510 * 2 ^ 59
def prefixEnd_195510 : Nat := 4983230072969 + 3 ^ 40 * 195510 * 2
def baseEnd_195510 : Nat := 1652520210051609875323

theorem tailTrace_195510 : CollatzResearch.WordTrace tailWord_195510 prefixEnd_195510 1652520210051609875323 := by
  unfold tailWord_195510
  simp only [CollatzResearch.WordTrace]
  refine ⟨445677220106758455922499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4753890347805423529839989 445677220106758455922499)
  ·
    refine ⟨668515830160137683883749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 445677220106758455922499 668515830160137683883749)
    ·
      refine ⟨125346718155025815728203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 668515830160137683883749 125346718155025815728203)
      ·
        refine ⟨188020077232538723592305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125346718155025815728203 188020077232538723592305)
        ·
          refine ⟨141015057924404042694229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188020077232538723592305 141015057924404042694229)
          ·
            refine ⟨1652520210051609875323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 141015057924404042694229 1652520210051609875323)
            ·
              rfl

theorem cell21_195510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 8].length) (baseStart_195510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195510 prefixEnd_195510 := by exact prefixLift 195510
  have htrace : WordTrace (prefixWord ++ tailWord_195510) baseStart_195510 baseEnd_195510 := by
    simpa [prefixWord, tailWord_195510, baseEnd_195510] using wordTrace_append hprefix tailTrace_195510
  have hstable : (prefixWord ++ tailWord_195510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195510).length < 2 ^ (prefixWord ++ tailWord_195510).sum := by decide
  have hdescent : baseEnd_195510 < baseStart_195510 := by decide
  rcases family_descends (prefixWord ++ tailWord_195510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195535 : List Nat := [1, 1, 2, 1, 1, 8, 1, 6]
def baseStart_195535 : Nat := 118140960795 + 195535 * 2 ^ 59
def prefixEnd_195535 : Nat := 4983230072969 + 3 ^ 40 * 195535 * 2
def baseEnd_195535 : Nat := 14874583670666326239001

theorem tailTrace_195535 : CollatzResearch.WordTrace tailWord_195535 prefixEnd_195535 14874583670666326239001 := by
  unfold tailWord_195535
  simp only [CollatzResearch.WordTrace]
  refine ⟨7131747346617564564420059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4754498231078376376280039 7131747346617564564420059)
  ·
    refine ⟨10697621019926346846630089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7131747346617564564420059 10697621019926346846630089)
    ·
      refine ⟨8023215764944760134972567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10697621019926346846630089 8023215764944760134972567)
      ·
        refine ⟨12034823647417140202458851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8023215764944760134972567 12034823647417140202458851)
        ·
          refine ⟨18052235471125710303688277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12034823647417140202458851 18052235471125710303688277)
          ·
            refine ⟨211549634427254417621347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 18052235471125710303688277 211549634427254417621347)
            ·
              refine ⟨317324451640881626432021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211549634427254417621347 317324451640881626432021)
              ·
                refine ⟨14874583670666326239001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 317324451640881626432021 14874583670666326239001)
                ·
                  rfl

theorem cell21_195535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 6].length) (baseStart_195535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195535 prefixEnd_195535 := by exact prefixLift 195535
  have htrace : WordTrace (prefixWord ++ tailWord_195535) baseStart_195535 baseEnd_195535 := by
    simpa [prefixWord, tailWord_195535, baseEnd_195535] using wordTrace_append hprefix tailTrace_195535
  have hstable : (prefixWord ++ tailWord_195535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195535).length < 2 ^ (prefixWord ++ tailWord_195535).sum := by decide
  have hdescent : baseEnd_195535 < baseStart_195535 := by decide
  rcases family_descends (prefixWord ++ tailWord_195535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195572 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 6]
def baseStart_195572 : Nat := 118140960795 + 195572 * 2 ^ 59
def prefixEnd_195572 : Nat := 4983230072969 + 3 ^ 40 * 195572 * 2
def baseEnd_195572 : Nat := 44632194916095136600261

theorem tailTrace_195572 : CollatzResearch.WordTrace tailWord_195572 prefixEnd_195572 44632194916095136600261 := by
  unfold tailWord_195572
  simp only [CollatzResearch.WordTrace]
  refine ⟨3566548423741759941758485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4755397898322346589011313 3566548423741759941758485)
  ·
    refine ⟨167181957362894997269929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3566548423741759941758485 167181957362894997269929)
    ·
      refine ⟨125386468022171247952447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167181957362894997269929 125386468022171247952447)
      ·
        refine ⟨188079702033256871928671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125386468022171247952447 188079702033256871928671)
        ·
          refine ⟨282119553049885307893007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188079702033256871928671 282119553049885307893007)
          ·
            refine ⟨423179329574827961839511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282119553049885307893007 423179329574827961839511)
            ·
              refine ⟨634768994362241942759267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423179329574827961839511 634768994362241942759267)
              ·
                refine ⟨952153491543362914138901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634768994362241942759267 952153491543362914138901)
                ·
                  refine ⟨44632194916095136600261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 952153491543362914138901 44632194916095136600261)
                  ·
                    rfl

theorem cell21_195572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_195572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195572 prefixEnd_195572 := by exact prefixLift 195572
  have htrace : WordTrace (prefixWord ++ tailWord_195572) baseStart_195572 baseEnd_195572 := by
    simpa [prefixWord, tailWord_195572, baseEnd_195572] using wordTrace_append hprefix tailTrace_195572
  have hstable : (prefixWord ++ tailWord_195572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195572).length < 2 ^ (prefixWord ++ tailWord_195572).sum := by decide
  have hdescent : baseEnd_195572 < baseStart_195572 := by decide
  rcases family_descends (prefixWord ++ tailWord_195572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195580 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 6]
def baseStart_195580 : Nat := 118140960795 + 195580 * 2 ^ 59
def prefixEnd_195580 : Nat := 4983230072969 + 3 ^ 40 * 195580 * 2
def baseEnd_195580 : Nat := 44634020625088900466911

theorem tailTrace_195580 : CollatzResearch.WordTrace tailWord_195580 prefixEnd_195580 44634020625088900466911 := by
  unfold tailWord_195580
  simp only [CollatzResearch.WordTrace]
  refine ⟨3566694315727268624904097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4755592420969691499872129 3566694315727268624904097)
  ·
    refine ⟨2675020736795451468678073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3566694315727268624904097 2675020736795451468678073)
    ·
      refine ⟨2006265552596588601508555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2675020736795451468678073 2006265552596588601508555)
      ·
        refine ⟨3009398328894882902262833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2006265552596588601508555 3009398328894882902262833)
        ·
          refine ⟨2257048746671162176697125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3009398328894882902262833 2257048746671162176697125)
          ·
            refine ⟨423196640000842908130711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2257048746671162176697125 423196640000842908130711)
            ·
              refine ⟨634794960001264362196067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423196640000842908130711 634794960001264362196067)
              ·
                refine ⟨952192440001896543294101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634794960001264362196067 952192440001896543294101)
                ·
                  refine ⟨44634020625088900466911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 952192440001896543294101 44634020625088900466911)
                  ·
                    rfl

theorem cell21_195580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_195580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195580 prefixEnd_195580 := by exact prefixLift 195580
  have htrace : WordTrace (prefixWord ++ tailWord_195580) baseStart_195580 baseEnd_195580 := by
    simpa [prefixWord, tailWord_195580, baseEnd_195580] using wordTrace_append hprefix tailTrace_195580
  have hstable : (prefixWord ++ tailWord_195580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195580).length < 2 ^ (prefixWord ++ tailWord_195580).sum := by decide
  have hdescent : baseEnd_195580 < baseStart_195580 := by decide
  rcases family_descends (prefixWord ++ tailWord_195580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195642 : List Nat := [3, 1, 1, 1, 3, 1, 2, 6, 3]
def baseStart_195642 : Nat := 118140960795 + 195642 * 2 ^ 59
def prefixEnd_195642 : Nat := 4983230072969 + 3 ^ 40 * 195642 * 2
def baseEnd_195642 : Nat := 44648169869790570433451

theorem tailTrace_195642 : CollatzResearch.WordTrace tailWord_195642 prefixEnd_195642 44648169869790570433451 := by
  unfold tailWord_195642
  simp only [CollatzResearch.WordTrace]
  refine ⟨1783912489307480459641295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4757099971486614559043453 1783912489307480459641295)
  ·
    refine ⟨2675868733961220689461943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1783912489307480459641295 2675868733961220689461943)
    ·
      refine ⟨4013803100941831034192915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2675868733961220689461943 4013803100941831034192915)
      ·
        refine ⟨6020704651412746551289373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4013803100941831034192915 6020704651412746551289373)
        ·
          refine ⟨2257764244279779956733515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6020704651412746551289373 2257764244279779956733515)
          ·
            refine ⟨3386646366419669935100273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2257764244279779956733515 3386646366419669935100273)
            ·
              refine ⟨2539984774814752451325205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3386646366419669935100273 2539984774814752451325205)
              ·
                refine ⟨119061786319441521155869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2539984774814752451325205 119061786319441521155869)
                ·
                  refine ⟨44648169869790570433451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119061786319441521155869 44648169869790570433451)
                  ·
                    rfl

theorem cell21_195642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_195642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195642 prefixEnd_195642 := by exact prefixLift 195642
  have htrace : WordTrace (prefixWord ++ tailWord_195642) baseStart_195642 baseEnd_195642 := by
    simpa [prefixWord, tailWord_195642, baseEnd_195642] using wordTrace_append hprefix tailTrace_195642
  have hstable : (prefixWord ++ tailWord_195642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195642).length < 2 ^ (prefixWord ++ tailWord_195642).sum := by decide
  have hdescent : baseEnd_195642 < baseStart_195642 := by decide
  rcases family_descends (prefixWord ++ tailWord_195642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195656 : List Nat := [2, 1, 3, 1, 1, 1, 5, 3, 4]
def baseStart_195656 : Nat := 118140960795 + 195656 * 2 ^ 59
def prefixEnd_195656 : Nat := 4983230072969 + 3 ^ 40 * 195656 * 2
def baseEnd_195656 : Nat := 44651364860529657200089

theorem tailTrace_195656 : CollatzResearch.WordTrace tailWord_195656 prefixEnd_195656 44651364860529657200089 := by
  unfold tailWord_195656
  simp only [CollatzResearch.WordTrace]
  refine ⟨3568080289589601114787411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4757440386119468153049881 3568080289589601114787411)
  ·
    refine ⟨5352120434384401672181117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3568080289589601114787411 5352120434384401672181117)
    ·
      refine ⟨2007045162894150627067919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5352120434384401672181117 2007045162894150627067919)
      ·
        refine ⟨3010567744341225940601879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2007045162894150627067919 3010567744341225940601879)
        ·
          refine ⟨4515851616511838910902819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3010567744341225940601879 4515851616511838910902819)
          ·
            refine ⟨6773777424767758366354229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4515851616511838910902819 6773777424767758366354229)
            ·
              refine ⟨635041633571977346845709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6773777424767758366354229 635041633571977346845709)
              ·
                refine ⟨238140612589491505067141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 635041633571977346845709 238140612589491505067141)
                ·
                  refine ⟨44651364860529657200089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 238140612589491505067141 44651364860529657200089)
                  ·
                    rfl

theorem cell21_195656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_195656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195656 prefixEnd_195656 := by exact prefixLift 195656
  have htrace : WordTrace (prefixWord ++ tailWord_195656) baseStart_195656 baseEnd_195656 := by
    simpa [prefixWord, tailWord_195656, baseEnd_195656] using wordTrace_append hprefix tailTrace_195656
  have hstable : (prefixWord ++ tailWord_195656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195656).length < 2 ^ (prefixWord ++ tailWord_195656).sum := by decide
  have hdescent : baseEnd_195656 < baseStart_195656 := by decide
  rcases family_descends (prefixWord ++ tailWord_195656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195735 : List Nat := [1, 1, 3, 3, 3, 2, 2, 3, 3]
def baseStart_195735 : Nat := 118140960795 + 195735 * 2 ^ 59
def prefixEnd_195735 : Nat := 4983230072969 + 3 ^ 40 * 195735 * 2
def baseEnd_195735 : Nat := 44669393736843075383261

theorem tailTrace_195735 : CollatzResearch.WordTrace tailWord_195735 prefixEnd_195735 44669393736843075383261 := by
  unfold tailWord_195735
  simp only [CollatzResearch.WordTrace]
  refine ⟨7139041945892998721700659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4759361297261999147800439 7139041945892998721700659)
  ·
    refine ⟨10708562918839498082550989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7139041945892998721700659 10708562918839498082550989)
    ·
      refine ⟨4015711094564811780956621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10708562918839498082550989 4015711094564811780956621)
      ·
        refine ⟨1505891660461804417858733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4015711094564811780956621 1505891660461804417858733)
        ·
          refine ⟨564709372673176656697025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1505891660461804417858733 564709372673176656697025)
          ·
            refine ⟨423532029504882492522769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 564709372673176656697025 423532029504882492522769)
            ·
              refine ⟨317649022128661869392077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423532029504882492522769 317649022128661869392077)
              ·
                refine ⟨119118383298248201022029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317649022128661869392077 119118383298248201022029)
                ·
                  refine ⟨44669393736843075383261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119118383298248201022029 44669393736843075383261)
                  ·
                    rfl

theorem cell21_195735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 3].length) (baseStart_195735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195735 prefixEnd_195735 := by exact prefixLift 195735
  have htrace : WordTrace (prefixWord ++ tailWord_195735) baseStart_195735 baseEnd_195735 := by
    simpa [prefixWord, tailWord_195735, baseEnd_195735] using wordTrace_append hprefix tailTrace_195735
  have hstable : (prefixWord ++ tailWord_195735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195735).length < 2 ^ (prefixWord ++ tailWord_195735).sum := by decide
  have hdescent : baseEnd_195735 < baseStart_195735 := by decide
  rcases family_descends (prefixWord ++ tailWord_195735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195749 : List Nat := [1, 3, 1, 2, 1, 6, 1, 2, 4]
def baseStart_195749 : Nat := 118140960795 + 195749 * 2 ^ 59
def prefixEnd_195749 : Nat := 4983230072969 + 3 ^ 40 * 195749 * 2
def baseEnd_195749 : Nat := 44672588727582162149899

theorem tailTrace_195749 : CollatzResearch.WordTrace tailWord_195749 prefixEnd_195749 44672588727582162149899 := by
  unfold tailWord_195749
  simp only [CollatzResearch.WordTrace]
  refine ⟨7139552567842279112710301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4759701711894852741806867 7139552567842279112710301)
  ·
    refine ⟨2677332212940854667266363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7139552567842279112710301 2677332212940854667266363)
    ·
      refine ⟨4015998319411282000899545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2677332212940854667266363 4015998319411282000899545)
      ·
        refine ⟨3011998739558461500674659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4015998319411282000899545 3011998739558461500674659)
        ·
          refine ⟨4517998109337692251011989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3011998739558461500674659 4517998109337692251011989)
          ·
            refine ⟨211781161375204324266187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4517998109337692251011989 211781161375204324266187)
            ·
              refine ⟨317671742062806486399281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211781161375204324266187 317671742062806486399281)
              ·
                refine ⟨238253806547104864799461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317671742062806486399281 238253806547104864799461)
                ·
                  refine ⟨44672588727582162149899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 238253806547104864799461 44672588727582162149899)
                  ·
                    rfl

theorem cell21_195749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_195749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195749 prefixEnd_195749 := by exact prefixLift 195749
  have htrace : WordTrace (prefixWord ++ tailWord_195749) baseStart_195749 baseEnd_195749 := by
    simpa [prefixWord, tailWord_195749, baseEnd_195749] using wordTrace_append hprefix tailTrace_195749
  have hstable : (prefixWord ++ tailWord_195749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195749).length < 2 ^ (prefixWord ++ tailWord_195749).sum := by decide
  have hdescent : baseEnd_195749 < baseStart_195749 := by decide
  rcases family_descends (prefixWord ++ tailWord_195749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195760 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 9]
def baseStart_195760 : Nat := 118140960795 + 195760 * 2 ^ 59
def prefixEnd_195760 : Nat := 4983230072969 + 3 ^ 40 * 195760 * 2
def baseEnd_195760 : Nat := 44675099077448587466543

theorem tailTrace_195760 : CollatzResearch.WordTrace tailWord_195760 prefixEnd_195760 44675099077448587466543 := by
  unfold tailWord_195760
  simp only [CollatzResearch.WordTrace]
  refine ⟨3569976885401213995680367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4759969180534951994240489 3569976885401213995680367)
  ·
    refine ⟨5354965328101820993520551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3569976885401213995680367 5354965328101820993520551)
    ·
      refine ⟨8032447992152731490280827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5354965328101820993520551 8032447992152731490280827)
      ·
        refine ⟨12048671988229097235421241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8032447992152731490280827 12048671988229097235421241)
        ·
          refine ⟨9036503991171822926565931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12048671988229097235421241 9036503991171822926565931)
          ·
            refine ⟨13554755986757734389848897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9036503991171822926565931 13554755986757734389848897)
            ·
              refine ⟨10166066990068300792386673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13554755986757734389848897 10166066990068300792386673)
              ·
                refine ⟨7624550242551225594290005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10166066990068300792386673 7624550242551225594290005)
                ·
                  refine ⟨44675099077448587466543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7624550242551225594290005 44675099077448587466543)
                  ·
                    rfl

theorem cell21_195760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_195760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195760 prefixEnd_195760 := by exact prefixLift 195760
  have htrace : WordTrace (prefixWord ++ tailWord_195760) baseStart_195760 baseEnd_195760 := by
    simpa [prefixWord, tailWord_195760, baseEnd_195760] using wordTrace_append hprefix tailTrace_195760
  have hstable : (prefixWord ++ tailWord_195760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195760).length < 2 ^ (prefixWord ++ tailWord_195760).sum := by decide
  have hdescent : baseEnd_195760 < baseStart_195760 := by decide
  rcases family_descends (prefixWord ++ tailWord_195760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195822 : List Nat := [4, 1, 2, 1, 1, 1, 3, 8]
def baseStart_195822 : Nat := 118140960795 + 195822 * 2 ^ 59
def prefixEnd_195822 : Nat := 4983230072969 + 3 ^ 40 * 195822 * 2
def baseEnd_195822 : Nat := 14896416107383419144361

theorem tailTrace_195822 : CollatzResearch.WordTrace tailWord_195822 prefixEnd_195822 14896416107383419144361 := by
  unfold tailWord_195822
  simp only [CollatzResearch.WordTrace]
  refine ⟨892776887072226572514715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4761476731051875053411813 892776887072226572514715)
  ·
    refine ⟨1339165330608339858772073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 892776887072226572514715 1339165330608339858772073)
    ·
      refine ⟨1004373997956254894079055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1339165330608339858772073 1004373997956254894079055)
      ·
        refine ⟨1506560996934382341118583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004373997956254894079055 1506560996934382341118583)
        ·
          refine ⟨2259841495401573511677875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1506560996934382341118583 2259841495401573511677875)
          ·
            refine ⟨3389762243102360267516813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259841495401573511677875 3389762243102360267516813)
            ·
              refine ⟨1271160841163385100318805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3389762243102360267516813 1271160841163385100318805)
              ·
                refine ⟨14896416107383419144361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1271160841163385100318805 14896416107383419144361)
                ·
                  rfl

theorem cell21_195822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_195822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195822 prefixEnd_195822 := by exact prefixLift 195822
  have htrace : WordTrace (prefixWord ++ tailWord_195822) baseStart_195822 baseEnd_195822 := by
    simpa [prefixWord, tailWord_195822, baseEnd_195822] using wordTrace_append hprefix tailTrace_195822
  have hstable : (prefixWord ++ tailWord_195822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195822).length < 2 ^ (prefixWord ++ tailWord_195822).sum := by decide
  have hdescent : baseEnd_195822 < baseStart_195822 := by decide
  rcases family_descends (prefixWord ++ tailWord_195822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195912 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 9]
def baseStart_195912 : Nat := 118140960795 + 195912 * 2 ^ 59
def prefixEnd_195912 : Nat := 4983230072969 + 3 ^ 40 * 195912 * 2
def baseEnd_195912 : Nat := 44709787548330100932899

theorem tailTrace_195912 : CollatzResearch.WordTrace tailWord_195912 prefixEnd_195912 44709787548330100932899 := by
  unfold tailWord_195912
  simp only [CollatzResearch.WordTrace]
  refine ⟨3572748833125878975446995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4763665110834505300595993 3572748833125878975446995)
  ·
    refine ⟨5359123249688818463170493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3572748833125878975446995 5359123249688818463170493)
    ·
      refine ⟨2009671218633306923688935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5359123249688818463170493 2009671218633306923688935)
      ·
        refine ⟨3014506827949960385533403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009671218633306923688935 3014506827949960385533403)
        ·
          refine ⟨4521760241924940578300105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3014506827949960385533403 4521760241924940578300105)
          ·
            refine ⟨3391320181443705433725079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4521760241924940578300105 3391320181443705433725079)
            ·
              refine ⟨5086980272165558150587619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3391320181443705433725079 5086980272165558150587619)
              ·
                refine ⟨7630470408248337225881429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5086980272165558150587619 7630470408248337225881429)
                ·
                  refine ⟨44709787548330100932899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7630470408248337225881429 44709787548330100932899)
                  ·
                    rfl

theorem cell21_195912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_195912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_195912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_195912 prefixEnd_195912 := by exact prefixLift 195912
  have htrace : WordTrace (prefixWord ++ tailWord_195912) baseStart_195912 baseEnd_195912 := by
    simpa [prefixWord, tailWord_195912, baseEnd_195912] using wordTrace_append hprefix tailTrace_195912
  have hstable : (prefixWord ++ tailWord_195912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195912).length < 2 ^ (prefixWord ++ tailWord_195912).sum := by decide
  have hdescent : baseEnd_195912 < baseStart_195912 := by decide
  rcases family_descends (prefixWord ++ tailWord_195912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196067 : List Nat := [1, 1, 1, 6, 2, 2, 3, 5]
def baseStart_196067 : Nat := 118140960795 + 196067 * 2 ^ 59
def prefixEnd_196067 : Nat := 4983230072969 + 3 ^ 40 * 196067 * 2
def baseEnd_196067 : Nat := 14915053553361425283083

theorem tailTrace_196067 : CollatzResearch.WordTrace tailWord_196067 prefixEnd_196067 14915053553361425283083 := by
  unfold tailWord_196067
  simp only [CollatzResearch.WordTrace]
  refine ⟨7151150980690219422786455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4767433987126812948524303 7151150980690219422786455)
  ·
    refine ⟨10726726471035329134179683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7151150980690219422786455 10726726471035329134179683)
    ·
      refine ⟨16090089706552993701269525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10726726471035329134179683 16090089706552993701269525)
      ·
        refine ⟨754222954994671579747009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16090089706552993701269525 754222954994671579747009)
        ·
          refine ⟨565667216246003684810257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 754222954994671579747009 565667216246003684810257)
          ·
            refine ⟨424250412184502763607693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 565667216246003684810257 424250412184502763607693)
            ·
              refine ⟨159093904569188536352885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 424250412184502763607693 159093904569188536352885)
              ·
                refine ⟨14915053553361425283083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159093904569188536352885 14915053553361425283083)
                ·
                  rfl

theorem cell21_196067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 5].length) (baseStart_196067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_196067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_196067 prefixEnd_196067 := by exact prefixLift 196067
  have htrace : WordTrace (prefixWord ++ tailWord_196067) baseStart_196067 baseEnd_196067 := by
    simpa [prefixWord, tailWord_196067, baseEnd_196067] using wordTrace_append hprefix tailTrace_196067
  have hstable : (prefixWord ++ tailWord_196067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196067).length < 2 ^ (prefixWord ++ tailWord_196067).sum := by decide
  have hdescent : baseEnd_196067 < baseStart_196067 := by decide
  rcases family_descends (prefixWord ++ tailWord_196067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196095 : List Nat := [1, 1, 2, 2, 1, 2, 2, 6, 4]
def baseStart_196095 : Nat := 118140960795 + 196095 * 2 ^ 59
def prefixEnd_196095 : Nat := 4983230072969 + 3 ^ 40 * 196095 * 2
def baseEnd_196095 : Nat := 44751550641562449382525

theorem tailTrace_196095 : CollatzResearch.WordTrace tailWord_196095 prefixEnd_196095 44751550641562449382525 := by
  unfold tailWord_196095
  simp only [CollatzResearch.WordTrace]
  refine ⟨7152172224588780204805739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4768114816392520136537159 7152172224588780204805739)
  ·
    refine ⟨10728258336883170307208609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7152172224588780204805739 10728258336883170307208609)
    ·
      refine ⟨8046193752662377730406457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10728258336883170307208609 8046193752662377730406457)
      ·
        refine ⟨6034645314496783297804843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8046193752662377730406457 6034645314496783297804843)
        ·
          refine ⟨9051967971745174946707265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6034645314496783297804843 9051967971745174946707265)
          ·
            refine ⟨6788975978808881210030449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9051967971745174946707265 6788975978808881210030449)
            ·
              refine ⟨5091731984106660907522837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6788975978808881210030449 5091731984106660907522837)
              ·
                refine ⟨238674936754999730040133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5091731984106660907522837 238674936754999730040133)
                ·
                  refine ⟨44751550641562449382525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 238674936754999730040133 44751550641562449382525)
                  ·
                    rfl

theorem cell21_196095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 4].length) (baseStart_196095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_196095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_196095 prefixEnd_196095 := by exact prefixLift 196095
  have htrace : WordTrace (prefixWord ++ tailWord_196095) baseStart_196095 baseEnd_196095 := by
    simpa [prefixWord, tailWord_196095, baseEnd_196095] using wordTrace_append hprefix tailTrace_196095
  have hstable : (prefixWord ++ tailWord_196095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196095).length < 2 ^ (prefixWord ++ tailWord_196095).sum := by decide
  have hdescent : baseEnd_196095 < baseStart_196095 := by decide
  rcases family_descends (prefixWord ++ tailWord_196095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196098 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 5]
def baseStart_196098 : Nat := 118140960795 + 196098 * 2 ^ 59
def prefixEnd_196098 : Nat := 4983230072969 + 3 ^ 40 * 196098 * 2
def baseEnd_196098 : Nat := 44752235282435110832519

theorem tailTrace_196098 : CollatzResearch.WordTrace tailWord_196098 prefixEnd_196098 44752235282435110832519 := by
  unfold tailWord_196098
  simp only [CollatzResearch.WordTrace]
  refine ⟨1788070410894477929291237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4768187762385274478109965 1788070410894477929291237)
  ·
    refine ⟨335263202042714611742107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1788070410894477929291237 335263202042714611742107)
    ·
      refine ⟨502894803064071917613161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335263202042714611742107 502894803064071917613161)
      ·
        refine ⟨377171102298053938209871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502894803064071917613161 377171102298053938209871)
        ·
          refine ⟨565756653447080907314807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377171102298053938209871 565756653447080907314807)
          ·
            refine ⟨848634980170621360972211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565756653447080907314807 848634980170621360972211)
            ·
              refine ⟨1272952470255932041458317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848634980170621360972211 1272952470255932041458317)
              ·
                refine ⟨477357176345974515546869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1272952470255932041458317 477357176345974515546869)
                ·
                  refine ⟨44752235282435110832519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 477357176345974515546869 44752235282435110832519)
                  ·
                    rfl

theorem cell21_196098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_196098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_196098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_196098 prefixEnd_196098 := by exact prefixLift 196098
  have htrace : WordTrace (prefixWord ++ tailWord_196098) baseStart_196098 baseEnd_196098 := by
    simpa [prefixWord, tailWord_196098, baseEnd_196098] using wordTrace_append hprefix tailTrace_196098
  have hstable : (prefixWord ++ tailWord_196098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196098).length < 2 ^ (prefixWord ++ tailWord_196098).sum := by decide
  have hdescent : baseEnd_196098 < baseStart_196098 := by decide
  rcases family_descends (prefixWord ++ tailWord_196098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196205 : List Nat := [1, 5, 1, 1, 4, 1, 2, 2, 4]
def baseStart_196205 : Nat := 118140960795 + 196205 * 2 ^ 59
def prefixEnd_196205 : Nat := 4983230072969 + 3 ^ 40 * 196205 * 2
def baseEnd_196205 : Nat := 44776654140226702548967

theorem tailTrace_196205 : CollatzResearch.WordTrace tailWord_196205 prefixEnd_196205 44776654140226702548967 := by
  unfold tailWord_196205
  simp only [CollatzResearch.WordTrace]
  refine ⟨7156184254190268991310069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4770789502793512660873379 7156184254190268991310069)
  ·
    refine ⟨670892273830337717935319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7156184254190268991310069 670892273830337717935319)
    ·
      refine ⟨1006338410745506576902979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 670892273830337717935319 1006338410745506576902979)
      ·
        refine ⟨1509507616118259865354469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1006338410745506576902979 1509507616118259865354469)
        ·
          refine ⟨283032678022173724753963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1509507616118259865354469 283032678022173724753963)
          ·
            refine ⟨424549017033260587130945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283032678022173724753963 424549017033260587130945)
            ·
              refine ⟨318411762774945440348209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424549017033260587130945 318411762774945440348209)
              ·
                refine ⟨238808822081209080261157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318411762774945440348209 238808822081209080261157)
                ·
                  refine ⟨44776654140226702548967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 238808822081209080261157 44776654140226702548967)
                  ·
                    rfl

theorem cell21_196205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_196205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_196205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_196205 prefixEnd_196205 := by exact prefixLift 196205
  have htrace : WordTrace (prefixWord ++ tailWord_196205) baseStart_196205 baseEnd_196205 := by
    simpa [prefixWord, tailWord_196205, baseEnd_196205] using wordTrace_append hprefix tailTrace_196205
  have hstable : (prefixWord ++ tailWord_196205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196205).length < 2 ^ (prefixWord ++ tailWord_196205).sum := by decide
  have hdescent : baseEnd_196205 < baseStart_196205 := by decide
  rcases family_descends (prefixWord ++ tailWord_196205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196337 : List Nat := [1, 2, 2, 2, 2, 3, 1, 8]
def baseStart_196337 : Nat := 118140960795 + 196337 * 2 ^ 59
def prefixEnd_196337 : Nat := 4983230072969 + 3 ^ 40 * 196337 * 2
def baseEnd_196337 : Nat := 14935592779541268782899

theorem tailTrace_196337 : CollatzResearch.WordTrace tailWord_196337 prefixEnd_196337 14935592779541268782899 := by
  unfold tailWord_196337
  simp only [CollatzResearch.WordTrace]
  refine ⟨7160998689712055535115265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4773999126474703690076843 7160998689712055535115265)
  ·
    refine ⟨5370749017284041651336449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7160998689712055535115265 5370749017284041651336449)
    ·
      refine ⟨4028061762963031238502337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5370749017284041651336449 4028061762963031238502337)
      ·
        refine ⟨3021046322222273428876753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4028061762963031238502337 3021046322222273428876753)
        ·
          refine ⟨2265784741666705071657565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3021046322222273428876753 2265784741666705071657565)
          ·
            refine ⟨849669278125014401871587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2265784741666705071657565 849669278125014401871587)
            ·
              refine ⟨1274503917187521602807381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849669278125014401871587 1274503917187521602807381)
              ·
                refine ⟨14935592779541268782899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1274503917187521602807381 14935592779541268782899)
                ·
                  rfl

theorem cell21_196337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 8].length) (baseStart_196337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_196337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_196337 prefixEnd_196337 := by exact prefixLift 196337
  have htrace : WordTrace (prefixWord ++ tailWord_196337) baseStart_196337 baseEnd_196337 := by
    simpa [prefixWord, tailWord_196337, baseEnd_196337] using wordTrace_append hprefix tailTrace_196337
  have hstable : (prefixWord ++ tailWord_196337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196337).length < 2 ^ (prefixWord ++ tailWord_196337).sum := by decide
  have hdescent : baseEnd_196337 < baseStart_196337 := by decide
  rcases family_descends (prefixWord ++ tailWord_196337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196354 : List Nat := [3, 4, 1, 1, 1, 1, 1, 9]
def baseStart_196354 : Nat := 118140960795 + 196354 * 2 ^ 59
def prefixEnd_196354 : Nat := 4983230072969 + 3 ^ 40 * 196354 * 2
def baseEnd_196354 : Nat := 14936885990078518188443

theorem tailTrace_196354 : CollatzResearch.WordTrace tailWord_196354 prefixEnd_196354 14936885990078518188443 := by
  unfold tailWord_196354
  simp only [CollatzResearch.WordTrace]
  refine ⟨1790404682662616859621029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4774412487100311625656077 1790404682662616859621029)
  ·
    refine ⟨335700877999240661178943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1790404682662616859621029 335700877999240661178943)
    ·
      refine ⟨503551316998860991768415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335700877999240661178943 503551316998860991768415)
      ·
        refine ⟨755326975498291487652623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503551316998860991768415 755326975498291487652623)
        ·
          refine ⟨1132990463247437231478935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 755326975498291487652623 1132990463247437231478935)
          ·
            refine ⟨1699485694871155847218403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1132990463247437231478935 1699485694871155847218403)
            ·
              refine ⟨2549228542306733770827605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699485694871155847218403 2549228542306733770827605)
              ·
                refine ⟨14936885990078518188443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2549228542306733770827605 14936885990078518188443)
                ·
                  rfl

theorem cell21_196354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_196354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_196354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_196354 prefixEnd_196354 := by exact prefixLift 196354
  have htrace : WordTrace (prefixWord ++ tailWord_196354) baseStart_196354 baseEnd_196354 := by
    simpa [prefixWord, tailWord_196354, baseEnd_196354] using wordTrace_append hprefix tailTrace_196354
  have hstable : (prefixWord ++ tailWord_196354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196354).length < 2 ^ (prefixWord ++ tailWord_196354).sum := by decide
  have hdescent : baseEnd_196354 < baseStart_196354 := by decide
  rcases family_descends (prefixWord ++ tailWord_196354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196506 : List Nat := [3, 1, 1, 4, 2, 2, 2, 6]
def baseStart_196506 : Nat := 118140960795 + 196506 * 2 ^ 59
def prefixEnd_196506 : Nat := 4983230072969 + 3 ^ 40 * 196506 * 2
def baseEnd_196506 : Nat := 14948448813705689343895

theorem tailTrace_196506 : CollatzResearch.WordTrace tailWord_196506 prefixEnd_196506 14948448813705689343895 := by
  unfold tailWord_196506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1791790656524949349504343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4778108417399864932011581 1791790656524949349504343)
  ·
    refine ⟨2687685984787424024256515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1791790656524949349504343 2687685984787424024256515)
    ·
      refine ⟨4031528977181136036384773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2687685984787424024256515 4031528977181136036384773)
      ·
        refine ⟨755911683221463006822145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4031528977181136036384773 755911683221463006822145)
        ·
          refine ⟨566933762416097255116609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755911683221463006822145 566933762416097255116609)
          ·
            refine ⟨425200321812072941337457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 566933762416097255116609 425200321812072941337457)
            ·
              refine ⟨318900241359054706003093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425200321812072941337457 318900241359054706003093)
              ·
                refine ⟨14948448813705689343895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 318900241359054706003093 14948448813705689343895)
                ·
                  rfl

theorem cell21_196506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_196506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_196506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_196506 prefixEnd_196506 := by exact prefixLift 196506
  have htrace : WordTrace (prefixWord ++ tailWord_196506) baseStart_196506 baseEnd_196506 := by
    simpa [prefixWord, tailWord_196506, baseEnd_196506] using wordTrace_append hprefix tailTrace_196506
  have hstable : (prefixWord ++ tailWord_196506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196506).length < 2 ^ (prefixWord ++ tailWord_196506).sum := by decide
  have hdescent : baseEnd_196506 < baseStart_196506 := by decide
  rcases family_descends (prefixWord ++ tailWord_196506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196509 : List Nat := [1, 4, 2, 1, 2, 4, 2, 1, 4]
def baseStart_196509 : Nat := 118140960795 + 196509 * 2 ^ 59
def prefixEnd_196509 : Nat := 4983230072969 + 3 ^ 40 * 196509 * 2
def baseEnd_196509 : Nat := 44846031081989729481679

theorem tailTrace_196509 : CollatzResearch.WordTrace tailWord_196509 prefixEnd_196509 44846031081989729481679 := by
  unfold tailWord_196509
  simp only [CollatzResearch.WordTrace]
  refine ⟨7167272045088928910376581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4778181363392619273584387 7167272045088928910376581)
  ·
    refine ⟨1343863508454174170695609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7167272045088928910376581 1343863508454174170695609)
    ·
      refine ⟨1007897631340630628021707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1343863508454174170695609 1007897631340630628021707)
      ·
        refine ⟨1511846447010945942032561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1007897631340630628021707 1511846447010945942032561)
        ·
          refine ⟨1133884835258209456524421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1511846447010945942032561 1133884835258209456524421)
          ·
            refine ⟨212603406610914273098329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1133884835258209456524421 212603406610914273098329)
            ·
              refine ⟨159452554958185704823747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212603406610914273098329 159452554958185704823747)
              ·
                refine ⟨239178832437278557235621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159452554958185704823747 239178832437278557235621)
                ·
                  refine ⟨44846031081989729481679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 239178832437278557235621 44846031081989729481679)
                  ·
                    rfl

theorem cell21_196509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_196509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_196509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_196509 prefixEnd_196509 := by exact prefixLift 196509
  have htrace : WordTrace (prefixWord ++ tailWord_196509) baseStart_196509 baseEnd_196509 := by
    simpa [prefixWord, tailWord_196509, baseEnd_196509] using wordTrace_append hprefix tailTrace_196509
  have hstable : (prefixWord ++ tailWord_196509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196509).length < 2 ^ (prefixWord ++ tailWord_196509).sum := by decide
  have hdescent : baseEnd_196509 < baseStart_196509 := by decide
  rcases family_descends (prefixWord ++ tailWord_196509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196537 : List Nat := [1, 2, 1, 4, 2, 1, 2, 5, 3]
def baseStart_196537 : Nat := 118140960795 + 196537 * 2 ^ 59
def prefixEnd_196537 : Nat := 4983230072969 + 3 ^ 40 * 196537 * 2
def baseEnd_196537 : Nat := 44852421063467903014955

theorem tailTrace_196537 : CollatzResearch.WordTrace tailWord_196537 prefixEnd_196537 44852421063467903014955 := by
  unfold tailWord_196537
  simp only [CollatzResearch.WordTrace]
  refine ⟨7168293288987489692395865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4778862192658326461597243 7168293288987489692395865)
  ·
    refine ⟨5376219966740617269296899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7168293288987489692395865 5376219966740617269296899)
    ·
      refine ⟨8064329950110925903945349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5376219966740617269296899 8064329950110925903945349)
      ·
        refine ⟨1512061865645798606989753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8064329950110925903945349 1512061865645798606989753)
        ·
          refine ⟨1134046399234348955242315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1512061865645798606989753 1134046399234348955242315)
          ·
            refine ⟨1701069598851523432863473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134046399234348955242315 1701069598851523432863473)
            ·
              refine ⟨1275802199138642574647605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1701069598851523432863473 1275802199138642574647605)
              ·
                refine ⟨119606456169247741373213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1275802199138642574647605 119606456169247741373213)
                ·
                  refine ⟨44852421063467903014955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119606456169247741373213 44852421063467903014955)
                  ·
                    rfl

theorem cell21_196537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 3].length) (baseStart_196537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_196537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_196537 prefixEnd_196537 := by exact prefixLift 196537
  have htrace : WordTrace (prefixWord ++ tailWord_196537) baseStart_196537 baseEnd_196537 := by
    simpa [prefixWord, tailWord_196537, baseEnd_196537] using wordTrace_append hprefix tailTrace_196537
  have hstable : (prefixWord ++ tailWord_196537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196537).length < 2 ^ (prefixWord ++ tailWord_196537).sum := by decide
  have hdescent : baseEnd_196537 < baseStart_196537 := by decide
  rcases family_descends (prefixWord ++ tailWord_196537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196554 : List Nat := [3, 1, 2, 1, 2, 1, 6, 2, 3]
def baseStart_196554 : Nat := 118140960795 + 196554 * 2 ^ 59
def prefixEnd_196554 : Nat := 4983230072969 + 3 ^ 40 * 196554 * 2
def baseEnd_196554 : Nat := 44856300695079651231587

theorem tailTrace_196554 : CollatzResearch.WordTrace tailWord_196554 prefixEnd_196554 44856300695079651231587 := by
  unfold tailWord_196554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1792228332481475398941179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4779275553283934397176477 1792228332481475398941179)
  ·
    refine ⟨2688342498722213098411769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1792228332481475398941179 2688342498722213098411769)
    ·
      refine ⟨2016256874041659823808827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2688342498722213098411769 2016256874041659823808827)
      ·
        refine ⟨3024385311062489735713241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2016256874041659823808827 3024385311062489735713241)
        ·
          refine ⟨2268288983296867301784931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3024385311062489735713241 2268288983296867301784931)
          ·
            refine ⟨3402433474945300952677397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2268288983296867301784931 3402433474945300952677397)
            ·
              refine ⟨159489069138060982156753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3402433474945300952677397 159489069138060982156753)
              ·
                refine ⟨119616801853545736617565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159489069138060982156753 119616801853545736617565)
                ·
                  refine ⟨44856300695079651231587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119616801853545736617565 44856300695079651231587)
                  ·
                    rfl

theorem cell21_196554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_196554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_196554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_196554 prefixEnd_196554 := by exact prefixLift 196554
  have htrace : WordTrace (prefixWord ++ tailWord_196554) baseStart_196554 baseEnd_196554 := by
    simpa [prefixWord, tailWord_196554, baseEnd_196554] using wordTrace_append hprefix tailTrace_196554
  have hstable : (prefixWord ++ tailWord_196554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196554).length < 2 ^ (prefixWord ++ tailWord_196554).sum := by decide
  have hdescent : baseEnd_196554 < baseStart_196554 := by decide
  rcases family_descends (prefixWord ++ tailWord_196554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196613 : List Nat := [1, 3, 1, 1, 2, 4, 2, 4, 3]
def baseStart_196613 : Nat := 118140960795 + 196613 * 2 ^ 59
def prefixEnd_196613 : Nat := 4983230072969 + 3 ^ 40 * 196613 * 2
def baseEnd_196613 : Nat := 44869765298908659748133

theorem tailTrace_196613 : CollatzResearch.WordTrace tailWord_196613 prefixEnd_196613 44869765298908659748133 := by
  unfold tailWord_196613
  simp only [CollatzResearch.WordTrace]
  refine ⟨7171065236712154672162493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4780710157808103114774995 7171065236712154672162493)
  ·
    refine ⟨2689149463767058002060935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7171065236712154672162493 2689149463767058002060935)
    ·
      refine ⟨4033724195650587003091403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2689149463767058002060935 4033724195650587003091403)
      ·
        refine ⟨6050586293475880504637105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033724195650587003091403 6050586293475880504637105)
        ·
          refine ⟨4537939720106910378477829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6050586293475880504637105 4537939720106910378477829)
          ·
            refine ⟨850863697520045695964593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4537939720106910378477829 850863697520045695964593)
            ·
              refine ⟨638147773140034271973445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850863697520045695964593 638147773140034271973445)
              ·
                refine ⟨119652707463756425995021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 638147773140034271973445 119652707463756425995021)
                ·
                  refine ⟨44869765298908659748133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119652707463756425995021 44869765298908659748133)
                  ·
                    rfl

theorem cell21_196613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_196613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_196613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_196613 prefixEnd_196613 := by exact prefixLift 196613
  have htrace : WordTrace (prefixWord ++ tailWord_196613) baseStart_196613 baseEnd_196613 := by
    simpa [prefixWord, tailWord_196613, baseEnd_196613] using wordTrace_append hprefix tailTrace_196613
  have hstable : (prefixWord ++ tailWord_196613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196613).length < 2 ^ (prefixWord ++ tailWord_196613).sum := by decide
  have hdescent : baseEnd_196613 < baseStart_196613 := by decide
  rcases family_descends (prefixWord ++ tailWord_196613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196672 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 5]
def baseStart_196672 : Nat := 118140960795 + 196672 * 2 ^ 59
def prefixEnd_196672 : Nat := 4983230072969 + 3 ^ 40 * 196672 * 2
def baseEnd_196672 : Nat := 44883229902737668264679

theorem tailTrace_196672 : CollatzResearch.WordTrace tailWord_196672 prefixEnd_196672 44883229902737668264679 := by
  unfold tailWord_196672
  simp only [CollatzResearch.WordTrace]
  refine ⟨3586608571749203874280135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4782144762332271832373513 3586608571749203874280135)
  ·
    refine ⟨5379912857623805811420203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3586608571749203874280135 5379912857623805811420203)
    ·
      refine ⟨8069869286435708717130305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5379912857623805811420203 8069869286435708717130305)
      ·
        refine ⟨6052401964826781537847729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8069869286435708717130305 6052401964826781537847729)
        ·
          refine ⟨4539301473620086153385797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6052401964826781537847729 4539301473620086153385797)
          ·
            refine ⟨851119026303766153759837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4539301473620086153385797 851119026303766153759837)
            ·
              refine ⟨319169634863912307659939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 851119026303766153759837 319169634863912307659939)
              ·
                refine ⟨478754452295868461489909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319169634863912307659939 478754452295868461489909)
                ·
                  refine ⟨44883229902737668264679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 478754452295868461489909 44883229902737668264679)
                  ·
                    rfl

theorem cell21_196672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_196672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_196672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_196672 prefixEnd_196672 := by exact prefixLift 196672
  have htrace : WordTrace (prefixWord ++ tailWord_196672) baseStart_196672 baseEnd_196672 := by
    simpa [prefixWord, tailWord_196672, baseEnd_196672] using wordTrace_append hprefix tailTrace_196672
  have hstable : (prefixWord ++ tailWord_196672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196672).length < 2 ^ (prefixWord ++ tailWord_196672).sum := by decide
  have hdescent : baseEnd_196672 < baseStart_196672 := by decide
  rcases family_descends (prefixWord ++ tailWord_196672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196765 : List Nat := [1, 4, 2, 1, 1, 3, 1, 5, 3]
def baseStart_196765 : Nat := 118140960795 + 196765 * 2 ^ 59
def prefixEnd_196765 : Nat := 4983230072969 + 3 ^ 40 * 196765 * 2
def baseEnd_196765 : Nat := 44904453769790173214489

theorem tailTrace_196765 : CollatzResearch.WordTrace tailWord_196765 prefixEnd_196765 44904453769790173214489 := by
  unfold tailWord_196765
  simp only [CollatzResearch.WordTrace]
  refine ⟨7176609132161484631695749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4784406088107656421130499 7176609132161484631695749)
  ·
    refine ⟨1345614212280278368442953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7176609132161484631695749 1345614212280278368442953)
    ·
      refine ⟨1009210659210208776332215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1345614212280278368442953 1009210659210208776332215)
      ·
        refine ⟨1513815988815313164498323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009210659210208776332215 1513815988815313164498323)
        ·
          refine ⟨2270723983222969746747485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1513815988815313164498323 2270723983222969746747485)
          ·
            refine ⟨851521493708613655030307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2270723983222969746747485 851521493708613655030307)
            ·
              refine ⟨1277282240562920482545461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851521493708613655030307 1277282240562920482545461)
              ·
                refine ⟨119745210052773795238637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1277282240562920482545461 119745210052773795238637)
                ·
                  refine ⟨44904453769790173214489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119745210052773795238637 44904453769790173214489)
                  ·
                    rfl

theorem cell21_196765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_196765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_196765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_196765 prefixEnd_196765 := by exact prefixLift 196765
  have htrace : WordTrace (prefixWord ++ tailWord_196765) baseStart_196765 baseEnd_196765 := by
    simpa [prefixWord, tailWord_196765, baseEnd_196765] using wordTrace_append hprefix tailTrace_196765
  have hstable : (prefixWord ++ tailWord_196765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196765).length < 2 ^ (prefixWord ++ tailWord_196765).sum := by decide
  have hdescent : baseEnd_196765 < baseStart_196765 := by decide
  rcases family_descends (prefixWord ++ tailWord_196765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196948 : List Nat := [2, 4, 1, 1, 2, 4, 1, 2, 4]
def baseStart_196948 : Nat := 118140960795 + 196948 * 2 ^ 59
def prefixEnd_196948 : Nat := 4983230072969 + 3 ^ 40 * 196948 * 2
def baseEnd_196948 : Nat := 44946216863022521664115

theorem tailTrace_196948 : CollatzResearch.WordTrace tailWord_196948 prefixEnd_196948 44946216863022521664115 := by
  unfold tailWord_196948
  simp only [CollatzResearch.WordTrace]
  refine ⟨3591641845249253442803749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4788855793665671257071665 3591641845249253442803749)
  ·
    refine ⟨673432845984235020525703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3591641845249253442803749 673432845984235020525703)
    ·
      refine ⟨1010149268976352530788555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 673432845984235020525703 1010149268976352530788555)
      ·
        refine ⟨1515223903464528796182833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1010149268976352530788555 1515223903464528796182833)
        ·
          refine ⟨1136417927598396597137125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1515223903464528796182833 1136417927598396597137125)
          ·
            refine ⟨213078361424699361963211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1136417927598396597137125 213078361424699361963211)
            ·
              refine ⟨319617542137049042944817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213078361424699361963211 319617542137049042944817)
              ·
                refine ⟨239713156602786782208613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319617542137049042944817 239713156602786782208613)
                ·
                  refine ⟨44946216863022521664115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 239713156602786782208613 44946216863022521664115)
                  ·
                    rfl

theorem cell21_196948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_196948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_196948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_196948 prefixEnd_196948 := by exact prefixLift 196948
  have htrace : WordTrace (prefixWord ++ tailWord_196948) baseStart_196948 baseEnd_196948 := by
    simpa [prefixWord, tailWord_196948, baseEnd_196948] using wordTrace_append hprefix tailTrace_196948
  have hstable : (prefixWord ++ tailWord_196948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196948).length < 2 ^ (prefixWord ++ tailWord_196948).sum := by decide
  have hdescent : baseEnd_196948 < baseStart_196948 := by decide
  rcases family_descends (prefixWord ++ tailWord_196948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196959 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 5]
def baseStart_196959 : Nat := 118140960795 + 196959 * 2 ^ 59
def prefixEnd_196959 : Nat := 4983230072969 + 3 ^ 40 * 196959 * 2
def baseEnd_196959 : Nat := 44948727212888946980759

theorem tailTrace_196959 : CollatzResearch.WordTrace tailWord_196959 prefixEnd_196959 44948727212888946980759 := by
  unfold tailWord_196959
  simp only [CollatzResearch.WordTrace]
  refine ⟨7183684893458655764257931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4789123262305770509505287 7183684893458655764257931)
  ·
    refine ⟨10775527340187983646386897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7183684893458655764257931 10775527340187983646386897)
    ·
      refine ⟨8081645505140987734790173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10775527340187983646386897 8081645505140987734790173)
      ·
        refine ⟨3030617064427870400546315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8081645505140987734790173 3030617064427870400546315)
        ·
          refine ⟨4545925596641805600819473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3030617064427870400546315 4545925596641805600819473)
          ·
            refine ⟨3409444197481354200614605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4545925596641805600819473 3409444197481354200614605)
            ·
              refine ⟨1278541574055507825230477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3409444197481354200614605 1278541574055507825230477)
              ·
                refine ⟨479453090270815434461429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1278541574055507825230477 479453090270815434461429)
                ·
                  refine ⟨44948727212888946980759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 479453090270815434461429 44948727212888946980759)
                  ·
                    rfl

theorem cell21_196959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 5].length) (baseStart_196959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_196959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_196959 prefixEnd_196959 := by exact prefixLift 196959
  have htrace : WordTrace (prefixWord ++ tailWord_196959) baseStart_196959 baseEnd_196959 := by
    simpa [prefixWord, tailWord_196959, baseEnd_196959] using wordTrace_append hprefix tailTrace_196959
  have hstable : (prefixWord ++ tailWord_196959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196959).length < 2 ^ (prefixWord ++ tailWord_196959).sum := by decide
  have hdescent : baseEnd_196959 < baseStart_196959 := by decide
  rcases family_descends (prefixWord ++ tailWord_196959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197004 : List Nat := [2, 2, 1, 2, 1, 4, 9]
def baseStart_197004 : Nat := 118140960795 + 197004 * 2 ^ 59
def prefixEnd_197004 : Nat := 4983230072969 + 3 ^ 40 * 197004 * 2
def baseEnd_197004 : Nat := 4995444091775429858963

theorem tailTrace_197004 : CollatzResearch.WordTrace tailWord_197004 prefixEnd_197004 4995444091775429858963 := by
  unfold tailWord_197004
  simp only [CollatzResearch.WordTrace]
  refine ⟨3592663089147814224823033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4790217452197085633097377 3592663089147814224823033)
  ·
    refine ⟨2694497316860860668617275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3592663089147814224823033 2694497316860860668617275)
    ·
      refine ⟨4041745975291291002925913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2694497316860860668617275 4041745975291291002925913)
      ·
        refine ⟨3031309481468468252194435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4041745975291291002925913 3031309481468468252194435)
        ·
          refine ⟨4546964222202702378291653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3031309481468468252194435 4546964222202702378291653)
          ·
            refine ⟨852555791663006695929685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4546964222202702378291653 852555791663006695929685)
            ·
              refine ⟨4995444091775429858963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 852555791663006695929685 4995444091775429858963)
              ·
                rfl

theorem cell21_197004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 9].length) (baseStart_197004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197004 prefixEnd_197004 := by exact prefixLift 197004
  have htrace : WordTrace (prefixWord ++ tailWord_197004) baseStart_197004 baseEnd_197004 := by
    simpa [prefixWord, tailWord_197004, baseEnd_197004] using wordTrace_append hprefix tailTrace_197004
  have hstable : (prefixWord ++ tailWord_197004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197004).length < 2 ^ (prefixWord ++ tailWord_197004).sum := by decide
  have hdescent : baseEnd_197004 < baseStart_197004 := by decide
  rcases family_descends (prefixWord ++ tailWord_197004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197024 : List Nat := [2, 1, 1, 4, 1, 5, 2, 1, 4]
def baseStart_197024 : Nat := 118140960795 + 197024 * 2 ^ 59
def prefixEnd_197024 : Nat := 4983230072969 + 3 ^ 40 * 197024 * 2
def baseEnd_197024 : Nat := 44963561098463278397293

theorem tailTrace_197024 : CollatzResearch.WordTrace tailWord_197024 prefixEnd_197024 44963561098463278397293 := by
  unfold tailWord_197024
  simp only [CollatzResearch.WordTrace]
  refine ⟨3593027819111585932687063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4790703758815447910249417 3593027819111585932687063)
  ·
    refine ⟨5389541728667378899030595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3593027819111585932687063 5389541728667378899030595)
    ·
      refine ⟨8084312593001068348545893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5389541728667378899030595 8084312593001068348545893)
      ·
        refine ⟨1515808611187700315352355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8084312593001068348545893 1515808611187700315352355)
        ·
          refine ⟨2273712916781550473028533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515808611187700315352355 2273712916781550473028533)
          ·
            refine ⟨213160585948270356846425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2273712916781550473028533 213160585948270356846425)
            ·
              refine ⟨159870439461202767634819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213160585948270356846425 159870439461202767634819)
              ·
                refine ⟨239805659191804151452229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159870439461202767634819 239805659191804151452229)
                ·
                  refine ⟨44963561098463278397293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 239805659191804151452229 44963561098463278397293)
                  ·
                    rfl

theorem cell21_197024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 4].length) (baseStart_197024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197024 prefixEnd_197024 := by exact prefixLift 197024
  have htrace : WordTrace (prefixWord ++ tailWord_197024) baseStart_197024 baseEnd_197024 := by
    simpa [prefixWord, tailWord_197024, baseEnd_197024] using wordTrace_append hprefix tailTrace_197024
  have hstable : (prefixWord ++ tailWord_197024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197024).length < 2 ^ (prefixWord ++ tailWord_197024).sum := by decide
  have hdescent : baseEnd_197024 < baseStart_197024 := by decide
  rcases family_descends (prefixWord ++ tailWord_197024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197162 : List Nat := [3, 1, 4, 1, 1, 4, 1, 3, 3]
def baseStart_197162 : Nat := 118140960795 + 197162 * 2 ^ 59
def prefixEnd_197162 : Nat := 4983230072969 + 3 ^ 40 * 197162 * 2
def baseEnd_197162 : Nat := 44995054578605705097011

theorem tailTrace_197162 : CollatzResearch.WordTrace tailWord_197162 prefixEnd_197162 44995054578605705097011 := by
  unfold tailWord_197162
  simp only [CollatzResearch.WordTrace]
  refine ⟨1797772227930805358474435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4794059274482147622598493 1797772227930805358474435)
  ·
    refine ⟨2696658341896208037711653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1797772227930805358474435 2696658341896208037711653)
    ·
      refine ⟨505623439105539007070935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2696658341896208037711653 505623439105539007070935)
      ·
        refine ⟨758435158658308510606403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505623439105539007070935 758435158658308510606403)
        ·
          refine ⟨1137652737987462765909605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758435158658308510606403 1137652737987462765909605)
          ·
            refine ⟨213309888372649268608051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1137652737987462765909605 213309888372649268608051)
            ·
              refine ⟨319964832558973902912077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213309888372649268608051 319964832558973902912077)
              ·
                refine ⟨119986812209615213592029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319964832558973902912077 119986812209615213592029)
                ·
                  refine ⟨44995054578605705097011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119986812209615213592029 44995054578605705097011)
                  ·
                    rfl

theorem cell21_197162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_197162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197162 prefixEnd_197162 := by exact prefixLift 197162
  have htrace : WordTrace (prefixWord ++ tailWord_197162) baseStart_197162 baseEnd_197162 := by
    simpa [prefixWord, tailWord_197162, baseEnd_197162] using wordTrace_append hprefix tailTrace_197162
  have hstable : (prefixWord ++ tailWord_197162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197162).length < 2 ^ (prefixWord ++ tailWord_197162).sum := by decide
  have hdescent : baseEnd_197162 < baseStart_197162 := by decide
  rcases family_descends (prefixWord ++ tailWord_197162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197190 : List Nat := [6, 1, 1, 1, 2, 1, 1, 8]
def baseStart_197190 : Nat := 118140960795 + 197190 * 2 ^ 59
def prefixEnd_197190 : Nat := 4983230072969 + 3 ^ 40 * 197190 * 2
def baseEnd_197190 : Nat := 15000481520027959543429

theorem tailTrace_197190 : CollatzResearch.WordTrace tailWord_197190 prefixEnd_197190 15000481520027959543429 := by
  unfold tailWord_197190
  simp only [CollatzResearch.WordTrace]
  refine ⟨224753442363180694247407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4794740103747854810611349 224753442363180694247407)
  ·
    refine ⟨337130163544771041371111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224753442363180694247407 337130163544771041371111)
    ·
      refine ⟨505695245317156562056667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337130163544771041371111 505695245317156562056667)
      ·
        refine ⟨758542867975734843085001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505695245317156562056667 758542867975734843085001)
        ·
          refine ⟨568907150981801132313751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 758542867975734843085001 568907150981801132313751)
          ·
            refine ⟨853360726472701698470627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568907150981801132313751 853360726472701698470627)
            ·
              refine ⟨1280041089709052547705941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853360726472701698470627 1280041089709052547705941)
              ·
                refine ⟨15000481520027959543429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1280041089709052547705941 15000481520027959543429)
                ·
                  rfl

theorem cell21_197190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_197190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197190 prefixEnd_197190 := by exact prefixLift 197190
  have htrace : WordTrace (prefixWord ++ tailWord_197190) baseStart_197190 baseEnd_197190 := by
    simpa [prefixWord, tailWord_197190, baseEnd_197190] using wordTrace_append hprefix tailTrace_197190
  have hstable : (prefixWord ++ tailWord_197190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197190).length < 2 ^ (prefixWord ++ tailWord_197190).sum := by decide
  have hdescent : baseEnd_197190 < baseStart_197190 := by decide
  rcases family_descends (prefixWord ++ tailWord_197190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197232 : List Nat := [2, 1, 1, 1, 7, 9]
def baseStart_197232 : Nat := 118140960795 + 197232 * 2 ^ 59
def prefixEnd_197232 : Nat := 4983230072969 + 3 ^ 40 * 197232 * 2
def baseEnd_197232 : Nat := 1667075167863005145563

theorem tailTrace_197232 : CollatzResearch.WordTrace tailWord_197232 prefixEnd_197232 1667075167863005145563 := by
  unfold tailWord_197232
  simp only [CollatzResearch.WordTrace]
  refine ⟨3596821010734811694472975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4795761347646415592630633 3596821010734811694472975)
  ·
    refine ⟨5395231516102217541709463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3596821010734811694472975 5395231516102217541709463)
    ·
      refine ⟨8092847274153326312564195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5395231516102217541709463 8092847274153326312564195)
      ·
        refine ⟨12139270911229989468846293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8092847274153326312564195 12139270911229989468846293)
        ·
          refine ⟨284514161981952878176085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 12139270911229989468846293 284514161981952878176085)
          ·
            refine ⟨1667075167863005145563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 284514161981952878176085 1667075167863005145563)
            ·
              rfl

theorem cell21_197232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 9].length) (baseStart_197232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197232 prefixEnd_197232 := by exact prefixLift 197232
  have htrace : WordTrace (prefixWord ++ tailWord_197232) baseStart_197232 baseEnd_197232 := by
    simpa [prefixWord, tailWord_197232, baseEnd_197232] using wordTrace_append hprefix tailTrace_197232
  have hstable : (prefixWord ++ tailWord_197232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197232).length < 2 ^ (prefixWord ++ tailWord_197232).sum := by decide
  have hdescent : baseEnd_197232 < baseStart_197232 := by decide
  rcases family_descends (prefixWord ++ tailWord_197232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197238 : List Nat := [5, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_197238 : Nat := 118140960795 + 197238 * 2 ^ 59
def prefixEnd_197238 : Nat := 4983230072969 + 3 ^ 40 * 197238 * 2
def baseEnd_197238 : Nat := 45012398814046461830189

theorem tailTrace_197238 : CollatzResearch.WordTrace tailWord_197238 prefixEnd_197238 45012398814046461830189 := by
  unfold tailWord_197238
  simp only [CollatzResearch.WordTrace]
  refine ⟨449616303715492900854023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4795907239631924275776245 449616303715492900854023)
  ·
    refine ⟨674424455573239351281035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 449616303715492900854023 674424455573239351281035)
    ·
      refine ⟨1011636683359859026921553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 674424455573239351281035 1011636683359859026921553)
      ·
        refine ⟨758727512519894270191165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1011636683359859026921553 758727512519894270191165)
        ·
          refine ⟨284522817194960351321687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 758727512519894270191165 284522817194960351321687)
          ·
            refine ⟨426784225792440526982531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284522817194960351321687 426784225792440526982531)
            ·
              refine ⟨640176338688660790473797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426784225792440526982531 640176338688660790473797)
              ·
                refine ⟨120033063504123898213837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 640176338688660790473797 120033063504123898213837)
                ·
                  refine ⟨45012398814046461830189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120033063504123898213837 45012398814046461830189)
                  ·
                    rfl

theorem cell21_197238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_197238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197238 prefixEnd_197238 := by exact prefixLift 197238
  have htrace : WordTrace (prefixWord ++ tailWord_197238) baseStart_197238 baseEnd_197238 := by
    simpa [prefixWord, tailWord_197238, baseEnd_197238] using wordTrace_append hprefix tailTrace_197238
  have hstable : (prefixWord ++ tailWord_197238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197238).length < 2 ^ (prefixWord ++ tailWord_197238).sum := by decide
  have hdescent : baseEnd_197238 < baseStart_197238 := by decide
  rcases family_descends (prefixWord ++ tailWord_197238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197266 : List Nat := [3, 2, 3, 1, 2, 2, 3, 5]
def baseStart_197266 : Nat := 118140960795 + 197266 * 2 ^ 59
def prefixEnd_197266 : Nat := 4983230072969 + 3 ^ 40 * 197266 * 2
def baseEnd_197266 : Nat := 15006262931841545121155

theorem tailTrace_197266 : CollatzResearch.WordTrace tailWord_197266 prefixEnd_197266 15006262931841545121155 := by
  unfold tailWord_197266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1798720525836611798920913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4796588068897631463789101 1798720525836611798920913)
  ·
    refine ⟨1349040394377458849190685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1798720525836611798920913 1349040394377458849190685)
    ·
      refine ⟨505890147891547068446507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1349040394377458849190685 505890147891547068446507)
      ·
        refine ⟨758835221837320602669761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505890147891547068446507 758835221837320602669761)
        ·
          refine ⟨569126416377990452002321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 758835221837320602669761 569126416377990452002321)
          ·
            refine ⟨426844812283492839001741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569126416377990452002321 426844812283492839001741)
            ·
              refine ⟨160066804606309814625653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 426844812283492839001741 160066804606309814625653)
              ·
                refine ⟨15006262931841545121155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160066804606309814625653 15006262931841545121155)
                ·
                  rfl

theorem cell21_197266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_197266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197266 prefixEnd_197266 := by exact prefixLift 197266
  have htrace : WordTrace (prefixWord ++ tailWord_197266) baseStart_197266 baseEnd_197266 := by
    simpa [prefixWord, tailWord_197266, baseEnd_197266] using wordTrace_append hprefix tailTrace_197266
  have hstable : (prefixWord ++ tailWord_197266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197266).length < 2 ^ (prefixWord ++ tailWord_197266).sum := by decide
  have hdescent : baseEnd_197266 < baseStart_197266 := by decide
  rcases family_descends (prefixWord ++ tailWord_197266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197297 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 5]
def baseStart_197297 : Nat := 118140960795 + 197297 * 2 ^ 59
def prefixEnd_197297 : Nat := 4983230072969 + 3 ^ 40 * 197297 * 2
def baseEnd_197297 : Nat := 45025863417875470346735

theorem tailTrace_197297 : CollatzResearch.WordTrace tailWord_197297 prefixEnd_197297 45025863417875470346735 := by
  unfold tailWord_197297
  simp only [CollatzResearch.WordTrace]
  refine ⟨7196012766234139490062145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4797341844156092993374763 7196012766234139490062145)
  ·
    refine ⟨5397009574675604617546609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7196012766234139490062145 5397009574675604617546609)
    ·
      refine ⟨4047757181006703463159957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5397009574675604617546609 4047757181006703463159957)
      ·
        refine ⟨189738617859689224835623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4047757181006703463159957 189738617859689224835623)
        ·
          refine ⟨284607926789533837253435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189738617859689224835623 284607926789533837253435)
          ·
            refine ⟨426911890184300755880153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284607926789533837253435 426911890184300755880153)
            ·
              refine ⟨320183917638225566910115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426911890184300755880153 320183917638225566910115)
              ·
                refine ⟨480275876457338350365173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320183917638225566910115 480275876457338350365173)
                ·
                  refine ⟨45025863417875470346735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 480275876457338350365173 45025863417875470346735)
                  ·
                    rfl

theorem cell21_197297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_197297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197297 prefixEnd_197297 := by exact prefixLift 197297
  have htrace : WordTrace (prefixWord ++ tailWord_197297) baseStart_197297 baseEnd_197297 := by
    simpa [prefixWord, tailWord_197297, baseEnd_197297] using wordTrace_append hprefix tailTrace_197297
  have hstable : (prefixWord ++ tailWord_197297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197297).length < 2 ^ (prefixWord ++ tailWord_197297).sum := by decide
  have hdescent : baseEnd_197297 < baseStart_197297 := by decide
  rcases family_descends (prefixWord ++ tailWord_197297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197308 : List Nat := [2, 2, 2, 3, 1, 1, 2, 8]
def baseStart_197308 : Nat := 118140960795 + 197308 * 2 ^ 59
def prefixEnd_197308 : Nat := 4983230072969 + 3 ^ 40 * 197308 * 2
def baseEnd_197308 : Nat := 15009457922580631887793

theorem tailTrace_197308 : CollatzResearch.WordTrace tailWord_197308 prefixEnd_197308 15009457922580631887793 := by
  unfold tailWord_197308
  simp only [CollatzResearch.WordTrace]
  refine ⟨3598206984597144184356289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4797609312796192245808385 3598206984597144184356289)
  ·
    refine ⟨2698655238447858138267217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3598206984597144184356289 2698655238447858138267217)
    ·
      refine ⟨2023991428835893603700413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2698655238447858138267217 2023991428835893603700413)
      ·
        refine ⟨758996785813460101387655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2023991428835893603700413 758996785813460101387655)
        ·
          refine ⟨1138495178720190152081483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758996785813460101387655 1138495178720190152081483)
          ·
            refine ⟨1707742768080285228122225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138495178720190152081483 1707742768080285228122225)
            ·
              refine ⟨1280807076060213921091669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1707742768080285228122225 1280807076060213921091669)
              ·
                refine ⟨15009457922580631887793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1280807076060213921091669 15009457922580631887793)
                ·
                  rfl

theorem cell21_197308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 8].length) (baseStart_197308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197308 prefixEnd_197308 := by exact prefixLift 197308
  have htrace : WordTrace (prefixWord ++ tailWord_197308) baseStart_197308 baseEnd_197308 := by
    simpa [prefixWord, tailWord_197308, baseEnd_197308] using wordTrace_append hprefix tailTrace_197308
  have hstable : (prefixWord ++ tailWord_197308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197308).length < 2 ^ (prefixWord ++ tailWord_197308).sum := by decide
  have hdescent : baseEnd_197308 < baseStart_197308 := by decide
  rcases family_descends (prefixWord ++ tailWord_197308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197311 : List Nat := [1, 1, 2, 2, 2, 5, 3, 1, 4]
def baseStart_197311 : Nat := 118140960795 + 197311 * 2 ^ 59
def prefixEnd_197311 : Nat := 4983230072969 + 3 ^ 40 * 197311 * 2
def baseEnd_197311 : Nat := 45029058408614557113373

theorem tailTrace_197311 : CollatzResearch.WordTrace tailWord_197311 prefixEnd_197311 45029058408614557113373 := by
  unfold tailWord_197311
  simp only [CollatzResearch.WordTrace]
  refine ⟨7196523388183419881071787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4797682258788946587381191 7196523388183419881071787)
  ·
    refine ⟨10794785082275129821607681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7196523388183419881071787 10794785082275129821607681)
    ·
      refine ⟨8096088811706347366205761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10794785082275129821607681 8096088811706347366205761)
      ·
        refine ⟨6072066608779760524654321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8096088811706347366205761 6072066608779760524654321)
        ·
          refine ⟨4554049956584820393490741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6072066608779760524654321 4554049956584820393490741)
          ·
            refine ⟨426942183429826911889757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4554049956584820393490741 426942183429826911889757)
            ·
              refine ⟨160103318786185091958659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 426942183429826911889757 160103318786185091958659)
              ·
                refine ⟨240154978179277637937989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160103318786185091958659 240154978179277637937989)
                ·
                  refine ⟨45029058408614557113373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 240154978179277637937989 45029058408614557113373)
                  ·
                    rfl

theorem cell21_197311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 4].length) (baseStart_197311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197311 prefixEnd_197311 := by exact prefixLift 197311
  have htrace : WordTrace (prefixWord ++ tailWord_197311) baseStart_197311 baseEnd_197311 := by
    simpa [prefixWord, tailWord_197311, baseEnd_197311] using wordTrace_append hprefix tailTrace_197311
  have hstable : (prefixWord ++ tailWord_197311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197311).length < 2 ^ (prefixWord ++ tailWord_197311).sum := by decide
  have hdescent : baseEnd_197311 < baseStart_197311 := by decide
  rcases family_descends (prefixWord ++ tailWord_197311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197353 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 6]
def baseStart_197353 : Nat := 118140960795 + 197353 * 2 ^ 59
def prefixEnd_197353 : Nat := 4983230072969 + 3 ^ 40 * 197353 * 2
def baseEnd_197353 : Nat := 45038643380831817413287

theorem tailTrace_197353 : CollatzResearch.WordTrace tailWord_197353 prefixEnd_197353 45038643380831817413287 := by
  unfold tailWord_197353
  simp only [CollatzResearch.WordTrace]
  refine ⟨7198055254031261054100713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4798703502687507369400475 7198055254031261054100713)
  ·
    refine ⟨5398541440523445790575535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7198055254031261054100713 5398541440523445790575535)
    ·
      refine ⟨8097812160785168685863303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5398541440523445790575535 8097812160785168685863303)
      ·
        refine ⟨12146718241177753028794955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8097812160785168685863303 12146718241177753028794955)
        ·
          refine ⟨18220077361766629543192433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12146718241177753028794955 18220077361766629543192433)
          ·
            refine ⟨13665058021324972157394325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18220077361766629543192433 13665058021324972157394325)
            ·
              refine ⟨640549594749608069877859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13665058021324972157394325 640549594749608069877859)
              ·
                refine ⟨960824392124412104816789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640549594749608069877859 960824392124412104816789)
                ·
                  refine ⟨45038643380831817413287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 960824392124412104816789 45038643380831817413287)
                  ·
                    rfl

theorem cell21_197353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_197353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197353 prefixEnd_197353 := by exact prefixLift 197353
  have htrace : WordTrace (prefixWord ++ tailWord_197353) baseStart_197353 baseEnd_197353 := by
    simpa [prefixWord, tailWord_197353, baseEnd_197353] using wordTrace_append hprefix tailTrace_197353
  have hstable : (prefixWord ++ tailWord_197353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197353).length < 2 ^ (prefixWord ++ tailWord_197353).sum := by decide
  have hdescent : baseEnd_197353 < baseStart_197353 := by decide
  rcases family_descends (prefixWord ++ tailWord_197353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197384 : List Nat := [2, 1, 3, 2, 2, 2, 2, 7]
def baseStart_197384 : Nat := 118140960795 + 197384 * 2 ^ 59
def prefixEnd_197384 : Nat := 4983230072969 + 3 ^ 40 * 197384 * 2
def baseEnd_197384 : Nat := 15015239334394217465519

theorem tailTrace_197384 : CollatzResearch.WordTrace tailWord_197384 prefixEnd_197384 15015239334394217465519 := by
  unfold tailWord_197384
  simp only [CollatzResearch.WordTrace]
  refine ⟨3599592958459476674239603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4799457277945968898986137 3599592958459476674239603)
  ·
    refine ⟨5399389437689215011359405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3599592958459476674239603 5399389437689215011359405)
    ·
      refine ⟨2024771039133455629259777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5399389437689215011359405 2024771039133455629259777)
      ·
        refine ⟨1518578279350091721944833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2024771039133455629259777 1518578279350091721944833)
        ·
          refine ⟨1138933709512568791458625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1518578279350091721944833 1138933709512568791458625)
          ·
            refine ⟨854200282134426593593969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1138933709512568791458625 854200282134426593593969)
            ·
              refine ⟨640650211600819945195477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854200282134426593593969 640650211600819945195477)
              ·
                refine ⟨15015239334394217465519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 640650211600819945195477 15015239334394217465519)
                ·
                  rfl

theorem cell21_197384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 7].length) (baseStart_197384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197384 prefixEnd_197384 := by exact prefixLift 197384
  have htrace : WordTrace (prefixWord ++ tailWord_197384) baseStart_197384 baseEnd_197384 := by
    simpa [prefixWord, tailWord_197384, baseEnd_197384] using wordTrace_append hprefix tailTrace_197384
  have hstable : (prefixWord ++ tailWord_197384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197384).length < 2 ^ (prefixWord ++ tailWord_197384).sum := by decide
  have hdescent : baseEnd_197384 < baseStart_197384 := by decide
  rcases family_descends (prefixWord ++ tailWord_197384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197463 : List Nat := [1, 1, 3, 2, 4, 3, 1, 2, 4]
def baseStart_197463 : Nat := 118140960795 + 197463 * 2 ^ 59
def prefixEnd_197463 : Nat := 4983230072969 + 3 ^ 40 * 197463 * 2
def baseEnd_197463 : Nat := 45063746879496070579729

theorem tailTrace_197463 : CollatzResearch.WordTrace tailWord_197463 prefixEnd_197463 45063746879496070579729 := by
  unfold tailWord_197463
  simp only [CollatzResearch.WordTrace]
  refine ⟨7202067283632749840605043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4801378189088499893736695 7202067283632749840605043)
  ·
    refine ⟨10803100925449124760907565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7202067283632749840605043 10803100925449124760907565)
    ·
      refine ⟨4051162847043421785340337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10803100925449124760907565 4051162847043421785340337)
      ·
        refine ⟨3038372135282566339005253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4051162847043421785340337 3038372135282566339005253)
        ·
          refine ⟨569694775365481188563485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3038372135282566339005253 569694775365481188563485)
          ·
            refine ⟨213635540762055445711307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 569694775365481188563485 213635540762055445711307)
            ·
              refine ⟨320453311143083168566961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213635540762055445711307 320453311143083168566961)
              ·
                refine ⟨240339983357312376425221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320453311143083168566961 240339983357312376425221)
                ·
                  refine ⟨45063746879496070579729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 240339983357312376425221 45063746879496070579729)
                  ·
                    rfl

theorem cell21_197463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 4].length) (baseStart_197463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197463 prefixEnd_197463 := by exact prefixLift 197463
  have htrace : WordTrace (prefixWord ++ tailWord_197463) baseStart_197463 baseEnd_197463 := by
    simpa [prefixWord, tailWord_197463, baseEnd_197463] using wordTrace_append hprefix tailTrace_197463
  have hstable : (prefixWord ++ tailWord_197463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197463).length < 2 ^ (prefixWord ++ tailWord_197463).sum := by decide
  have hdescent : baseEnd_197463 < baseStart_197463 := by decide
  rcases family_descends (prefixWord ++ tailWord_197463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197494 : List Nat := [5, 1, 1, 3, 1, 1, 4, 5]
def baseStart_197494 : Nat := 118140960795 + 197494 * 2 ^ 59
def prefixEnd_197494 : Nat := 4983230072969 + 3 ^ 40 * 197494 * 2
def baseEnd_197494 : Nat := 15023607167282301854333

theorem tailTrace_197494 : CollatzResearch.WordTrace tailWord_197494 prefixEnd_197494 15023607167282301854333 := by
  unfold tailWord_197494
  simp only [CollatzResearch.WordTrace]
  refine ⟨450199871657527633436471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4802131964346961423322357 450199871657527633436471)
  ·
    refine ⟨675299807486291450154707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 450199871657527633436471 675299807486291450154707)
    ·
      refine ⟨1012949711229437175232061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 675299807486291450154707 1012949711229437175232061)
      ·
        refine ⟨379856141711038940712023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1012949711229437175232061 379856141711038940712023)
        ·
          refine ⟨569784212566558411068035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379856141711038940712023 569784212566558411068035)
          ·
            refine ⟨854676318849837616602053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569784212566558411068035 854676318849837616602053)
            ·
              refine ⟨160251809784344553112885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 854676318849837616602053 160251809784344553112885)
              ·
                refine ⟨15023607167282301854333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160251809784344553112885 15023607167282301854333)
                ·
                  rfl

theorem cell21_197494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_197494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197494 prefixEnd_197494 := by exact prefixLift 197494
  have htrace : WordTrace (prefixWord ++ tailWord_197494) baseStart_197494 baseEnd_197494 := by
    simpa [prefixWord, tailWord_197494, baseEnd_197494] using wordTrace_append hprefix tailTrace_197494
  have hstable : (prefixWord ++ tailWord_197494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197494).length < 2 ^ (prefixWord ++ tailWord_197494).sum := by decide
  have hdescent : baseEnd_197494 < baseStart_197494 := by decide
  rcases family_descends (prefixWord ++ tailWord_197494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197525 : List Nat := [1, 3, 2, 1, 1, 5, 3, 2, 3]
def baseStart_197525 : Nat := 118140960795 + 197525 * 2 ^ 59
def prefixEnd_197525 : Nat := 4983230072969 + 3 ^ 40 * 197525 * 2
def baseEnd_197525 : Nat := 45077896124197740546269

theorem tailTrace_197525 : CollatzResearch.WordTrace tailWord_197525 prefixEnd_197525 45077896124197740546269 := by
  unfold tailWord_197525
  simp only [CollatzResearch.WordTrace]
  refine ⟨7204328609408134429362029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4802885739605422952908019 7204328609408134429362029)
  ·
    refine ⟨2701623228528050411010761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7204328609408134429362029 2701623228528050411010761)
    ·
      refine ⟨2026217421396037808258071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2701623228528050411010761 2026217421396037808258071)
      ·
        refine ⟨3039326132094056712387107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2026217421396037808258071 3039326132094056712387107)
        ·
          refine ⟨4558989198141085068580661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3039326132094056712387107 4558989198141085068580661)
          ·
            refine ⟨427405237325726725179437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4558989198141085068580661 427405237325726725179437)
            ·
              refine ⟨160276963997147521942289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 427405237325726725179437 160276963997147521942289)
              ·
                refine ⟨120207722997860641456717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160276963997147521942289 120207722997860641456717)
                ·
                  refine ⟨45077896124197740546269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120207722997860641456717 45077896124197740546269)
                  ·
                    rfl

theorem cell21_197525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_197525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197525 prefixEnd_197525 := by exact prefixLift 197525
  have htrace : WordTrace (prefixWord ++ tailWord_197525) baseStart_197525 baseEnd_197525 := by
    simpa [prefixWord, tailWord_197525, baseEnd_197525] using wordTrace_append hprefix tailTrace_197525
  have hstable : (prefixWord ++ tailWord_197525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197525).length < 2 ^ (prefixWord ++ tailWord_197525).sum := by decide
  have hdescent : baseEnd_197525 < baseStart_197525 := by decide
  rcases family_descends (prefixWord ++ tailWord_197525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197618 : List Nat := [3, 2, 1, 5, 1, 1, 2, 3, 3]
def baseStart_197618 : Nat := 118140960795 + 197618 * 2 ^ 59
def prefixEnd_197618 : Nat := 4983230072969 + 3 ^ 40 * 197618 * 2
def baseEnd_197618 : Nat := 45099119991250245496079

theorem tailTrace_197618 : CollatzResearch.WordTrace tailWord_197618 prefixEnd_197618 45099119991250245496079 := by
  unfold tailWord_197618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1801930149517802828124377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4805147065380807541665005 1801930149517802828124377)
  ·
    refine ⟨1351447612138352121093283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1801930149517802828124377 1351447612138352121093283)
    ·
      refine ⟨2027171418207528181639925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1351447612138352121093283 2027171418207528181639925)
      ·
        refine ⟨190047320456955767028743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2027171418207528181639925 190047320456955767028743)
        ·
          refine ⟨285070980685433650543115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190047320456955767028743 285070980685433650543115)
          ·
            refine ⟨427606471028150475814673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285070980685433650543115 427606471028150475814673)
            ·
              refine ⟨320704853271112856861005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427606471028150475814673 320704853271112856861005)
              ·
                refine ⟨120264319976667321322877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320704853271112856861005 120264319976667321322877)
                ·
                  refine ⟨45099119991250245496079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120264319976667321322877 45099119991250245496079)
                  ·
                    rfl

theorem cell21_197618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_197618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197618 prefixEnd_197618 := by exact prefixLift 197618
  have htrace : WordTrace (prefixWord ++ tailWord_197618) baseStart_197618 baseEnd_197618 := by
    simpa [prefixWord, tailWord_197618, baseEnd_197618] using wordTrace_append hprefix tailTrace_197618
  have hstable : (prefixWord ++ tailWord_197618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197618).length < 2 ^ (prefixWord ++ tailWord_197618).sum := by decide
  have hdescent : baseEnd_197618 < baseStart_197618 := by decide
  rcases family_descends (prefixWord ++ tailWord_197618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197643 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 5]
def baseStart_197643 : Nat := 118140960795 + 197643 * 2 ^ 59
def prefixEnd_197643 : Nat := 4983230072969 + 3 ^ 40 * 197643 * 2
def baseEnd_197643 : Nat := 45104825331855757579361

theorem tailTrace_197643 : CollatzResearch.WordTrace tailWord_197643 prefixEnd_197643 45104825331855757579361 := by
  unfold tailWord_197643
  simp only [CollatzResearch.WordTrace]
  refine ⟨7208632422980640582157583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4805754948653760388105055 7208632422980640582157583)
  ·
    refine ⟨10812948634470960873236375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7208632422980640582157583 10812948634470960873236375)
    ·
      refine ⟨16219422951706441309854563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10812948634470960873236375 16219422951706441309854563)
      ·
        refine ⟨24329134427559661964781845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16219422951706441309854563 24329134427559661964781845)
        ·
          refine ⟨1140428176291859154599149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24329134427559661964781845 1140428176291859154599149)
          ·
            refine ⟨427660566109447182974681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1140428176291859154599149 427660566109447182974681)
            ·
              refine ⟨320745424582085387231011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427660566109447182974681 320745424582085387231011)
              ·
                refine ⟨481118136873128080846517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320745424582085387231011 481118136873128080846517)
                ·
                  refine ⟨45104825331855757579361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 481118136873128080846517 45104825331855757579361)
                  ·
                    rfl

theorem cell21_197643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 5].length) (baseStart_197643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197643 prefixEnd_197643 := by exact prefixLift 197643
  have htrace : WordTrace (prefixWord ++ tailWord_197643) baseStart_197643 baseEnd_197643 := by
    simpa [prefixWord, tailWord_197643, baseEnd_197643] using wordTrace_append hprefix tailTrace_197643
  have hstable : (prefixWord ++ tailWord_197643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197643).length < 2 ^ (prefixWord ++ tailWord_197643).sum := by decide
  have hdescent : baseEnd_197643 < baseStart_197643 := by decide
  rcases family_descends (prefixWord ++ tailWord_197643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197657 : List Nat := [1, 2, 1, 2, 1, 1, 4, 5, 4]
def baseStart_197657 : Nat := 118140960795 + 197657 * 2 ^ 59
def prefixEnd_197657 : Nat := 4983230072969 + 3 ^ 40 * 197657 * 2
def baseEnd_197657 : Nat := 45108020322594844345999

theorem tailTrace_197657 : CollatzResearch.WordTrace tailWord_197657 prefixEnd_197657 45108020322594844345999 := by
  unfold tailWord_197657
  simp only [CollatzResearch.WordTrace]
  refine ⟨7209143044929920973167225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4806095363286613982111483 7209143044929920973167225)
  ·
    refine ⟨5406857283697440729875419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7209143044929920973167225 5406857283697440729875419)
    ·
      refine ⟨8110285925546161094813129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5406857283697440729875419 8110285925546161094813129)
      ·
        refine ⟨6082714444159620821109847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8110285925546161094813129 6082714444159620821109847)
        ·
          refine ⟨9124071666239431231664771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6082714444159620821109847 9124071666239431231664771)
          ·
            refine ⟨13686107499359146847497157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9124071666239431231664771 13686107499359146847497157)
            ·
              refine ⟨2566145156129840033905717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13686107499359146847497157 2566145156129840033905717)
              ·
                refine ⟨240576108387172503178661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2566145156129840033905717 240576108387172503178661)
                ·
                  refine ⟨45108020322594844345999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 240576108387172503178661 45108020322594844345999)
                  ·
                    rfl

theorem cell21_197657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_197657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197657 prefixEnd_197657 := by exact prefixLift 197657
  have htrace : WordTrace (prefixWord ++ tailWord_197657) baseStart_197657 baseEnd_197657 := by
    simpa [prefixWord, tailWord_197657, baseEnd_197657] using wordTrace_append hprefix tailTrace_197657
  have hstable : (prefixWord ++ tailWord_197657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197657).length < 2 ^ (prefixWord ++ tailWord_197657).sum := by decide
  have hdescent : baseEnd_197657 < baseStart_197657 := by decide
  rcases family_descends (prefixWord ++ tailWord_197657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197688 : List Nat := [2, 1, 2, 1, 5, 3, 7]
def baseStart_197688 : Nat := 118140960795 + 197688 * 2 ^ 59
def prefixEnd_197688 : Nat := 4983230072969 + 3 ^ 40 * 197688 * 2
def baseEnd_197688 : Nat := 5012788327216186592141

theorem tailTrace_197688 : CollatzResearch.WordTrace tailWord_197688 prefixEnd_197688 5012788327216186592141 := by
  unfold tailWord_197688
  simp only [CollatzResearch.WordTrace]
  refine ⟨3605136853908806633772859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4806849138545075511697145 3605136853908806633772859)
  ·
    refine ⟨5407705280863209950659289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3605136853908806633772859 5407705280863209950659289)
    ·
      refine ⟨4055778960647407462994467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5407705280863209950659289 4055778960647407462994467)
      ·
        refine ⟨6083668440971111194491701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4055778960647407462994467 6083668440971111194491701)
        ·
          refine ⟨570343916341041674483597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6083668440971111194491701 570343916341041674483597)
          ·
            refine ⟨213878968627890627931349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 570343916341041674483597 213878968627890627931349)
            ·
              refine ⟨5012788327216186592141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 213878968627890627931349 5012788327216186592141)
              ·
                rfl

theorem cell21_197688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 7].length) (baseStart_197688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197688 prefixEnd_197688 := by exact prefixLift 197688
  have htrace : WordTrace (prefixWord ++ tailWord_197688) baseStart_197688 baseEnd_197688 := by
    simpa [prefixWord, tailWord_197688, baseEnd_197688] using wordTrace_append hprefix tailTrace_197688
  have hstable : (prefixWord ++ tailWord_197688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197688).length < 2 ^ (prefixWord ++ tailWord_197688).sum := by decide
  have hdescent : baseEnd_197688 < baseStart_197688 := by decide
  rcases family_descends (prefixWord ++ tailWord_197688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197694 : List Nat := [4, 2, 1, 3, 1, 2, 3, 2, 3]
def baseStart_197694 : Nat := 118140960795 + 197694 * 2 ^ 59
def prefixEnd_197694 : Nat := 4983230072969 + 3 ^ 40 * 197694 * 2
def baseEnd_197694 : Nat := 45116464226691002229257

theorem tailTrace_197694 : CollatzResearch.WordTrace tailWord_197694 prefixEnd_197694 45116464226691002229257 := by
  unfold tailWord_197694
  simp only [CollatzResearch.WordTrace]
  refine ⟨901311568224484536533017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4806995030530584194842757 901311568224484536533017)
  ·
    refine ⟨675983676168363402399763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 901311568224484536533017 675983676168363402399763)
    ·
      refine ⟨1013975514252545103599645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 675983676168363402399763 1013975514252545103599645)
      ·
        refine ⟨380240817844704413849867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1013975514252545103599645 380240817844704413849867)
        ·
          refine ⟨570361226767056620774801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380240817844704413849867 570361226767056620774801)
          ·
            refine ⟨427770920075292465581101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 570361226767056620774801 427770920075292465581101)
            ·
              refine ⟨160414095028234674592913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 427770920075292465581101 160414095028234674592913)
              ·
                refine ⟨120310571271176005944685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160414095028234674592913 120310571271176005944685)
                ·
                  refine ⟨45116464226691002229257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120310571271176005944685 45116464226691002229257)
                  ·
                    rfl

theorem cell21_197694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_197694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197694 prefixEnd_197694 := by exact prefixLift 197694
  have htrace : WordTrace (prefixWord ++ tailWord_197694) baseStart_197694 baseEnd_197694 := by
    simpa [prefixWord, tailWord_197694, baseEnd_197694] using wordTrace_append hprefix tailTrace_197694
  have hstable : (prefixWord ++ tailWord_197694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197694).length < 2 ^ (prefixWord ++ tailWord_197694).sum := by decide
  have hdescent : baseEnd_197694 < baseStart_197694 := by decide
  rcases family_descends (prefixWord ++ tailWord_197694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197764 : List Nat := [2, 3, 2, 1, 2, 2, 3, 6]
def baseStart_197764 : Nat := 118140960795 + 197764 * 2 ^ 59
def prefixEnd_197764 : Nat := 4983230072969 + 3 ^ 40 * 197764 * 2
def baseEnd_197764 : Nat := 15044146393462145354149

theorem tailTrace_197764 : CollatzResearch.WordTrace tailWord_197764 prefixEnd_197764 15044146393462145354149 := by
  unfold tailWord_197764
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606522827771139123656173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4808697103694852164874897 3606522827771139123656173)
  ·
    refine ⟨1352446060414177171371065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3606522827771139123656173 1352446060414177171371065)
    ·
      refine ⟨1014334545310632878528299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1352446060414177171371065 1014334545310632878528299)
      ·
        refine ⟨1521501817965949317792449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1014334545310632878528299 1521501817965949317792449)
        ·
          refine ⟨1141126363474461988344337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1521501817965949317792449 1141126363474461988344337)
          ·
            refine ⟨855844772605846491258253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1141126363474461988344337 855844772605846491258253)
            ·
              refine ⟨320941789727192434221845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 855844772605846491258253 320941789727192434221845)
              ·
                refine ⟨15044146393462145354149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 320941789727192434221845 15044146393462145354149)
                ·
                  rfl

theorem cell21_197764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 6].length) (baseStart_197764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197764 prefixEnd_197764 := by exact prefixLift 197764
  have htrace : WordTrace (prefixWord ++ tailWord_197764) baseStart_197764 baseEnd_197764 := by
    simpa [prefixWord, tailWord_197764, baseEnd_197764] using wordTrace_append hprefix tailTrace_197764
  have hstable : (prefixWord ++ tailWord_197764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197764).length < 2 ^ (prefixWord ++ tailWord_197764).sum := by decide
  have hdescent : baseEnd_197764 < baseStart_197764 := by decide
  rcases family_descends (prefixWord ++ tailWord_197764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197899 : List Nat := [1, 1, 1, 1, 5, 3, 2, 7]
def baseStart_197899 : Nat := 118140960795 + 197899 * 2 ^ 59
def prefixEnd_197899 : Nat := 4983230072969 + 3 ^ 40 * 197899 * 2
def baseEnd_197899 : Nat := 15054416006552067104057

theorem tailTrace_197899 : CollatzResearch.WordTrace tailWord_197899 prefixEnd_197899 15054416006552067104057 := by
  unfold tailWord_197899
  simp only [CollatzResearch.WordTrace]
  refine ⟨7217969510053196303476751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4811979673368797535651167 7217969510053196303476751)
  ·
    refine ⟨10826954265079794455215127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7217969510053196303476751 10826954265079794455215127)
    ·
      refine ⟨16240431397619691682822691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10826954265079794455215127 16240431397619691682822691)
      ·
        refine ⟨24360647096429537524234037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16240431397619691682822691 24360647096429537524234037)
        ·
          refine ⟨2283810665290269142896941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24360647096429537524234037 2283810665290269142896941)
          ·
            refine ⟨856428999483850928586353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2283810665290269142896941 856428999483850928586353)
            ·
              refine ⟨642321749612888196439765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 856428999483850928586353 642321749612888196439765)
              ·
                refine ⟨15054416006552067104057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 642321749612888196439765 15054416006552067104057)
                ·
                  rfl

theorem cell21_197899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 7].length) (baseStart_197899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197899 prefixEnd_197899 := by exact prefixLift 197899
  have htrace : WordTrace (prefixWord ++ tailWord_197899) baseStart_197899 baseEnd_197899 := by
    simpa [prefixWord, tailWord_197899, baseEnd_197899] using wordTrace_append hprefix tailTrace_197899
  have hstable : (prefixWord ++ tailWord_197899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197899).length < 2 ^ (prefixWord ++ tailWord_197899).sum := by decide
  have hdescent : baseEnd_197899 < baseStart_197899 := by decide
  rcases family_descends (prefixWord ++ tailWord_197899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197922 : List Nat := [3, 3, 1, 1, 4, 2, 2, 2, 3]
def baseStart_197922 : Nat := 118140960795 + 197922 * 2 ^ 59
def prefixEnd_197922 : Nat := 4983230072969 + 3 ^ 40 * 197922 * 2
def baseEnd_197922 : Nat := 45168496933013272428791

theorem tailTrace_197922 : CollatzResearch.WordTrace tailWord_197922 prefixEnd_197922 45168496933013272428791 := by
  unfold tailWord_197922
  simp only [CollatzResearch.WordTrace]
  refine ⟨1804702097242467807891005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4812538925979914154376013 1804702097242467807891005)
  ·
    refine ⟨676763286465925427959127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1804702097242467807891005 676763286465925427959127)
    ·
      refine ⟨1015144929698888141938691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 676763286465925427959127 1015144929698888141938691)
      ·
        refine ⟨1522717394548332212908037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1015144929698888141938691 1522717394548332212908037)
        ·
          refine ⟨285509511477812289920257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1522717394548332212908037 285509511477812289920257)
          ·
            refine ⟨214132133608359217440193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285509511477812289920257 214132133608359217440193)
            ·
              refine ⟨160599100206269413080145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214132133608359217440193 160599100206269413080145)
              ·
                refine ⟨120449325154702059810109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160599100206269413080145 120449325154702059810109)
                ·
                  refine ⟨45168496933013272428791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120449325154702059810109 45168496933013272428791)
                  ·
                    rfl

theorem cell21_197922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_197922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197922 prefixEnd_197922 := by exact prefixLift 197922
  have htrace : WordTrace (prefixWord ++ tailWord_197922) baseStart_197922 baseEnd_197922 := by
    simpa [prefixWord, tailWord_197922, baseEnd_197922] using wordTrace_append hprefix tailTrace_197922
  have hstable : (prefixWord ++ tailWord_197922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197922).length < 2 ^ (prefixWord ++ tailWord_197922).sum := by decide
  have hdescent : baseEnd_197922 < baseStart_197922 := by decide
  rcases family_descends (prefixWord ++ tailWord_197922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197933 : List Nat := [1, 5, 3, 1, 1, 1, 3, 6]
def baseStart_197933 : Nat := 118140960795 + 197933 * 2 ^ 59
def prefixEnd_197933 : Nat := 4983230072969 + 3 ^ 40 * 197933 * 2
def baseEnd_197933 : Nat := 15057002427626565915145

theorem tailTrace_197933 : CollatzResearch.WordTrace tailWord_197933 prefixEnd_197933 15057002427626565915145 := by
  unfold tailWord_197933
  simp only [CollatzResearch.WordTrace]
  refine ⟨7219209591930020110214453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4812806394620013406809635 7219209591930020110214453)
  ·
    refine ⟨676800899243439385332605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7219209591930020110214453 676800899243439385332605)
    ·
      refine ⟨253800337216289769499727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 676800899243439385332605 253800337216289769499727)
      ·
        refine ⟨380700505824434654249591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253800337216289769499727 380700505824434654249591)
        ·
          refine ⟨571050758736651981374387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380700505824434654249591 571050758736651981374387)
          ·
            refine ⟨856576138104977972061581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571050758736651981374387 856576138104977972061581)
            ·
              refine ⟨321216051789366739523093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 856576138104977972061581 321216051789366739523093)
              ·
                refine ⟨15057002427626565915145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 321216051789366739523093 15057002427626565915145)
                ·
                  rfl

theorem cell21_197933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 6].length) (baseStart_197933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197933 prefixEnd_197933 := by exact prefixLift 197933
  have htrace : WordTrace (prefixWord ++ tailWord_197933) baseStart_197933 baseEnd_197933 := by
    simpa [prefixWord, tailWord_197933, baseEnd_197933] using wordTrace_append hprefix tailTrace_197933
  have hstable : (prefixWord ++ tailWord_197933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197933).length < 2 ^ (prefixWord ++ tailWord_197933).sum := by decide
  have hdescent : baseEnd_197933 < baseStart_197933 := by decide
  rcases family_descends (prefixWord ++ tailWord_197933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197944 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 8]
def baseStart_197944 : Nat := 118140960795 + 197944 * 2 ^ 59
def prefixEnd_197944 : Nat := 4983230072969 + 3 ^ 40 * 197944 * 2
def baseEnd_197944 : Nat := 45173517632746123062079

theorem tailTrace_197944 : CollatzResearch.WordTrace tailWord_197944 prefixEnd_197944 45173517632746123062079 := by
  unfold tailWord_197944
  simp only [CollatzResearch.WordTrace]
  refine ⟨3609805397445084494432443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4813073863260112659243257 3609805397445084494432443)
  ·
    refine ⟨5414708096167626741648665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3609805397445084494432443 5414708096167626741648665)
    ·
      refine ⟨4061031072125720056236499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5414708096167626741648665 4061031072125720056236499)
      ·
        refine ⟨6091546608188580084354749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4061031072125720056236499 6091546608188580084354749)
        ·
          refine ⟨2284329978070717531633031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6091546608188580084354749 2284329978070717531633031)
          ·
            refine ⟨3426494967106076297449547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284329978070717531633031 3426494967106076297449547)
            ·
              refine ⟨5139742450659114446174321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3426494967106076297449547 5139742450659114446174321)
              ·
                refine ⟨3854806837994335834630741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5139742450659114446174321 3854806837994335834630741)
                ·
                  refine ⟨45173517632746123062079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3854806837994335834630741 45173517632746123062079)
                  ·
                    rfl

theorem cell21_197944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_197944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197944 prefixEnd_197944 := by exact prefixLift 197944
  have htrace : WordTrace (prefixWord ++ tailWord_197944) baseStart_197944 baseEnd_197944 := by
    simpa [prefixWord, tailWord_197944, baseEnd_197944] using wordTrace_append hprefix tailTrace_197944
  have hstable : (prefixWord ++ tailWord_197944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197944).length < 2 ^ (prefixWord ++ tailWord_197944).sum := by decide
  have hdescent : baseEnd_197944 < baseStart_197944 := by decide
  rcases family_descends (prefixWord ++ tailWord_197944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197964 : List Nat := [2, 2, 1, 3, 2, 3, 2, 3, 3]
def baseStart_197964 : Nat := 118140960795 + 197964 * 2 ^ 59
def prefixEnd_197964 : Nat := 4983230072969 + 3 ^ 40 * 197964 * 2
def baseEnd_197964 : Nat := 45178081905230532728705

theorem tailTrace_197964 : CollatzResearch.WordTrace tailWord_197964 prefixEnd_197964 45178081905230532728705 := by
  unfold tailWord_197964
  simp only [CollatzResearch.WordTrace]
  refine ⟨3610170127408856202296473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4813560169878474936395297 3610170127408856202296473)
  ·
    refine ⟨2707627595556642151722355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3610170127408856202296473 2707627595556642151722355)
    ·
      refine ⟨4061441393334963227583533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2707627595556642151722355 4061441393334963227583533)
      ·
        refine ⟨1523040522500611210343825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4061441393334963227583533 1523040522500611210343825)
        ·
          refine ⟨1142280391875458407757869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1523040522500611210343825 1142280391875458407757869)
          ·
            refine ⟨428355146953296902909201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1142280391875458407757869 428355146953296902909201)
            ·
              refine ⟨321266360214972677181901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428355146953296902909201 321266360214972677181901)
              ·
                refine ⟨120474885080614753943213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321266360214972677181901 120474885080614753943213)
                ·
                  refine ⟨45178081905230532728705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120474885080614753943213 45178081905230532728705)
                  ·
                    rfl

theorem cell21_197964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_197964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197964 prefixEnd_197964 := by exact prefixLift 197964
  have htrace : WordTrace (prefixWord ++ tailWord_197964) baseStart_197964 baseEnd_197964 := by
    simpa [prefixWord, tailWord_197964, baseEnd_197964] using wordTrace_append hprefix tailTrace_197964
  have hstable : (prefixWord ++ tailWord_197964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197964).length < 2 ^ (prefixWord ++ tailWord_197964).sum := by decide
  have hdescent : baseEnd_197964 < baseStart_197964 := by decide
  rcases family_descends (prefixWord ++ tailWord_197964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197975 : List Nat := [1, 1, 3, 2, 3, 3, 8]
def baseStart_197975 : Nat := 118140960795 + 197975 * 2 ^ 59
def prefixEnd_197975 : Nat := 4983230072969 + 3 ^ 40 * 197975 * 2
def baseEnd_197975 : Nat := 5020065806121884227261

theorem tailTrace_197975 : CollatzResearch.WordTrace tailWord_197975 prefixEnd_197975 5020065806121884227261 := by
  unfold tailWord_197975
  simp only [CollatzResearch.WordTrace]
  refine ⟨7220741457777861283243379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4813827638518574188828919 7220741457777861283243379)
  ·
    refine ⟨10831112186666791924865069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7220741457777861283243379 10831112186666791924865069)
    ·
      refine ⟨4061667070000046971824401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10831112186666791924865069 4061667070000046971824401)
      ·
        refine ⟨3046250302500035228868301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4061667070000046971824401 3046250302500035228868301)
        ·
          refine ⟨1142343863437513210825613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3046250302500035228868301 1142343863437513210825613)
          ·
            refine ⟨428378948789067454059605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1142343863437513210825613 428378948789067454059605)
            ·
              refine ⟨5020065806121884227261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 428378948789067454059605 5020065806121884227261)
              ·
                rfl

theorem cell21_197975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 8].length) (baseStart_197975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_197975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_197975 prefixEnd_197975 := by exact prefixLift 197975
  have htrace : WordTrace (prefixWord ++ tailWord_197975) baseStart_197975 baseEnd_197975 := by
    simpa [prefixWord, tailWord_197975, baseEnd_197975] using wordTrace_append hprefix tailTrace_197975
  have hstable : (prefixWord ++ tailWord_197975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197975).length < 2 ^ (prefixWord ++ tailWord_197975).sum := by decide
  have hdescent : baseEnd_197975 < baseStart_197975 := by decide
  rcases family_descends (prefixWord ++ tailWord_197975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198040 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 5]
def baseStart_198040 : Nat := 118140960795 + 198040 * 2 ^ 59
def prefixEnd_198040 : Nat := 4983230072969 + 3 ^ 40 * 198040 * 2
def baseEnd_198040 : Nat := 45195426140671289461883

theorem tailTrace_198040 : CollatzResearch.WordTrace tailWord_198040 prefixEnd_198040 45195426140671289461883 := by
  unfold tailWord_198040
  simp only [CollatzResearch.WordTrace]
  refine ⟨3611556101271188692179787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4815408135028251589573049 3611556101271188692179787)
  ·
    refine ⟨5417334151906783038269681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3611556101271188692179787 5417334151906783038269681)
    ·
      refine ⟨4063000613930087278702261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5417334151906783038269681 4063000613930087278702261)
      ·
        refine ⟨380906307555945682378337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4063000613930087278702261 380906307555945682378337)
        ·
          refine ⟨285679730666959261783753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380906307555945682378337 285679730666959261783753)
          ·
            refine ⟨214259798000219446337815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285679730666959261783753 214259798000219446337815)
            ·
              refine ⟨321389697000329169506723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214259798000219446337815 321389697000329169506723)
              ·
                refine ⟨482084545500493754260085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321389697000329169506723 482084545500493754260085)
                ·
                  refine ⟨45195426140671289461883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 482084545500493754260085 45195426140671289461883)
                  ·
                    rfl

theorem cell21_198040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_198040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198040 prefixEnd_198040 := by exact prefixLift 198040
  have htrace : WordTrace (prefixWord ++ tailWord_198040) baseStart_198040 baseEnd_198040 := by
    simpa [prefixWord, tailWord_198040, baseEnd_198040] using wordTrace_append hprefix tailTrace_198040
  have hstable : (prefixWord ++ tailWord_198040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198040).length < 2 ^ (prefixWord ++ tailWord_198040).sum := by decide
  have hdescent : baseEnd_198040 < baseStart_198040 := by decide
  rcases family_descends (prefixWord ++ tailWord_198040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198051 : List Nat := [1, 1, 1, 4, 1, 3, 4, 6]
def baseStart_198051 : Nat := 118140960795 + 198051 * 2 ^ 59
def prefixEnd_198051 : Nat := 4983230072969 + 3 ^ 40 * 198051 * 2
def baseEnd_198051 : Nat := 15065978830179238259509

theorem tailTrace_198051 : CollatzResearch.WordTrace tailWord_198051 prefixEnd_198051 15065978830179238259509 := by
  unfold tailWord_198051
  simp only [CollatzResearch.WordTrace]
  refine ⟨7223513405502526263010007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4815675603668350842006671 7223513405502526263010007)
  ·
    refine ⟨10835270108253789394515011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7223513405502526263010007 10835270108253789394515011)
    ·
      refine ⟨16252905162380684091772517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10835270108253789394515011 16252905162380684091772517)
      ·
        refine ⟨3047419717946378267207347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16252905162380684091772517 3047419717946378267207347)
        ·
          refine ⟨4571129576919567400811021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3047419717946378267207347 4571129576919567400811021)
          ·
            refine ⟨1714173591344837775304133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4571129576919567400811021 1714173591344837775304133)
            ·
              refine ⟨321407548377157082869525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1714173591344837775304133 321407548377157082869525)
              ·
                refine ⟨15065978830179238259509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 321407548377157082869525 15065978830179238259509)
                ·
                  rfl

theorem cell21_198051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 6].length) (baseStart_198051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198051 prefixEnd_198051 := by exact prefixLift 198051
  have htrace : WordTrace (prefixWord ++ tailWord_198051) baseStart_198051 baseEnd_198051 := by
    simpa [prefixWord, tailWord_198051, baseEnd_198051] using wordTrace_append hprefix tailTrace_198051
  have hstable : (prefixWord ++ tailWord_198051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198051).length < 2 ^ (prefixWord ++ tailWord_198051).sum := by decide
  have hdescent : baseEnd_198051 < baseStart_198051 := by decide
  rcases family_descends (prefixWord ++ tailWord_198051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198113 : List Nat := [1, 2, 3, 1, 2, 3, 2, 3, 4]
def baseStart_198113 : Nat := 118140960795 + 198113 * 2 ^ 59
def prefixEnd_198113 : Nat := 4983230072969 + 3 ^ 40 * 198113 * 2
def baseEnd_198113 : Nat := 45212085735239384745067

theorem tailTrace_198113 : CollatzResearch.WordTrace tailWord_198113 prefixEnd_198113 45212085735239384745067 := by
  unfold tailWord_198113
  simp only [CollatzResearch.WordTrace]
  refine ⟨7225774731277910851766993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4817183154185273901177995 7225774731277910851766993)
  ·
    refine ⟨5419331048458433138825245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7225774731277910851766993 5419331048458433138825245)
    ·
      refine ⟨2032249143171912427059467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5419331048458433138825245 2032249143171912427059467)
      ·
        refine ⟨3048373714757868640589201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2032249143171912427059467 3048373714757868640589201)
        ·
          refine ⟨2286280286068401480441901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3048373714757868640589201 2286280286068401480441901)
          ·
            refine ⟨857355107275650555165713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2286280286068401480441901 857355107275650555165713)
            ·
              refine ⟨643016330456737916374285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857355107275650555165713 643016330456737916374285)
              ·
                refine ⟨241131123921276718640357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 643016330456737916374285 241131123921276718640357)
                ·
                  refine ⟨45212085735239384745067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 241131123921276718640357 45212085735239384745067)
                  ·
                    rfl

theorem cell21_198113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_198113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198113 prefixEnd_198113 := by exact prefixLift 198113
  have htrace : WordTrace (prefixWord ++ tailWord_198113) baseStart_198113 baseEnd_198113 := by
    simpa [prefixWord, tailWord_198113, baseEnd_198113] using wordTrace_append hprefix tailTrace_198113
  have hstable : (prefixWord ++ tailWord_198113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198113).length < 2 ^ (prefixWord ++ tailWord_198113).sum := by decide
  have hdescent : baseEnd_198113 < baseStart_198113 := by decide
  rcases family_descends (prefixWord ++ tailWord_198113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198133 : List Nat := [1, 3, 5, 1, 1, 2, 2, 3, 3]
def baseStart_198133 : Nat := 118140960795 + 198133 * 2 ^ 59
def prefixEnd_198133 : Nat := 4983230072969 + 3 ^ 40 * 198133 * 2
def baseEnd_198133 : Nat := 45216650007723794411693

theorem tailTrace_198133 : CollatzResearch.WordTrace tailWord_198133 prefixEnd_198133 45216650007723794411693 := by
  unfold tailWord_198133
  simp only [CollatzResearch.WordTrace]
  refine ⟨7226504191205454267495053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4817669460803636178330035 7226504191205454267495053)
  ·
    refine ⟨2709939071702045350310645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7226504191205454267495053 2709939071702045350310645)
    ·
      refine ⟨254056787972066751591623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2709939071702045350310645 254056787972066751591623)
      ·
        refine ⟨381085181958100127387435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254056787972066751591623 381085181958100127387435)
        ·
          refine ⟨571627772937150191081153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381085181958100127387435 571627772937150191081153)
          ·
            refine ⟨428720829702862643310865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571627772937150191081153 428720829702862643310865)
            ·
              refine ⟨321540622277146982483149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428720829702862643310865 321540622277146982483149)
              ·
                refine ⟨120577733353930118431181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321540622277146982483149 120577733353930118431181)
                ·
                  refine ⟨45216650007723794411693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120577733353930118431181 45216650007723794411693)
                  ·
                    rfl

theorem cell21_198133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_198133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198133 prefixEnd_198133 := by exact prefixLift 198133
  have htrace : WordTrace (prefixWord ++ tailWord_198133) baseStart_198133 baseEnd_198133 := by
    simpa [prefixWord, tailWord_198133, baseEnd_198133] using wordTrace_append hprefix tailTrace_198133
  have hstable : (prefixWord ++ tailWord_198133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198133).length < 2 ^ (prefixWord ++ tailWord_198133).sum := by decide
  have hdescent : baseEnd_198133 < baseStart_198133 := by decide
  rcases family_descends (prefixWord ++ tailWord_198133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198150 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_198150 : Nat := 118140960795 + 198150 * 2 ^ 59
def prefixEnd_198150 : Nat := 4983230072969 + 3 ^ 40 * 198150 * 2
def baseEnd_198150 : Nat := 45220529639335542628325

theorem tailTrace_198150 : CollatzResearch.WordTrace tailWord_198150 prefixEnd_198150 45220529639335542628325 := by
  unfold tailWord_198150
  simp only [CollatzResearch.WordTrace]
  refine ⟨225847632254495817839497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4818082821429244113909269 225847632254495817839497)
  ·
    refine ⟨169385724190871863379623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225847632254495817839497 169385724190871863379623)
    ·
      refine ⟨254078586286307795069435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169385724190871863379623 254078586286307795069435)
      ·
        refine ⟨381117879429461692604153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254078586286307795069435 381117879429461692604153)
        ·
          refine ⟨285838409572096269453115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381117879429461692604153 285838409572096269453115)
          ·
            refine ⟨428757614358144404179673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285838409572096269453115 428757614358144404179673)
            ·
              refine ⟨321568210768608303134755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428757614358144404179673 321568210768608303134755)
              ·
                refine ⟨482352316152912454702133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321568210768608303134755 482352316152912454702133)
                ·
                  refine ⟨45220529639335542628325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 482352316152912454702133 45220529639335542628325)
                  ·
                    rfl

theorem cell21_198150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_198150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198150 prefixEnd_198150 := by exact prefixLift 198150
  have htrace : WordTrace (prefixWord ++ tailWord_198150) baseStart_198150 baseEnd_198150 := by
    simpa [prefixWord, tailWord_198150, baseEnd_198150] using wordTrace_append hprefix tailTrace_198150
  have hstable : (prefixWord ++ tailWord_198150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198150).length < 2 ^ (prefixWord ++ tailWord_198150).sum := by decide
  have hdescent : baseEnd_198150 < baseStart_198150 := by decide
  rcases family_descends (prefixWord ++ tailWord_198150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198164 : List Nat := [2, 4, 3, 1, 2, 1, 3, 1, 4]
def baseStart_198164 : Nat := 118140960795 + 198164 * 2 ^ 59
def prefixEnd_198164 : Nat := 4983230072969 + 3 ^ 40 * 198164 * 2
def baseEnd_198164 : Nat := 45223724630074629394963

theorem tailTrace_198164 : CollatzResearch.WordTrace tailWord_198164 prefixEnd_198164 45223724630074629394963 := by
  unfold tailWord_198164
  simp only [CollatzResearch.WordTrace]
  refine ⟨3613817427046573280936773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4818423236062097707915697 3613817427046573280936773)
  ·
    refine ⟨677590767571232490175645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3613817427046573280936773 677590767571232490175645)
    ·
      refine ⟨254096537839212183815867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 677590767571232490175645 254096537839212183815867)
      ·
        refine ⟨381144806758818275723801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254096537839212183815867 381144806758818275723801)
        ·
          refine ⟨285858605069113706792851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381144806758818275723801 285858605069113706792851)
          ·
            refine ⟨428787907603670560189277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285858605069113706792851 428787907603670560189277)
            ·
              refine ⟨160795465351376460070979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 428787907603670560189277 160795465351376460070979)
              ·
                refine ⟨241193198027064690106469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160795465351376460070979 241193198027064690106469)
                ·
                  refine ⟨45223724630074629394963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 241193198027064690106469 45223724630074629394963)
                  ·
                    rfl

theorem cell21_198164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_198164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198164 prefixEnd_198164 := by exact prefixLift 198164
  have htrace : WordTrace (prefixWord ++ tailWord_198164) baseStart_198164 baseEnd_198164 := by
    simpa [prefixWord, tailWord_198164, baseEnd_198164] using wordTrace_append hprefix tailTrace_198164
  have hstable : (prefixWord ++ tailWord_198164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198164).length < 2 ^ (prefixWord ++ tailWord_198164).sum := by decide
  have hdescent : baseEnd_198164 < baseStart_198164 := by decide
  rcases family_descends (prefixWord ++ tailWord_198164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198265 : List Nat := [1, 2, 1, 3, 3, 1, 4, 2, 4]
def baseStart_198265 : Nat := 118140960795 + 198265 * 2 ^ 59
def prefixEnd_198265 : Nat := 4983230072969 + 3 ^ 40 * 198265 * 2
def baseEnd_198265 : Nat := 45246774206120898211423

theorem tailTrace_198265 : CollatzResearch.WordTrace tailWord_198265 prefixEnd_198265 45246774206120898211423 := by
  unfold tailWord_198265
  simp only [CollatzResearch.WordTrace]
  refine ⟨7231318626727240811300249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4820879084484827207533499 7231318626727240811300249)
  ·
    refine ⟨5423488970045430608475187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7231318626727240811300249 5423488970045430608475187)
    ·
      refine ⟨8135233455068145912712781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5423488970045430608475187 8135233455068145912712781)
      ·
        refine ⟨3050712545650554717267293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8135233455068145912712781 3050712545650554717267293)
        ·
          refine ⟨1144017204618958018975235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3050712545650554717267293 1144017204618958018975235)
          ·
            refine ⟨1716025806928437028462853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144017204618958018975235 1716025806928437028462853)
            ·
              refine ⟨321754838799081942836785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1716025806928437028462853 321754838799081942836785)
              ·
                refine ⟨241316129099311457127589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321754838799081942836785 241316129099311457127589)
                ·
                  refine ⟨45246774206120898211423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 241316129099311457127589 45246774206120898211423)
                  ·
                    rfl

theorem cell21_198265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_198265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198265 prefixEnd_198265 := by exact prefixLift 198265
  have htrace : WordTrace (prefixWord ++ tailWord_198265) baseStart_198265 baseEnd_198265 := by
    simpa [prefixWord, tailWord_198265, baseEnd_198265] using wordTrace_append hprefix tailTrace_198265
  have hstable : (prefixWord ++ tailWord_198265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198265).length < 2 ^ (prefixWord ++ tailWord_198265).sum := by decide
  have hdescent : baseEnd_198265 < baseStart_198265 := by decide
  rcases family_descends (prefixWord ++ tailWord_198265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198279 : List Nat := [1, 1, 4, 2, 1, 3, 3, 6]
def baseStart_198279 : Nat := 118140960795 + 198279 * 2 ^ 59
def prefixEnd_198279 : Nat := 4983230072969 + 3 ^ 40 * 198279 * 2
def baseEnd_198279 : Nat := 15083323065619994992687

theorem tailTrace_198279 : CollatzResearch.WordTrace tailWord_198279 prefixEnd_198279 15083323065619994992687 := by
  unfold tailWord_198279
  simp only [CollatzResearch.WordTrace]
  refine ⟨7231829248676521202309891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4821219499117680801539927 7231829248676521202309891)
  ·
    refine ⟨10847743873014781803464837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7231829248676521202309891 10847743873014781803464837)
    ·
      refine ⟨2033951976190271588149657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10847743873014781803464837 2033951976190271588149657)
      ·
        refine ⟨1525463982142703691112243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2033951976190271588149657 1525463982142703691112243)
        ·
          refine ⟨2288195973214055536668365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1525463982142703691112243 2288195973214055536668365)
          ·
            refine ⟨858073489955270826250637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2288195973214055536668365 858073489955270826250637)
            ·
              refine ⟨321777558733226559843989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 858073489955270826250637 321777558733226559843989)
              ·
                refine ⟨15083323065619994992687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 321777558733226559843989 15083323065619994992687)
                ·
                  rfl

theorem cell21_198279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 6].length) (baseStart_198279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198279 prefixEnd_198279 := by exact prefixLift 198279
  have htrace : WordTrace (prefixWord ++ tailWord_198279) baseStart_198279 baseEnd_198279 := by
    simpa [prefixWord, tailWord_198279, baseEnd_198279] using wordTrace_append hprefix tailTrace_198279
  have hstable : (prefixWord ++ tailWord_198279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198279).length < 2 ^ (prefixWord ++ tailWord_198279).sum := by decide
  have hdescent : baseEnd_198279 < baseStart_198279 := by decide
  rcases family_descends (prefixWord ++ tailWord_198279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198296 : List Nat := [2, 1, 2, 4, 1, 3, 3, 5]
def baseStart_198296 : Nat := 118140960795 + 198296 * 2 ^ 59
def prefixEnd_198296 : Nat := 4983230072969 + 3 ^ 40 * 198296 * 2
def baseEnd_198296 : Nat := 15084616276157244398231

theorem tailTrace_198296 : CollatzResearch.WordTrace tailWord_198296 prefixEnd_198296 15084616276157244398231 := by
  unfold tailWord_198296
  simp only [CollatzResearch.WordTrace]
  refine ⟨3616224644807466552839371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4821632859743288737119161 3616224644807466552839371)
  ·
    refine ⟨5424336967211199829259057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3616224644807466552839371 5424336967211199829259057)
    ·
      refine ⟨4068252725408399871944293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5424336967211199829259057 4068252725408399871944293)
      ·
        refine ⟨762797386014074975989555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4068252725408399871944293 762797386014074975989555)
        ·
          refine ⟨1144196079021112463984333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762797386014074975989555 1144196079021112463984333)
          ·
            refine ⟨429073529632917173994125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1144196079021112463984333 429073529632917173994125)
            ·
              refine ⟨160902573612343940247797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 429073529632917173994125 160902573612343940247797)
              ·
                refine ⟨15084616276157244398231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160902573612343940247797 15084616276157244398231)
                ·
                  rfl

theorem cell21_198296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 5].length) (baseStart_198296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198296 prefixEnd_198296 := by exact prefixLift 198296
  have htrace : WordTrace (prefixWord ++ tailWord_198296) baseStart_198296 baseEnd_198296 := by
    simpa [prefixWord, tailWord_198296, baseEnd_198296] using wordTrace_append hprefix tailTrace_198296
  have hstable : (prefixWord ++ tailWord_198296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198296).length < 2 ^ (prefixWord ++ tailWord_198296).sum := by decide
  have hdescent : baseEnd_198296 < baseStart_198296 := by decide
  rcases family_descends (prefixWord ++ tailWord_198296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198327 : List Nat := [1, 1, 3, 1, 5, 1, 2, 4, 3]
def baseStart_198327 : Nat := 118140960795 + 198327 * 2 ^ 59
def prefixEnd_198327 : Nat := 4983230072969 + 3 ^ 40 * 198327 * 2
def baseEnd_198327 : Nat := 45260923450822568177963

theorem tailTrace_198327 : CollatzResearch.WordTrace tailWord_198327 prefixEnd_198327 45260923450822568177963 := by
  unfold tailWord_198327
  simp only [CollatzResearch.WordTrace]
  refine ⟨7233579952502625400057235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4822386635001750266704823 7233579952502625400057235)
  ·
    refine ⟨10850369928753938100085853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7233579952502625400057235 10850369928753938100085853)
    ·
      refine ⟨4068888723282726787532195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10850369928753938100085853 4068888723282726787532195)
      ·
        refine ⟨6103333084924090181298293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4068888723282726787532195 6103333084924090181298293)
        ·
          refine ⟨572187476711633454496715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6103333084924090181298293 572187476711633454496715)
          ·
            refine ⟨858281215067450181745073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572187476711633454496715 858281215067450181745073)
            ·
              refine ⟨643710911300587636308805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858281215067450181745073 643710911300587636308805)
              ·
                refine ⟨120695795868860181807901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 643710911300587636308805 120695795868860181807901)
                ·
                  refine ⟨45260923450822568177963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120695795868860181807901 45260923450822568177963)
                  ·
                    rfl

theorem cell21_198327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 3].length) (baseStart_198327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198327 prefixEnd_198327 := by exact prefixLift 198327
  have htrace : WordTrace (prefixWord ++ tailWord_198327) baseStart_198327 baseEnd_198327 := by
    simpa [prefixWord, tailWord_198327, baseEnd_198327] using wordTrace_append hprefix tailTrace_198327
  have hstable : (prefixWord ++ tailWord_198327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198327).length < 2 ^ (prefixWord ++ tailWord_198327).sum := by decide
  have hdescent : baseEnd_198327 < baseStart_198327 := by decide
  rcases family_descends (prefixWord ++ tailWord_198327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198400 : List Nat := [2, 1, 1, 2, 1, 1, 2, 7, 4]
def baseStart_198400 : Nat := 118140960795 + 198400 * 2 ^ 59
def prefixEnd_198400 : Nat := 4983230072969 + 3 ^ 40 * 198400 * 2
def baseEnd_198400 : Nat := 45277583045390663461147

theorem tailTrace_198400 : CollatzResearch.WordTrace tailWord_198400 prefixEnd_198400 45277583045390663461147 := by
  unfold tailWord_198400
  simp only [CollatzResearch.WordTrace]
  refine ⟨3618121240619079433732327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4824161654158772578309769 3618121240619079433732327)
  ·
    refine ⟨5427181860928619150598491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3618121240619079433732327 5427181860928619150598491)
    ·
      refine ⟨8140772791392928725897737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5427181860928619150598491 8140772791392928725897737)
      ·
        refine ⟨6105579593544696544423303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8140772791392928725897737 6105579593544696544423303)
        ·
          refine ⟨9158369390317044816634955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6105579593544696544423303 9158369390317044816634955)
          ·
            refine ⟨13737554085475567224952433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9158369390317044816634955 13737554085475567224952433)
            ·
              refine ⟨10303165564106675418714325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13737554085475567224952433 10303165564106675418714325)
              ·
                refine ⟨241480442908750205126117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10303165564106675418714325 241480442908750205126117)
                ·
                  refine ⟨45277583045390663461147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 241480442908750205126117 45277583045390663461147)
                  ·
                    rfl

theorem cell21_198400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_198400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198400 prefixEnd_198400 := by exact prefixLift 198400
  have htrace : WordTrace (prefixWord ++ tailWord_198400) baseStart_198400 baseEnd_198400 := by
    simpa [prefixWord, tailWord_198400, baseEnd_198400] using wordTrace_append hprefix tailTrace_198400
  have hstable : (prefixWord ++ tailWord_198400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198400).length < 2 ^ (prefixWord ++ tailWord_198400).sum := by decide
  have hdescent : baseEnd_198400 < baseStart_198400 := by decide
  rcases family_descends (prefixWord ++ tailWord_198400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198462 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_198462 : Nat := 118140960795 + 198462 * 2 ^ 59
def prefixEnd_198462 : Nat := 4983230072969 + 3 ^ 40 * 198462 * 2
def baseEnd_198462 : Nat := 45291732290092333427687

theorem tailTrace_198462 : CollatzResearch.WordTrace tailWord_198462 prefixEnd_198462 45291732290092333427687 := by
  unfold tailWord_198462
  simp only [CollatzResearch.WordTrace]
  refine ⟨904812975876692932027705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4825669204675695637481093 904812975876692932027705)
  ·
    refine ⟨678609731907519699020779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 904812975876692932027705 678609731907519699020779)
    ·
      refine ⟨1017914597861279548531169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 678609731907519699020779 1017914597861279548531169)
      ·
        refine ⟨763435948395959661398377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1017914597861279548531169 763435948395959661398377)
        ·
          refine ⟨572576961296969746048783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 763435948395959661398377 572576961296969746048783)
          ·
            refine ⟨858865441945454619073175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572576961296969746048783 858865441945454619073175)
            ·
              refine ⟨1288298162918181928609763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858865441945454619073175 1288298162918181928609763)
              ·
                refine ⟨1932447244377272892914645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1288298162918181928609763 1932447244377272892914645)
                ·
                  refine ⟨45291732290092333427687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1932447244377272892914645 45291732290092333427687)
                  ·
                    rfl

theorem cell21_198462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_198462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198462 prefixEnd_198462 := by exact prefixLift 198462
  have htrace : WordTrace (prefixWord ++ tailWord_198462) baseStart_198462 baseEnd_198462 := by
    simpa [prefixWord, tailWord_198462, baseEnd_198462] using wordTrace_append hprefix tailTrace_198462
  have hstable : (prefixWord ++ tailWord_198462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198462).length < 2 ^ (prefixWord ++ tailWord_198462).sum := by decide
  have hdescent : baseEnd_198462 < baseStart_198462 := by decide
  rcases family_descends (prefixWord ++ tailWord_198462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198490 : List Nat := [3, 1, 1, 2, 1, 3, 10]
def baseStart_198490 : Nat := 118140960795 + 198490 * 2 ^ 59
def prefixEnd_198490 : Nat := 4983230072969 + 3 ^ 40 * 198490 * 2
def baseEnd_198490 : Nat := 5033124696841167440107

theorem tailTrace_198490 : CollatzResearch.WordTrace tailWord_198490 prefixEnd_198490 5033124696841167440107 := by
  unfold tailWord_198490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1809881262728026059560231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4826350033941402825493949 1809881262728026059560231)
  ·
    refine ⟨2714821894092039089340347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1809881262728026059560231 2714821894092039089340347)
    ·
      refine ⟨4072232841138058634010521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2714821894092039089340347 4072232841138058634010521)
      ·
        refine ⟨3054174630853543975507891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4072232841138058634010521 3054174630853543975507891)
        ·
          refine ⟨4581261946280315963261837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3054174630853543975507891 4581261946280315963261837)
          ·
            refine ⟨1717973229855118486223189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4581261946280315963261837 1717973229855118486223189)
            ·
              refine ⟨5033124696841167440107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1717973229855118486223189 5033124696841167440107)
              ·
                rfl

theorem cell21_198490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 10].length) (baseStart_198490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198490 prefixEnd_198490 := by exact prefixLift 198490
  have htrace : WordTrace (prefixWord ++ tailWord_198490) baseStart_198490 baseEnd_198490 := by
    simpa [prefixWord, tailWord_198490, baseEnd_198490] using wordTrace_append hprefix tailTrace_198490
  have hstable : (prefixWord ++ tailWord_198490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198490).length < 2 ^ (prefixWord ++ tailWord_198490).sum := by decide
  have hdescent : baseEnd_198490 < baseStart_198490 := by decide
  rcases family_descends (prefixWord ++ tailWord_198490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198521 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 5]
def baseStart_198521 : Nat := 118140960795 + 198521 * 2 ^ 59
def prefixEnd_198521 : Nat := 4983230072969 + 3 ^ 40 * 198521 * 2
def baseEnd_198521 : Nat := 45305196893921341944233

theorem tailTrace_198521 : CollatzResearch.WordTrace tailWord_198521 prefixEnd_198521 45305196893921341944233 := by
  unfold tailWord_198521
  simp only [CollatzResearch.WordTrace]
  refine ⟨7240655713799796532619417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4827103809199864355079611 7240655713799796532619417)
  ·
    refine ⟨5430491785349847399464563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7240655713799796532619417 5430491785349847399464563)
    ·
      refine ⟨8145737678024771099196845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5430491785349847399464563 8145737678024771099196845)
      ·
        refine ⟨3054651629259289162198817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8145737678024771099196845 3054651629259289162198817)
        ·
          refine ⟨2290988721944466871649113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3054651629259289162198817 2290988721944466871649113)
          ·
            refine ⟨1718241541458350153736835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2290988721944466871649113 1718241541458350153736835)
            ·
              refine ⟨2577362312187525230605253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718241541458350153736835 2577362312187525230605253)
              ·
                refine ⟨483255433535160980738485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2577362312187525230605253 483255433535160980738485)
                ·
                  refine ⟨45305196893921341944233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 483255433535160980738485 45305196893921341944233)
                  ·
                    rfl

theorem cell21_198521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_198521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198521 prefixEnd_198521 := by exact prefixLift 198521
  have htrace : WordTrace (prefixWord ++ tailWord_198521) baseStart_198521 baseEnd_198521 := by
    simpa [prefixWord, tailWord_198521, baseEnd_198521] using wordTrace_append hprefix tailTrace_198521
  have hstable : (prefixWord ++ tailWord_198521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198521).length < 2 ^ (prefixWord ++ tailWord_198521).sum := by decide
  have hdescent : baseEnd_198521 < baseStart_198521 := by decide
  rcases family_descends (prefixWord ++ tailWord_198521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198628 : List Nat := [2, 3, 1, 1, 1, 1, 3, 5, 4]
def baseStart_198628 : Nat := 118140960795 + 198628 * 2 ^ 59
def prefixEnd_198628 : Nat := 4983230072969 + 3 ^ 40 * 198628 * 2
def baseEnd_198628 : Nat := 45329615751712933660681

theorem tailTrace_198628 : CollatzResearch.WordTrace tailWord_198628 prefixEnd_198628 45329615751712933660681 := by
  unfold tailWord_198628
  simp only [CollatzResearch.WordTrace]
  refine ⟨3622279162206076903382269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4829705549608102537843025 3622279162206076903382269)
  ·
    refine ⟨1358354685827278838768351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3622279162206076903382269 1358354685827278838768351)
    ·
      refine ⟨2037532028740918258152527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1358354685827278838768351 2037532028740918258152527)
      ·
        refine ⟨3056298043111377387228791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2037532028740918258152527 3056298043111377387228791)
        ·
          refine ⟨4584447064667066080843187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3056298043111377387228791 4584447064667066080843187)
          ·
            refine ⟨6876670597000599121264781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4584447064667066080843187 6876670597000599121264781)
            ·
              refine ⟨2578751473875224670474293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6876670597000599121264781 2578751473875224670474293)
              ·
                refine ⟨241757950675802312856965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2578751473875224670474293 241757950675802312856965)
                ·
                  refine ⟨45329615751712933660681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 241757950675802312856965 45329615751712933660681)
                  ·
                    rfl

theorem cell21_198628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_198628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198628 prefixEnd_198628 := by exact prefixLift 198628
  have htrace : WordTrace (prefixWord ++ tailWord_198628) baseStart_198628 baseEnd_198628 := by
    simpa [prefixWord, tailWord_198628, baseEnd_198628] using wordTrace_append hprefix tailTrace_198628
  have hstable : (prefixWord ++ tailWord_198628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198628).length < 2 ^ (prefixWord ++ tailWord_198628).sum := by decide
  have hdescent : baseEnd_198628 < baseStart_198628 := by decide
  rcases family_descends (prefixWord ++ tailWord_198628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198780 : List Nat := [2, 2, 2, 1, 1, 4, 1, 4, 4]
def baseStart_198780 : Nat := 118140960795 + 198780 * 2 ^ 59
def prefixEnd_198780 : Nat := 4983230072969 + 3 ^ 40 * 198780 * 2
def baseEnd_198780 : Nat := 45364304222594447127037

theorem tailTrace_198780 : CollatzResearch.WordTrace tailWord_198780 prefixEnd_198780 45364304222594447127037 := by
  unfold tailWord_198780
  simp only [CollatzResearch.WordTrace]
  refine ⟨3625051109930741883148897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4833401479907655844198529 3625051109930741883148897)
  ·
    refine ⟨2718788332448056412361673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3625051109930741883148897 2718788332448056412361673)
    ·
      refine ⟨2039091249336042309271255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2718788332448056412361673 2039091249336042309271255)
      ·
        refine ⟨3058636874004063463906883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2039091249336042309271255 3058636874004063463906883)
        ·
          refine ⟨4587955311006095195860325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3058636874004063463906883 4587955311006095195860325)
          ·
            refine ⟨860241620813642849223811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4587955311006095195860325 860241620813642849223811)
            ·
              refine ⟨1290362431220464273835717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860241620813642849223811 1290362431220464273835717)
              ·
                refine ⟨241942955853837051344197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1290362431220464273835717 241942955853837051344197)
                ·
                  refine ⟨45364304222594447127037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 241942955853837051344197 45364304222594447127037)
                  ·
                    rfl

theorem cell21_198780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_198780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198780 prefixEnd_198780 := by exact prefixLift 198780
  have htrace : WordTrace (prefixWord ++ tailWord_198780) baseStart_198780 baseEnd_198780 := by
    simpa [prefixWord, tailWord_198780, baseEnd_198780] using wordTrace_append hprefix tailTrace_198780
  have hstable : (prefixWord ++ tailWord_198780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198780).length < 2 ^ (prefixWord ++ tailWord_198780).sum := by decide
  have hdescent : baseEnd_198780 < baseStart_198780 := by decide
  rcases family_descends (prefixWord ++ tailWord_198780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198842 : List Nat := [3, 1, 1, 1, 2, 2, 4, 4, 3]
def baseStart_198842 : Nat := 118140960795 + 198842 * 2 ^ 59
def prefixEnd_198842 : Nat := 4983230072969 + 3 ^ 40 * 198842 * 2
def baseEnd_198842 : Nat := 45378453467296117093577

theorem tailTrace_198842 : CollatzResearch.WordTrace tailWord_198842 prefixEnd_198842 45378453467296117093577 := by
  unfold tailWord_198842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1813090886409217088763695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4834909030424578903369853 1813090886409217088763695)
  ·
    refine ⟨2719636329613825633145543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1813090886409217088763695 2719636329613825633145543)
    ·
      refine ⟨4079454494420738449718315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2719636329613825633145543 4079454494420738449718315)
      ·
        refine ⟨6119181741631107674577473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4079454494420738449718315 6119181741631107674577473)
        ·
          refine ⟨4589386306223330755933105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6119181741631107674577473 4589386306223330755933105)
          ·
            refine ⟨3442039729667498066949829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4589386306223330755933105 3442039729667498066949829)
            ·
              refine ⟨645382449312655887553093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3442039729667498066949829 645382449312655887553093)
              ·
                refine ⟨121009209246122978916205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 645382449312655887553093 121009209246122978916205)
                ·
                  refine ⟨45378453467296117093577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121009209246122978916205 45378453467296117093577)
                  ·
                    rfl

theorem cell21_198842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_198842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198842 prefixEnd_198842 := by exact prefixLift 198842
  have htrace : WordTrace (prefixWord ++ tailWord_198842) baseStart_198842 baseEnd_198842 := by
    simpa [prefixWord, tailWord_198842, baseEnd_198842] using wordTrace_append hprefix tailTrace_198842
  have hstable : (prefixWord ++ tailWord_198842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198842).length < 2 ^ (prefixWord ++ tailWord_198842).sum := by decide
  have hdescent : baseEnd_198842 < baseStart_198842 := by decide
  rcases family_descends (prefixWord ++ tailWord_198842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198887 : List Nat := [1, 1, 5, 3, 1, 3, 7]
def baseStart_198887 : Nat := 118140960795 + 198887 * 2 ^ 59
def prefixEnd_198887 : Nat := 4983230072969 + 3 ^ 40 * 198887 * 2
def baseEnd_198887 : Nat := 5043191453376226538165

theorem tailTrace_198887 : CollatzResearch.WordTrace tailWord_198887 prefixEnd_198887 5043191453376226538165 := by
  unfold tailWord_198887
  simp only [CollatzResearch.WordTrace]
  refine ⟨7254004830473841040442915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4836003220315894026961943 7254004830473841040442915)
  ·
    refine ⟨10881007245710761560664373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7254004830473841040442915 10881007245710761560664373)
    ·
      refine ⟨1020094429285383896312285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10881007245710761560664373 1020094429285383896312285)
      ·
        refine ⟨382535410982018961117107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1020094429285383896312285 382535410982018961117107)
        ·
          refine ⟨573803116473028441675661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382535410982018961117107 573803116473028441675661)
          ·
            refine ⟨215176168677385665628373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 573803116473028441675661 215176168677385665628373)
            ·
              refine ⟨5043191453376226538165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 215176168677385665628373 5043191453376226538165)
              ·
                rfl

theorem cell21_198887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 7].length) (baseStart_198887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198887 prefixEnd_198887 := by exact prefixLift 198887
  have htrace : WordTrace (prefixWord ++ tailWord_198887) baseStart_198887 baseEnd_198887 := by
    simpa [prefixWord, tailWord_198887, baseEnd_198887] using wordTrace_append hprefix tailTrace_198887
  have hstable : (prefixWord ++ tailWord_198887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198887).length < 2 ^ (prefixWord ++ tailWord_198887).sum := by decide
  have hdescent : baseEnd_198887 < baseStart_198887 := by decide
  rcases family_descends (prefixWord ++ tailWord_198887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198946 : List Nat := [3, 3, 1, 1, 3, 10]
def baseStart_198946 : Nat := 118140960795 + 198946 * 2 ^ 59
def prefixEnd_198946 : Nat := 4983230072969 + 3 ^ 40 * 198946 * 2
def baseEnd_198946 : Nat := 1681562506822779531853

theorem tailTrace_198946 : CollatzResearch.WordTrace tailWord_198946 prefixEnd_198946 1681562506822779531853 := by
  unfold tailWord_198946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1814039184315023529210173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4837437824840062744560461 1814039184315023529210173)
  ·
    refine ⟨680264694118133823453815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1814039184315023529210173 680264694118133823453815)
    ·
      refine ⟨1020397041177200735180723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 680264694118133823453815 1020397041177200735180723)
      ·
        refine ⟨1530595561765801102771085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020397041177200735180723 1530595561765801102771085)
        ·
          refine ⟨573973335662175413539157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1530595561765801102771085 573973335662175413539157)
          ·
            refine ⟨1681562506822779531853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 573973335662175413539157 1681562506822779531853)
            ·
              rfl

theorem cell21_198946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 10].length) (baseStart_198946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198946 prefixEnd_198946 := by exact prefixLift 198946
  have htrace : WordTrace (prefixWord ++ tailWord_198946) baseStart_198946 baseEnd_198946 := by
    simpa [prefixWord, tailWord_198946, baseEnd_198946] using wordTrace_append hprefix tailTrace_198946
  have hstable : (prefixWord ++ tailWord_198946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198946).length < 2 ^ (prefixWord ++ tailWord_198946).sum := by decide
  have hdescent : baseEnd_198946 < baseStart_198946 := by decide
  rcases family_descends (prefixWord ++ tailWord_198946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198949 : List Nat := [1, 3, 1, 2, 5, 1, 2, 2, 4]
def baseStart_198949 : Nat := 118140960795 + 198949 * 2 ^ 59
def prefixEnd_198949 : Nat := 4983230072969 + 3 ^ 40 * 198949 * 2
def baseEnd_198949 : Nat := 45402872325087708810025

theorem tailTrace_198949 : CollatzResearch.WordTrace tailWord_198949 prefixEnd_198949 45402872325087708810025 := by
  unfold tailWord_198949
  simp only [CollatzResearch.WordTrace]
  refine ⟨7256266156249225629199901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4837510770832817086133267 7256266156249225629199901)
  ·
    refine ⟨2721099808593459610949963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7256266156249225629199901 2721099808593459610949963)
    ·
      refine ⟨4081649712890189416424945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2721099808593459610949963 4081649712890189416424945)
      ·
        refine ⟨3061237284667642062318709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4081649712890189416424945 3061237284667642062318709)
        ·
          refine ⟨286990995437591443342379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3061237284667642062318709 286990995437591443342379)
          ·
            refine ⟨430486493156387165013569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286990995437591443342379 430486493156387165013569)
            ·
              refine ⟨322864869867290373760177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430486493156387165013569 322864869867290373760177)
              ·
                refine ⟨242148652400467780320133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322864869867290373760177 242148652400467780320133)
                ·
                  refine ⟨45402872325087708810025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242148652400467780320133 45402872325087708810025)
                  ·
                    rfl

theorem cell21_198949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_198949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198949 prefixEnd_198949 := by exact prefixLift 198949
  have htrace : WordTrace (prefixWord ++ tailWord_198949) baseStart_198949 baseEnd_198949 := by
    simpa [prefixWord, tailWord_198949, baseEnd_198949] using wordTrace_append hprefix tailTrace_198949
  have hstable : (prefixWord ++ tailWord_198949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198949).length < 2 ^ (prefixWord ++ tailWord_198949).sum := by decide
  have hdescent : baseEnd_198949 < baseStart_198949 := by decide
  rcases family_descends (prefixWord ++ tailWord_198949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198994 : List Nat := [3, 2, 2, 1, 1, 1, 3, 5, 3]
def baseStart_198994 : Nat := 118140960795 + 198994 * 2 ^ 59
def prefixEnd_198994 : Nat := 4983230072969 + 3 ^ 40 * 198994 * 2
def baseEnd_198994 : Nat := 45413141938177630559933

theorem tailTrace_198994 : CollatzResearch.WordTrace tailWord_198994 prefixEnd_198994 45413141938177630559933 := by
  unfold tailWord_198994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1814476860271549578647009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4838604960724132209725357 1814476860271549578647009)
  ·
    refine ⟨1360857645203662183985257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1814476860271549578647009 1360857645203662183985257)
    ·
      refine ⟨1020643233902746637988943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1360857645203662183985257 1020643233902746637988943)
      ·
        refine ⟨1530964850854119956983415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020643233902746637988943 1530964850854119956983415)
        ·
          refine ⟨2296447276281179935475123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530964850854119956983415 2296447276281179935475123)
          ·
            refine ⟨3444670914421769903212685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296447276281179935475123 3444670914421769903212685)
            ·
              refine ⟨1291751592908163713704757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3444670914421769903212685 1291751592908163713704757)
              ·
                refine ⟨121101711835140348159821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1291751592908163713704757 121101711835140348159821)
                ·
                  refine ⟨45413141938177630559933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121101711835140348159821 45413141938177630559933)
                  ·
                    rfl

theorem cell21_198994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_198994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_198994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_198994 prefixEnd_198994 := by exact prefixLift 198994
  have htrace : WordTrace (prefixWord ++ tailWord_198994) baseStart_198994 baseEnd_198994 := by
    simpa [prefixWord, tailWord_198994, baseEnd_198994] using wordTrace_append hprefix tailTrace_198994
  have hstable : (prefixWord ++ tailWord_198994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198994).length < 2 ^ (prefixWord ++ tailWord_198994).sum := by decide
  have hdescent : baseEnd_198994 < baseStart_198994 := by decide
  rcases family_descends (prefixWord ++ tailWord_198994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199008 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 6]
def baseStart_199008 : Nat := 118140960795 + 199008 * 2 ^ 59
def prefixEnd_199008 : Nat := 4983230072969 + 3 ^ 40 * 199008 * 2
def baseEnd_199008 : Nat := 45416336928916717326571

theorem tailTrace_199008 : CollatzResearch.WordTrace tailWord_199008 prefixEnd_199008 45416336928916717326571 := by
  unfold tailWord_199008
  simp only [CollatzResearch.WordTrace]
  refine ⟨3629209031517739352798839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4838945375356985803731785 3629209031517739352798839)
  ·
    refine ⟨5443813547276609029198259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3629209031517739352798839 5443813547276609029198259)
    ·
      refine ⟨8165720320914913543797389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5443813547276609029198259 8165720320914913543797389)
      ·
        refine ⟨3062145120343092578924021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8165720320914913543797389 3062145120343092578924021)
        ·
          refine ⟨287076105032164929274127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3062145120343092578924021 287076105032164929274127)
          ·
            refine ⟨430614157548247393911191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287076105032164929274127 430614157548247393911191)
            ·
              refine ⟨645921236322371090866787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430614157548247393911191 645921236322371090866787)
              ·
                refine ⟨968881854483556636300181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645921236322371090866787 968881854483556636300181)
                ·
                  refine ⟨45416336928916717326571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 968881854483556636300181 45416336928916717326571)
                  ·
                    rfl

theorem cell21_199008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_199008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199008 prefixEnd_199008 := by exact prefixLift 199008
  have htrace : WordTrace (prefixWord ++ tailWord_199008) baseStart_199008 baseEnd_199008 := by
    simpa [prefixWord, tailWord_199008, baseEnd_199008] using wordTrace_append hprefix tailTrace_199008
  have hstable : (prefixWord ++ tailWord_199008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199008).length < 2 ^ (prefixWord ++ tailWord_199008).sum := by decide
  have hdescent : baseEnd_199008 < baseStart_199008 := by decide
  rcases family_descends (prefixWord ++ tailWord_199008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199036 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 7]
def baseStart_199036 : Nat := 118140960795 + 199036 * 2 ^ 59
def prefixEnd_199036 : Nat := 4983230072969 + 3 ^ 40 * 199036 * 2
def baseEnd_199036 : Nat := 45422726910394890859847

theorem tailTrace_199036 : CollatzResearch.WordTrace tailWord_199036 prefixEnd_199036 45422726910394890859847 := by
  unfold tailWord_199036
  simp only [CollatzResearch.WordTrace]
  refine ⟨3629719653467019743808481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4839626204622692991744641 3629719653467019743808481)
  ·
    refine ⟨2722289740100264807856361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3629719653467019743808481 2722289740100264807856361)
    ·
      refine ⟨2041717305075198605892271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2722289740100264807856361 2041717305075198605892271)
      ·
        refine ⟨3062575957612797908838407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2041717305075198605892271 3062575957612797908838407)
        ·
          refine ⟨4593863936419196863257611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3062575957612797908838407 4593863936419196863257611)
          ·
            refine ⟨6890795904628795294886417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4593863936419196863257611 6890795904628795294886417)
            ·
              refine ⟨5168096928471596471164813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6890795904628795294886417 5168096928471596471164813)
              ·
                refine ⟨1938036348176848676686805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5168096928471596471164813 1938036348176848676686805)
                ·
                  refine ⟨45422726910394890859847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1938036348176848676686805 45422726910394890859847)
                  ·
                    rfl

theorem cell21_199036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_199036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199036 prefixEnd_199036 := by exact prefixLift 199036
  have htrace : WordTrace (prefixWord ++ tailWord_199036) baseStart_199036 baseEnd_199036 := by
    simpa [prefixWord, tailWord_199036, baseEnd_199036] using wordTrace_append hprefix tailTrace_199036
  have hstable : (prefixWord ++ tailWord_199036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199036).length < 2 ^ (prefixWord ++ tailWord_199036).sum := by decide
  have hdescent : baseEnd_199036 < baseStart_199036 := by decide
  rcases family_descends (prefixWord ++ tailWord_199036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199062 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_199062 : Nat := 118140960795 + 199062 * 2 ^ 59
def prefixEnd_199062 : Nat := 4983230072969 + 3 ^ 40 * 199062 * 2
def baseEnd_199062 : Nat := 45428660464624623426461

theorem tailTrace_199062 : CollatzResearch.WordTrace tailWord_199062 prefixEnd_199062 45428660464624623426461 := by
  unfold tailWord_199062
  simp only [CollatzResearch.WordTrace]
  refine ⟨453774225302490370503965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4840258403226563952042293 453774225302490370503965)
  ·
    refine ⟨170165334488433888938987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 453774225302490370503965 170165334488433888938987)
    ·
      refine ⟨255248001732650833408481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170165334488433888938987 255248001732650833408481)
      ·
        refine ⟨191436001299488125056361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255248001732650833408481 191436001299488125056361)
        ·
          refine ⟨143577000974616093792271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191436001299488125056361 143577000974616093792271)
          ·
            refine ⟨215365501461924140688407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143577000974616093792271 215365501461924140688407)
            ·
              refine ⟨323048252192886211032611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215365501461924140688407 323048252192886211032611)
              ·
                refine ⟨484572378289329316548917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323048252192886211032611 484572378289329316548917)
                ·
                  refine ⟨45428660464624623426461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 484572378289329316548917 45428660464624623426461)
                  ·
                    rfl

theorem cell21_199062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_199062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199062 prefixEnd_199062 := by exact prefixLift 199062
  have htrace : WordTrace (prefixWord ++ tailWord_199062) baseStart_199062 baseEnd_199062 := by
    simpa [prefixWord, tailWord_199062, baseEnd_199062] using wordTrace_append hprefix tailTrace_199062
  have hstable : (prefixWord ++ tailWord_199062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199062).length < 2 ^ (prefixWord ++ tailWord_199062).sum := by decide
  have hdescent : baseEnd_199062 < baseStart_199062 := by decide
  rcases family_descends (prefixWord ++ tailWord_199062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199208 : List Nat := [2, 1, 5, 2, 1, 3, 2, 5]
def baseStart_199208 : Nat := 118140960795 + 199208 * 2 ^ 59
def prefixEnd_199208 : Nat := 4983230072969 + 3 ^ 40 * 199208 * 2
def baseEnd_199208 : Nat := 15153993217920271330943

theorem tailTrace_199208 : CollatzResearch.WordTrace tailWord_199208 prefixEnd_199208 15153993217920271330943 := by
  unfold tailWord_199208
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632856331155456431439139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4843808441540608575252185 3632856331155456431439139)
  ·
    refine ⟨5449284496733184647158709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3632856331155456431439139 5449284496733184647158709)
    ·
      refine ⟨510870421568736060671129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5449284496733184647158709 510870421568736060671129)
      ·
        refine ⟨383152816176552045503347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510870421568736060671129 383152816176552045503347)
        ·
          refine ⟨574729224264828068255021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383152816176552045503347 574729224264828068255021)
          ·
            refine ⟨215523459099310525595633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 574729224264828068255021 215523459099310525595633)
            ·
              refine ⟨161642594324482894196725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215523459099310525595633 161642594324482894196725)
              ·
                refine ⟨15153993217920271330943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161642594324482894196725 15153993217920271330943)
                ·
                  rfl

theorem cell21_199208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 5].length) (baseStart_199208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199208 prefixEnd_199208 := by exact prefixLift 199208
  have htrace : WordTrace (prefixWord ++ tailWord_199208) baseStart_199208 baseEnd_199208 := by
    simpa [prefixWord, tailWord_199208, baseEnd_199208] using wordTrace_append hprefix tailTrace_199208
  have hstable : (prefixWord ++ tailWord_199208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199208).length < 2 ^ (prefixWord ++ tailWord_199208).sum := by decide
  have hdescent : baseEnd_199208 < baseStart_199208 := by decide
  rcases family_descends (prefixWord ++ tailWord_199208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199239 : List Nat := [1, 1, 4, 1, 4, 2, 3, 2, 3]
def baseStart_199239 : Nat := 118140960795 + 199239 * 2 ^ 59
def prefixEnd_199239 : Nat := 4983230072969 + 3 ^ 40 * 199239 * 2
def baseEnd_199239 : Nat := 45469054276111648976099

theorem tailTrace_199239 : CollatzResearch.WordTrace tailWord_199239 prefixEnd_199239 45469054276111648976099 := by
  unfold tailWord_199239
  simp only [CollatzResearch.WordTrace]
  refine ⟨7266843325198605157256771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4844562216799070104837847 7266843325198605157256771)
  ·
    refine ⟨10900264987797907735885157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7266843325198605157256771 10900264987797907735885157)
    ·
      refine ⟨2043799685212107700478467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10900264987797907735885157 2043799685212107700478467)
      ·
        refine ⟨3065699527818161550717701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2043799685212107700478467 3065699527818161550717701)
        ·
          refine ⟨574818661465905290759569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3065699527818161550717701 574818661465905290759569)
          ·
            refine ⟨431113996099428968069677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574818661465905290759569 431113996099428968069677)
            ·
              refine ⟨161667748537285863026129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431113996099428968069677 161667748537285863026129)
              ·
                refine ⟨121250811402964397269597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161667748537285863026129 121250811402964397269597)
                ·
                  refine ⟨45469054276111648976099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121250811402964397269597 45469054276111648976099)
                  ·
                    rfl

theorem cell21_199239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 3].length) (baseStart_199239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199239 prefixEnd_199239 := by exact prefixLift 199239
  have htrace : WordTrace (prefixWord ++ tailWord_199239) baseStart_199239 baseEnd_199239 := by
    simpa [prefixWord, tailWord_199239, baseEnd_199239] using wordTrace_append hprefix tailTrace_199239
  have hstable : (prefixWord ++ tailWord_199239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199239).length < 2 ^ (prefixWord ++ tailWord_199239).sum := by decide
  have hdescent : baseEnd_199239 < baseStart_199239 := by decide
  rcases family_descends (prefixWord ++ tailWord_199239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199250 : List Nat := [3, 2, 2, 1, 2, 1, 4, 6]
def baseStart_199250 : Nat := 118140960795 + 199250 * 2 ^ 59
def prefixEnd_199250 : Nat := 4983230072969 + 3 ^ 40 * 199250 * 2
def baseEnd_199250 : Nat := 15157188208659358097581

theorem tailTrace_199250 : CollatzResearch.WordTrace tailWord_199250 prefixEnd_199250 15157188208659358097581 := by
  unfold tailWord_199250
  simp only [CollatzResearch.WordTrace]
  refine ⟨1816811132039688508976801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4844829685439169357271469 1816811132039688508976801)
  ·
    refine ⟨1362608349029766381732601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1816811132039688508976801 1362608349029766381732601)
    ·
      refine ⟨1021956261772324786299451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1362608349029766381732601 1021956261772324786299451)
      ·
        refine ⟨1532934392658487179449177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1021956261772324786299451 1532934392658487179449177)
        ·
          refine ⟨1149700794493865384586883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1532934392658487179449177 1149700794493865384586883)
          ·
            refine ⟨1724551191740798076880325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149700794493865384586883 1724551191740798076880325)
            ·
              refine ⟨323353348451399639415061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1724551191740798076880325 323353348451399639415061)
              ·
                refine ⟨15157188208659358097581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 323353348451399639415061 15157188208659358097581)
                ·
                  rfl

theorem cell21_199250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_199250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199250 prefixEnd_199250 := by exact prefixLift 199250
  have htrace : WordTrace (prefixWord ++ tailWord_199250) baseStart_199250 baseEnd_199250 := by
    simpa [prefixWord, tailWord_199250, baseEnd_199250] using wordTrace_append hprefix tailTrace_199250
  have hstable : (prefixWord ++ tailWord_199250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199250).length < 2 ^ (prefixWord ++ tailWord_199250).sum := by decide
  have hdescent : baseEnd_199250 < baseStart_199250 := by decide
  rcases family_descends (prefixWord ++ tailWord_199250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199264 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 5]
def baseStart_199264 : Nat := 118140960795 + 199264 * 2 ^ 59
def prefixEnd_199264 : Nat := 4983230072969 + 3 ^ 40 * 199264 * 2
def baseEnd_199264 : Nat := 45474759616717161059381

theorem tailTrace_199264 : CollatzResearch.WordTrace tailWord_199264 prefixEnd_199264 45474759616717161059381 := by
  unfold tailWord_199264
  simp only [CollatzResearch.WordTrace]
  refine ⟨3633877575054017213458423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4845170100072022951277897 3633877575054017213458423)
  ·
    refine ⟨5450816362581025820187635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3633877575054017213458423 5450816362581025820187635)
    ·
      refine ⟨8176224543871538730281453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5450816362581025820187635 8176224543871538730281453)
      ·
        refine ⟨3066084203951827023855545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8176224543871538730281453 3066084203951827023855545)
        ·
          refine ⟨2299563152963870267891659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3066084203951827023855545 2299563152963870267891659)
          ·
            refine ⟨3449344729445805401837489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2299563152963870267891659 3449344729445805401837489)
            ·
              refine ⟨2587008547084354051378117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3449344729445805401837489 2587008547084354051378117)
              ·
                refine ⟨485064102578316384633397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2587008547084354051378117 485064102578316384633397)
                ·
                  refine ⟨45474759616717161059381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 485064102578316384633397 45474759616717161059381)
                  ·
                    rfl

theorem cell21_199264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_199264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199264 prefixEnd_199264 := by exact prefixLift 199264
  have htrace : WordTrace (prefixWord ++ tailWord_199264) baseStart_199264 baseEnd_199264 := by
    simpa [prefixWord, tailWord_199264, baseEnd_199264] using wordTrace_append hprefix tailTrace_199264
  have hstable : (prefixWord ++ tailWord_199264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199264).length < 2 ^ (prefixWord ++ tailWord_199264).sum := by decide
  have hdescent : baseEnd_199264 < baseStart_199264 := by decide
  rcases family_descends (prefixWord ++ tailWord_199264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199357 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 5]
def baseStart_199357 : Nat := 118140960795 + 199357 * 2 ^ 59
def prefixEnd_199357 : Nat := 4983230072969 + 3 ^ 40 * 199357 * 2
def baseEnd_199357 : Nat := 45495983483769666009191

theorem tailTrace_199357 : CollatzResearch.WordTrace tailWord_199357 prefixEnd_199357 45495983483769666009191 := by
  unfold tailWord_199357
  simp only [CollatzResearch.WordTrace]
  refine ⟨7271147138771111310052325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4847431425847407540034883 7271147138771111310052325)
  ·
    refine ⟨1363340088519583370634811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7271147138771111310052325 1363340088519583370634811)
    ·
      refine ⟨2045010132779375055952217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1363340088519583370634811 2045010132779375055952217)
      ·
        refine ⟨1533757599584531291964163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2045010132779375055952217 1533757599584531291964163)
        ·
          refine ⟨2300636399376796937946245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533757599584531291964163 2300636399376796937946245)
          ·
            refine ⟨431369324883149425864921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2300636399376796937946245 431369324883149425864921)
            ·
              refine ⟨323526993662362069398691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431369324883149425864921 323526993662362069398691)
              ·
                refine ⟨485290490493543104098037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323526993662362069398691 485290490493543104098037)
                ·
                  refine ⟨45495983483769666009191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 485290490493543104098037 45495983483769666009191)
                  ·
                    rfl

theorem cell21_199357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_199357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199357 prefixEnd_199357 := by exact prefixLift 199357
  have htrace : WordTrace (prefixWord ++ tailWord_199357) baseStart_199357 baseEnd_199357 := by
    simpa [prefixWord, tailWord_199357, baseEnd_199357] using wordTrace_append hprefix tailTrace_199357
  have hstable : (prefixWord ++ tailWord_199357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199357).length < 2 ^ (prefixWord ++ tailWord_199357).sum := by decide
  have hdescent : baseEnd_199357 < baseStart_199357 := by decide
  rcases family_descends (prefixWord ++ tailWord_199357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199385 : List Nat := [1, 2, 1, 2, 3, 2, 3, 7]
def baseStart_199385 : Nat := 118140960795 + 199385 * 2 ^ 59
def prefixEnd_199385 : Nat := 4983230072969 + 3 ^ 40 * 199385 * 2
def baseEnd_199385 : Nat := 15167457821749279847489

theorem tailTrace_199385 : CollatzResearch.WordTrace tailWord_199385 prefixEnd_199385 15167457821749279847489 := by
  unfold tailWord_199385
  simp only [CollatzResearch.WordTrace]
  refine ⟨7272168382669672092071609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4848112255113114728047739 7272168382669672092071609)
  ·
    refine ⟨5454126287002254069053707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7272168382669672092071609 5454126287002254069053707)
    ·
      refine ⟨8181189430503381103580561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5454126287002254069053707 8181189430503381103580561)
      ·
        refine ⟨6135892072877535827685421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8181189430503381103580561 6135892072877535827685421)
        ·
          refine ⟨2300959527329075935382033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6135892072877535827685421 2300959527329075935382033)
          ·
            refine ⟨1725719645496806951536525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2300959527329075935382033 1725719645496806951536525)
            ·
              refine ⟨647144867061302606826197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1725719645496806951536525 647144867061302606826197)
              ·
                refine ⟨15167457821749279847489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 647144867061302606826197 15167457821749279847489)
                ·
                  rfl

theorem cell21_199385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 7].length) (baseStart_199385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199385 prefixEnd_199385 := by exact prefixLift 199385
  have htrace : WordTrace (prefixWord ++ tailWord_199385) baseStart_199385 baseEnd_199385 := by
    simpa [prefixWord, tailWord_199385, baseEnd_199385] using wordTrace_append hprefix tailTrace_199385
  have hstable : (prefixWord ++ tailWord_199385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199385).length < 2 ^ (prefixWord ++ tailWord_199385).sum := by decide
  have hdescent : baseEnd_199385 < baseStart_199385 := by decide
  rcases family_descends (prefixWord ++ tailWord_199385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199388 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 6]
def baseStart_199388 : Nat := 118140960795 + 199388 * 2 ^ 59
def prefixEnd_199388 : Nat := 4983230072969 + 3 ^ 40 * 199388 * 2
def baseEnd_199388 : Nat := 45503058106120500992461

theorem tailTrace_199388 : CollatzResearch.WordTrace tailWord_199388 prefixEnd_199388 45503058106120500992461 := by
  unfold tailWord_199388
  simp only [CollatzResearch.WordTrace]
  refine ⟨3636138900829401802215409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4848185201105869069620545 3636138900829401802215409)
  ·
    refine ⟨2727104175622051351661557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3636138900829401802215409 2727104175622051351661557)
    ·
      refine ⟨255666016464567314218271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2727104175622051351661557 255666016464567314218271)
      ·
        refine ⟨383499024696850971327407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255666016464567314218271 383499024696850971327407)
        ·
          refine ⟨575248537045276456991111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383499024696850971327407 575248537045276456991111)
          ·
            refine ⟨862872805567914685486667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575248537045276456991111 862872805567914685486667)
            ·
              refine ⟨1294309208351872028230001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862872805567914685486667 1294309208351872028230001)
              ·
                refine ⟨970731906263904021172501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1294309208351872028230001 970731906263904021172501)
                ·
                  refine ⟨45503058106120500992461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 970731906263904021172501 45503058106120500992461)
                  ·
                    rfl

theorem cell21_199388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_199388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199388 prefixEnd_199388 := by exact prefixLift 199388
  have htrace : WordTrace (prefixWord ++ tailWord_199388) baseStart_199388 baseEnd_199388 := by
    simpa [prefixWord, tailWord_199388, baseEnd_199388] using wordTrace_append hprefix tailTrace_199388
  have hstable : (prefixWord ++ tailWord_199388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199388).length < 2 ^ (prefixWord ++ tailWord_199388).sum := by decide
  have hdescent : baseEnd_199388 < baseStart_199388 := by decide
  rcases family_descends (prefixWord ++ tailWord_199388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199422 : List Nat := [4, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_199422 : Nat := 118140960795 + 199422 * 2 ^ 59
def prefixEnd_199422 : Nat := 4983230072969 + 3 ^ 40 * 199422 * 2
def baseEnd_199422 : Nat := 45510817369343997425725

theorem tailTrace_199422 : CollatzResearch.WordTrace tailWord_199422 prefixEnd_199422 45510817369343997425725 := by
  unfold tailWord_199422
  simp only [CollatzResearch.WordTrace]
  refine ⟨909189735441953426396065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4849011922357084940779013 909189735441953426396065)
  ·
    refine ⟨681892301581465069797049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 909189735441953426396065 681892301581465069797049)
    ·
      refine ⟨511419226186098802347787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 681892301581465069797049 511419226186098802347787)
      ·
        refine ⟨767128839279148203521681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511419226186098802347787 767128839279148203521681)
        ·
          refine ⟨575346629459361152641261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 767128839279148203521681 575346629459361152641261)
          ·
            refine ⟨215754986047260432240473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 575346629459361152641261 215754986047260432240473)
            ·
              refine ⟨161816239535445324180355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215754986047260432240473 161816239535445324180355)
              ·
                refine ⟨242724359303167986270533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161816239535445324180355 242724359303167986270533)
                ·
                  refine ⟨45510817369343997425725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242724359303167986270533 45510817369343997425725)
                  ·
                    rfl

theorem cell21_199422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_199422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199422 prefixEnd_199422 := by exact prefixLift 199422
  have htrace : WordTrace (prefixWord ++ tailWord_199422) baseStart_199422 baseEnd_199422 := by
    simpa [prefixWord, tailWord_199422, baseEnd_199422] using wordTrace_append hprefix tailTrace_199422
  have hstable : (prefixWord ++ tailWord_199422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199422).length < 2 ^ (prefixWord ++ tailWord_199422).sum := by decide
  have hdescent : baseEnd_199422 < baseStart_199422 := by decide
  rcases family_descends (prefixWord ++ tailWord_199422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199464 : List Nat := [2, 1, 5, 1, 1, 1, 4, 2, 4]
def baseStart_199464 : Nat := 118140960795 + 199464 * 2 ^ 59
def prefixEnd_199464 : Nat := 4983230072969 + 3 ^ 40 * 199464 * 2
def baseEnd_199464 : Nat := 45520402341561257725639

theorem tailTrace_199464 : CollatzResearch.WordTrace tailWord_199464 prefixEnd_199464 45520402341561257725639 := by
  unfold tailWord_199464
  simp only [CollatzResearch.WordTrace]
  refine ⟨3637524874691734292098723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4850033166255645722798297 3637524874691734292098723)
  ·
    refine ⟨5456287312037601438148085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3637524874691734292098723 5456287312037601438148085)
    ·
      refine ⟨511526935503525134826383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5456287312037601438148085 511526935503525134826383)
      ·
        refine ⟨767290403255287702239575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511526935503525134826383 767290403255287702239575)
        ·
          refine ⟨1150935604882931553359363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767290403255287702239575 1150935604882931553359363)
          ·
            refine ⟨1726403407324397330039045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150935604882931553359363 1726403407324397330039045)
            ·
              refine ⟨323700638873324499382321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1726403407324397330039045 323700638873324499382321)
              ·
                refine ⟨242775479154993374536741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323700638873324499382321 242775479154993374536741)
                ·
                  refine ⟨45520402341561257725639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242775479154993374536741 45520402341561257725639)
                  ·
                    rfl

theorem cell21_199464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_199464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199464 prefixEnd_199464 := by exact prefixLift 199464
  have htrace : WordTrace (prefixWord ++ tailWord_199464) baseStart_199464 baseEnd_199464 := by
    simpa [prefixWord, tailWord_199464, baseEnd_199464] using wordTrace_append hprefix tailTrace_199464
  have hstable : (prefixWord ++ tailWord_199464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199464).length < 2 ^ (prefixWord ++ tailWord_199464).sum := by decide
  have hdescent : baseEnd_199464 < baseStart_199464 := by decide
  rcases family_descends (prefixWord ++ tailWord_199464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199523 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 6]
def baseStart_199523 : Nat := 118140960795 + 199523 * 2 ^ 59
def prefixEnd_199523 : Nat := 4983230072969 + 3 ^ 40 * 199523 * 2
def baseEnd_199523 : Nat := 45533866945390266242185

theorem tailTrace_199523 : CollatzResearch.WordTrace tailWord_199523 prefixEnd_199523 45533866945390266242185 := by
  unfold tailWord_199523
  simp only [CollatzResearch.WordTrace]
  refine ⟨7277201656169721660595223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4851467770779814440396815 7277201656169721660595223)
  ·
    refine ⟨10915802484254582490892835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7277201656169721660595223 10915802484254582490892835)
    ·
      refine ⟨16373703726381873736339253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10915802484254582490892835 16373703726381873736339253)
      ·
        refine ⟨1535034724348300662781805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16373703726381873736339253 1535034724348300662781805)
        ·
          refine ⟨575638021630612748543177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1535034724348300662781805 575638021630612748543177)
          ·
            refine ⟨431728516222959561407383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575638021630612748543177 431728516222959561407383)
            ·
              refine ⟨647592774334439342111075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431728516222959561407383 647592774334439342111075)
              ·
                refine ⟨971389161501659013166613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647592774334439342111075 971389161501659013166613)
                ·
                  refine ⟨45533866945390266242185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 971389161501659013166613 45533866945390266242185)
                  ·
                    rfl

theorem cell21_199523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 6].length) (baseStart_199523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199523 prefixEnd_199523 := by exact prefixLift 199523
  have htrace : WordTrace (prefixWord ++ tailWord_199523) baseStart_199523 baseEnd_199523 := by
    simpa [prefixWord, tailWord_199523, baseEnd_199523] using wordTrace_append hprefix tailTrace_199523
  have hstable : (prefixWord ++ tailWord_199523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199523).length < 2 ^ (prefixWord ++ tailWord_199523).sum := by decide
  have hdescent : baseEnd_199523 < baseStart_199523 := by decide
  rcases family_descends (prefixWord ++ tailWord_199523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199585 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 5]
def baseStart_199585 : Nat := 118140960795 + 199585 * 2 ^ 59
def prefixEnd_199585 : Nat := 4983230072969 + 3 ^ 40 * 199585 * 2
def baseEnd_199585 : Nat := 45548016190091936208725

theorem tailTrace_199585 : CollatzResearch.WordTrace tailWord_199585 prefixEnd_199585 45548016190091936208725 := by
  unfold tailWord_199585
  simp only [CollatzResearch.WordTrace]
  refine ⟨7279462981945106249352209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4852975321296737499568139 7279462981945106249352209)
  ·
    refine ⟨5459597236458829687014157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7279462981945106249352209 5459597236458829687014157)
    ·
      refine ⟨2047348963672061132630309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5459597236458829687014157 2047348963672061132630309)
      ·
        refine ⟨383877930688511462368183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2047348963672061132630309 383877930688511462368183)
        ·
          refine ⟨575816896032767193552275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383877930688511462368183 575816896032767193552275)
          ·
            refine ⟨863725344049150790328413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575816896032767193552275 863725344049150790328413)
            ·
              refine ⟨323897004018431546373155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 863725344049150790328413 323897004018431546373155)
              ·
                refine ⟨485845506027647319559733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323897004018431546373155 485845506027647319559733)
                ·
                  refine ⟨45548016190091936208725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 485845506027647319559733 45548016190091936208725)
                  ·
                    rfl

theorem cell21_199585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_199585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199585 prefixEnd_199585 := by exact prefixLift 199585
  have htrace : WordTrace (prefixWord ++ tailWord_199585) baseStart_199585 baseEnd_199585 := by
    simpa [prefixWord, tailWord_199585, baseEnd_199585] using wordTrace_append hprefix tailTrace_199585
  have hstable : (prefixWord ++ tailWord_199585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199585).length < 2 ^ (prefixWord ++ tailWord_199585).sum := by decide
  have hdescent : baseEnd_199585 < baseStart_199585 := by decide
  rcases family_descends (prefixWord ++ tailWord_199585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199647 : List Nat := [1, 1, 2, 3, 6, 1, 1, 6]
def baseStart_199647 : Nat := 118140960795 + 199647 * 2 ^ 59
def prefixEnd_199647 : Nat := 4983230072969 + 3 ^ 40 * 199647 * 2
def baseEnd_199647 : Nat := 15187388478264535391755

theorem tailTrace_199647 : CollatzResearch.WordTrace tailWord_199647 prefixEnd_199647 15187388478264535391755 := by
  unfold tailWord_199647
  simp only [CollatzResearch.WordTrace]
  refine ⟨7281724307720490838109195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4854482871813660558739463 7281724307720490838109195)
  ·
    refine ⟨10922586461580736257163793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7281724307720490838109195 10922586461580736257163793)
    ·
      refine ⟨8191939846185552192872845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10922586461580736257163793 8191939846185552192872845)
      ·
        refine ⟨3071977442319582072327317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8191939846185552192872845 3071977442319582072327317)
        ·
          refine ⟨143998942608730409640343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3071977442319582072327317 143998942608730409640343)
          ·
            refine ⟨215998413913095614460515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143998942608730409640343 215998413913095614460515)
            ·
              refine ⟨323997620869643421690773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215998413913095614460515 323997620869643421690773)
              ·
                refine ⟨15187388478264535391755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 323997620869643421690773 15187388478264535391755)
                ·
                  rfl

theorem cell21_199647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 6].length) (baseStart_199647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199647 prefixEnd_199647 := by exact prefixLift 199647
  have htrace : WordTrace (prefixWord ++ tailWord_199647) baseStart_199647 baseEnd_199647 := by
    simpa [prefixWord, tailWord_199647, baseEnd_199647] using wordTrace_append hprefix tailTrace_199647
  have hstable : (prefixWord ++ tailWord_199647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199647).length < 2 ^ (prefixWord ++ tailWord_199647).sum := by decide
  have hdescent : baseEnd_199647 < baseStart_199647 := by decide
  rcases family_descends (prefixWord ++ tailWord_199647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199692 : List Nat := [2, 2, 1, 2, 3, 4, 1, 2, 4]
def baseStart_199692 : Nat := 118140960795 + 199692 * 2 ^ 59
def prefixEnd_199692 : Nat := 4983230072969 + 3 ^ 40 * 199692 * 2
def baseEnd_199692 : Nat := 45572435047883527925173

theorem tailTrace_199692 : CollatzResearch.WordTrace tailWord_199692 prefixEnd_199692 45572435047883527925173 := by
  unfold tailWord_199692
  simp only [CollatzResearch.WordTrace]
  refine ⟨3641682796278731761748665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4855577061704975682331553 3641682796278731761748665)
  ·
    refine ⟨2731262097209048821311499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3641682796278731761748665 2731262097209048821311499)
    ·
      refine ⟨4096893145813573231967249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2731262097209048821311499 4096893145813573231967249)
      ·
        refine ⟨3072669859360179923975437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4096893145813573231967249 3072669859360179923975437)
        ·
          refine ⟨1152251197260067471490789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3072669859360179923975437 1152251197260067471490789)
          ·
            refine ⟨216047099486262650904523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1152251197260067471490789 216047099486262650904523)
            ·
              refine ⟨324070649229393976356785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216047099486262650904523 324070649229393976356785)
              ·
                refine ⟨243052986922045482267589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324070649229393976356785 243052986922045482267589)
                ·
                  refine ⟨45572435047883527925173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243052986922045482267589 45572435047883527925173)
                  ·
                    rfl

theorem cell21_199692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_199692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199692 prefixEnd_199692 := by exact prefixLift 199692
  have htrace : WordTrace (prefixWord ++ tailWord_199692) baseStart_199692 baseEnd_199692 := by
    simpa [prefixWord, tailWord_199692, baseEnd_199692] using wordTrace_append hprefix tailTrace_199692
  have hstable : (prefixWord ++ tailWord_199692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199692).length < 2 ^ (prefixWord ++ tailWord_199692).sum := by decide
  have hdescent : baseEnd_199692 < baseStart_199692 := by decide
  rcases family_descends (prefixWord ++ tailWord_199692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199709 : List Nat := [1, 4, 2, 2, 3, 1, 3, 1, 4]
def baseStart_199709 : Nat := 118140960795 + 199709 * 2 ^ 59
def prefixEnd_199709 : Nat := 4983230072969 + 3 ^ 40 * 199709 * 2
def baseEnd_199709 : Nat := 45576314679495276141805

theorem tailTrace_199709 : CollatzResearch.WordTrace tailWord_199709 prefixEnd_199709 45576314679495276141805 := by
  unfold tailWord_199709
  simp only [CollatzResearch.WordTrace]
  refine ⟨7283985633495875426866181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4855990422330583617910787 7283985633495875426866181)
  ·
    refine ⟨1365747306280476642537409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7283985633495875426866181 1365747306280476642537409)
    ·
      refine ⟨1024310479710357481903057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1365747306280476642537409 1024310479710357481903057)
      ·
        refine ⟨768232859782768111427293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1024310479710357481903057 768232859782768111427293)
        ·
          refine ⟨288087322418538041785235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 768232859782768111427293 288087322418538041785235)
          ·
            refine ⟨432130983627807062677853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288087322418538041785235 432130983627807062677853)
            ·
              refine ⟨162049118860427648504195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 432130983627807062677853 162049118860427648504195)
              ·
                refine ⟨243073678290641472756293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162049118860427648504195 243073678290641472756293)
                ·
                  refine ⟨45576314679495276141805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243073678290641472756293 45576314679495276141805)
                  ·
                    rfl

theorem cell21_199709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_199709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199709 prefixEnd_199709 := by exact prefixLift 199709
  have htrace : WordTrace (prefixWord ++ tailWord_199709) baseStart_199709 baseEnd_199709 := by
    simpa [prefixWord, tailWord_199709, baseEnd_199709] using wordTrace_append hprefix tailTrace_199709
  have hstable : (prefixWord ++ tailWord_199709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199709).length < 2 ^ (prefixWord ++ tailWord_199709).sum := by decide
  have hdescent : baseEnd_199709 < baseStart_199709 := by decide
  rcases family_descends (prefixWord ++ tailWord_199709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199765 : List Nat := [1, 3, 2, 2, 1, 2, 4, 6]
def baseStart_199765 : Nat := 118140960795 + 199765 * 2 ^ 59
def prefixEnd_199765 : Nat := 4983230072969 + 3 ^ 40 * 199765 * 2
def baseEnd_199765 : Nat := 15196364880817207736119

theorem tailTrace_199765 : CollatzResearch.WordTrace tailWord_199765 prefixEnd_199765 15196364880817207736119 := by
  unfold tailWord_199765
  simp only [CollatzResearch.WordTrace]
  refine ⟨7286028121292996990904749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4857352080861997993936499 7286028121292996990904749)
  ·
    refine ⟨2732260545484873871589281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7286028121292996990904749 2732260545484873871589281)
    ·
      refine ⟨2049195409113655403691961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2732260545484873871589281 2049195409113655403691961)
      ·
        refine ⟨1536896556835241552768971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2049195409113655403691961 1536896556835241552768971)
        ·
          refine ⟨2305344835252862329153457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1536896556835241552768971 2305344835252862329153457)
          ·
            refine ⟨1729008626439646746865093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2305344835252862329153457 1729008626439646746865093)
            ·
              refine ⟨324189117457433765037205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1729008626439646746865093 324189117457433765037205)
              ·
                refine ⟨15196364880817207736119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 324189117457433765037205 15196364880817207736119)
                ·
                  rfl

theorem cell21_199765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 6].length) (baseStart_199765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199765 prefixEnd_199765 := by exact prefixLift 199765
  have htrace : WordTrace (prefixWord ++ tailWord_199765) baseStart_199765 baseEnd_199765 := by
    simpa [prefixWord, tailWord_199765, baseEnd_199765] using wordTrace_append hprefix tailTrace_199765
  have hstable : (prefixWord ++ tailWord_199765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199765).length < 2 ^ (prefixWord ++ tailWord_199765).sum := by decide
  have hdescent : baseEnd_199765 < baseStart_199765 := by decide
  rcases family_descends (prefixWord ++ tailWord_199765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199779 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 7]
def baseStart_199779 : Nat := 118140960795 + 199779 * 2 ^ 59
def prefixEnd_199779 : Nat := 4983230072969 + 3 ^ 40 * 199779 * 2
def baseEnd_199779 : Nat := 45592289633190709974995

theorem tailTrace_199779 : CollatzResearch.WordTrace tailWord_199779 prefixEnd_199779 45592289633190709974995 := by
  unfold tailWord_199779
  simp only [CollatzResearch.WordTrace]
  refine ⟨7286538743242277381914391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4857692495494851587942927 7286538743242277381914391)
  ·
    refine ⟨10929808114863416072871587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7286538743242277381914391 10929808114863416072871587)
    ·
      refine ⟨16394712172295124109307381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10929808114863416072871587 16394712172295124109307381)
      ·
        refine ⟨1537004266152667885247567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16394712172295124109307381 1537004266152667885247567)
        ·
          refine ⟨2305506399229001827871351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537004266152667885247567 2305506399229001827871351)
          ·
            refine ⟨3458259598843502741807027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305506399229001827871351 3458259598843502741807027)
            ·
              refine ⟨5187389398265254112710541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3458259598843502741807027 5187389398265254112710541)
              ·
                refine ⟨1945271024349470292266453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5187389398265254112710541 1945271024349470292266453)
                ·
                  refine ⟨45592289633190709974995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1945271024349470292266453 45592289633190709974995)
                  ·
                    rfl

theorem cell21_199779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 7].length) (baseStart_199779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199779 prefixEnd_199779 := by exact prefixLift 199779
  have htrace : WordTrace (prefixWord ++ tailWord_199779) baseStart_199779 baseEnd_199779 := by
    simpa [prefixWord, tailWord_199779, baseEnd_199779] using wordTrace_append hprefix tailTrace_199779
  have hstable : (prefixWord ++ tailWord_199779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199779).length < 2 ^ (prefixWord ++ tailWord_199779).sum := by decide
  have hdescent : baseEnd_199779 < baseStart_199779 := by decide
  rcases family_descends (prefixWord ++ tailWord_199779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199824 : List Nat := [2, 1, 1, 1, 1, 1, 4, 10]
def baseStart_199824 : Nat := 118140960795 + 199824 * 2 ^ 59
def prefixEnd_199824 : Nat := 4983230072969 + 3 ^ 40 * 199824 * 2
def baseEnd_199824 : Nat := 15200853082093543908301

theorem tailTrace_199824 : CollatzResearch.WordTrace tailWord_199824 prefixEnd_199824 15200853082093543908301 := by
  unfold tailWord_199824
  simp only [CollatzResearch.WordTrace]
  refine ⟨3644090014039625033651263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4858786685386166711535017 3644090014039625033651263)
  ·
    refine ⟨5466135021059437550476895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3644090014039625033651263 5466135021059437550476895)
    ·
      refine ⟨8199202531589156325715343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5466135021059437550476895 8199202531589156325715343)
      ·
        refine ⟨12298803797383734488573015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8199202531589156325715343 12298803797383734488573015)
        ·
          refine ⟨18448205696075601732859523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12298803797383734488573015 18448205696075601732859523)
          ·
            refine ⟨27672308544113402599289285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18448205696075601732859523 27672308544113402599289285)
            ·
              refine ⟨5188557852021262987366741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27672308544113402599289285 5188557852021262987366741)
              ·
                refine ⟨15200853082093543908301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5188557852021262987366741 15200853082093543908301)
                ·
                  rfl

theorem cell21_199824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 10].length) (baseStart_199824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199824 prefixEnd_199824 := by exact prefixLift 199824
  have htrace : WordTrace (prefixWord ++ tailWord_199824) baseStart_199824 baseEnd_199824 := by
    simpa [prefixWord, tailWord_199824, baseEnd_199824] using wordTrace_append hprefix tailTrace_199824
  have hstable : (prefixWord ++ tailWord_199824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199824).length < 2 ^ (prefixWord ++ tailWord_199824).sum := by decide
  have hdescent : baseEnd_199824 < baseStart_199824 := by decide
  rcases family_descends (prefixWord ++ tailWord_199824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199892 : List Nat := [2, 4, 1, 4, 1, 2, 2, 5]
def baseStart_199892 : Nat := 118140960795 + 199892 * 2 ^ 59
def prefixEnd_199892 : Nat := 4983230072969 + 3 ^ 40 * 199892 * 2
def baseEnd_199892 : Nat := 15206025924242541530477

theorem tailTrace_199892 : CollatzResearch.WordTrace tailWord_199892 prefixEnd_199892 15206025924242541530477 := by
  unfold tailWord_199892
  simp only [CollatzResearch.WordTrace]
  refine ⟨3645330095916448840388965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4860440127888598453851953 3645330095916448840388965)
  ·
    refine ⟨683499392984334157572931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3645330095916448840388965 683499392984334157572931)
    ·
      refine ⟨1025249089476501236359397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 683499392984334157572931 1025249089476501236359397)
      ·
        refine ⟨192234204276843981817387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1025249089476501236359397 192234204276843981817387)
        ·
          refine ⟨288351306415265972726081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192234204276843981817387 288351306415265972726081)
          ·
            refine ⟨216263479811449479544561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288351306415265972726081 216263479811449479544561)
            ·
              refine ⟨162197609858587109658421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216263479811449479544561 162197609858587109658421)
              ·
                refine ⟨15206025924242541530477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162197609858587109658421 15206025924242541530477)
                ·
                  rfl

theorem cell21_199892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 5].length) (baseStart_199892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199892 prefixEnd_199892 := by exact prefixLift 199892
  have htrace : WordTrace (prefixWord ++ tailWord_199892) baseStart_199892 baseEnd_199892 := by
    simpa [prefixWord, tailWord_199892, baseEnd_199892] using wordTrace_append hprefix tailTrace_199892
  have hstable : (prefixWord ++ tailWord_199892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199892).length < 2 ^ (prefixWord ++ tailWord_199892).sum := by decide
  have hdescent : baseEnd_199892 < baseStart_199892 := by decide
  rcases family_descends (prefixWord ++ tailWord_199892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199917 : List Nat := [1, 5, 1, 2, 2, 1, 9]
def baseStart_199917 : Nat := 118140960795 + 199917 * 2 ^ 59
def prefixEnd_199917 : Nat := 4983230072969 + 3 ^ 40 * 199917 * 2
def baseEnd_199917 : Nat := 5069309234814792963857

theorem tailTrace_199917 : CollatzResearch.WordTrace tailWord_199917 prefixEnd_199917 5069309234814792963857 := by
  unfold tailWord_199917
  simp only [CollatzResearch.WordTrace]
  refine ⟨7291572016742326950438005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4861048011161551300292003 7291572016742326950438005)
  ·
    refine ⟨683584876569593151603563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7291572016742326950438005 683584876569593151603563)
    ·
      refine ⟨1025377314854389727405345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 683584876569593151603563 1025377314854389727405345)
      ·
        refine ⟨769032986140792295554009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1025377314854389727405345 769032986140792295554009)
        ·
          refine ⟨576774739605594221665507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 769032986140792295554009 576774739605594221665507)
          ·
            refine ⟨865162109408391332498261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576774739605594221665507 865162109408391332498261)
            ·
              refine ⟨5069309234814792963857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 865162109408391332498261 5069309234814792963857)
              ·
                rfl

theorem cell21_199917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 9].length) (baseStart_199917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199917 prefixEnd_199917 := by exact prefixLift 199917
  have htrace : WordTrace (prefixWord ++ tailWord_199917) baseStart_199917 baseEnd_199917 := by
    simpa [prefixWord, tailWord_199917, baseEnd_199917] using wordTrace_append hprefix tailTrace_199917
  have hstable : (prefixWord ++ tailWord_199917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199917).length < 2 ^ (prefixWord ++ tailWord_199917).sum := by decide
  have hdescent : baseEnd_199917 < baseStart_199917 := by decide
  rcases family_descends (prefixWord ++ tailWord_199917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199934 : List Nat := [4, 2, 2, 1, 1, 3, 2, 6]
def baseStart_199934 : Nat := 118140960795 + 199934 * 2 ^ 59
def prefixEnd_199934 : Nat := 4983230072969 + 3 ^ 40 * 199934 * 2
def baseEnd_199934 : Nat := 15209220914981628297115

theorem tailTrace_199934 : CollatzResearch.WordTrace tailWord_199934 prefixEnd_199934 15209220914981628297115 := by
  unfold tailWord_199934
  simp only [CollatzResearch.WordTrace]
  refine ⟨911524007210092356725857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4861461371787159235871237 911524007210092356725857)
  ·
    refine ⟨683643005407569267544393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 911524007210092356725857 683643005407569267544393)
    ·
      refine ⟨512732254055676950658295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 683643005407569267544393 512732254055676950658295)
      ·
        refine ⟨769098381083515425987443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512732254055676950658295 769098381083515425987443)
        ·
          refine ⟨1153647571625273138981165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769098381083515425987443 1153647571625273138981165)
          ·
            refine ⟨432617839359477427117937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1153647571625273138981165 432617839359477427117937)
            ·
              refine ⟨324463379519608070338453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432617839359477427117937 324463379519608070338453)
              ·
                refine ⟨15209220914981628297115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 324463379519608070338453 15209220914981628297115)
                ·
                  rfl

theorem cell21_199934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_199934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_199934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_199934 prefixEnd_199934 := by exact prefixLift 199934
  have htrace : WordTrace (prefixWord ++ tailWord_199934) baseStart_199934 baseEnd_199934 := by
    simpa [prefixWord, tailWord_199934, baseEnd_199934] using wordTrace_append hprefix tailTrace_199934
  have hstable : (prefixWord ++ tailWord_199934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199934).length < 2 ^ (prefixWord ++ tailWord_199934).sum := by decide
  have hdescent : baseEnd_199934 < baseStart_199934 := by decide
  rcases family_descends (prefixWord ++ tailWord_199934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200007 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 7]
def baseStart_200007 : Nat := 118140960795 + 200007 * 2 ^ 59
def prefixEnd_200007 : Nat := 4983230072969 + 3 ^ 40 * 200007 * 2
def baseEnd_200007 : Nat := 45644322339512980174529

theorem tailTrace_200007 : CollatzResearch.WordTrace tailWord_200007 prefixEnd_200007 45644322339512980174529 := by
  unfold tailWord_200007
  simp only [CollatzResearch.WordTrace]
  refine ⟨7294854586416272321214275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4863236390944181547476183 7294854586416272321214275)
  ·
    refine ⟨10942281879624408481821413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7294854586416272321214275 10942281879624408481821413)
    ·
      refine ⟨2051677852429576590341515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10942281879624408481821413 2051677852429576590341515)
      ·
        refine ⟨3077516778644364885512273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2051677852429576590341515 3077516778644364885512273)
        ·
          refine ⟨2308137583983273664134205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3077516778644364885512273 2308137583983273664134205)
          ·
            refine ⟨865551593993727624050327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2308137583983273664134205 865551593993727624050327)
            ·
              refine ⟨1298327390990591436075491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865551593993727624050327 1298327390990591436075491)
              ·
                refine ⟨1947491086485887154113237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298327390990591436075491 1947491086485887154113237)
                ·
                  refine ⟨45644322339512980174529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1947491086485887154113237 45644322339512980174529)
                  ·
                    rfl

theorem cell21_200007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 7].length) (baseStart_200007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200007 prefixEnd_200007 := by exact prefixLift 200007
  have htrace : WordTrace (prefixWord ++ tailWord_200007) baseStart_200007 baseEnd_200007 := by
    simpa [prefixWord, tailWord_200007, baseEnd_200007] using wordTrace_append hprefix tailTrace_200007
  have hstable : (prefixWord ++ tailWord_200007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200007).length < 2 ^ (prefixWord ++ tailWord_200007).sum := by decide
  have hdescent : baseEnd_200007 < baseStart_200007 := by decide
  rcases family_descends (prefixWord ++ tailWord_200007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200055 : List Nat := [1, 1, 3, 1, 1, 2, 7, 1, 4]
def baseStart_200055 : Nat := 118140960795 + 200055 * 2 ^ 59
def prefixEnd_200055 : Nat := 4983230072969 + 3 ^ 40 * 200055 * 2
def baseEnd_200055 : Nat := 45655276593475563374431

theorem tailTrace_200055 : CollatzResearch.WordTrace tailWord_200055 prefixEnd_200055 45655276593475563374431 := by
  unfold tailWord_200055
  simp only [CollatzResearch.WordTrace]
  refine ⟨7296605290242376518961619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4864403526828251012641079 7296605290242376518961619)
  ·
    refine ⟨10944907935363564778442429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7296605290242376518961619 10944907935363564778442429)
    ·
      refine ⟨4104340475761336791915911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10944907935363564778442429 4104340475761336791915911)
      ·
        refine ⟨6156510713642005187873867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4104340475761336791915911 6156510713642005187873867)
        ·
          refine ⟨9234766070463007781810801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6156510713642005187873867 9234766070463007781810801)
          ·
            refine ⟨6926074552847255836358101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9234766070463007781810801 6926074552847255836358101)
            ·
              refine ⟨162329872332357558664643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6926074552847255836358101 162329872332357558664643)
              ·
                refine ⟨243494808498536337996965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162329872332357558664643 243494808498536337996965)
                ·
                  refine ⟨45655276593475563374431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243494808498536337996965 45655276593475563374431)
                  ·
                    rfl

theorem cell21_200055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 4].length) (baseStart_200055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200055 prefixEnd_200055 := by exact prefixLift 200055
  have htrace : WordTrace (prefixWord ++ tailWord_200055) baseStart_200055 baseEnd_200055 := by
    simpa [prefixWord, tailWord_200055, baseEnd_200055] using wordTrace_append hprefix tailTrace_200055
  have hstable : (prefixWord ++ tailWord_200055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200055).length < 2 ^ (prefixWord ++ tailWord_200055).sum := by decide
  have hdescent : baseEnd_200055 < baseStart_200055 := by decide
  rcases family_descends (prefixWord ++ tailWord_200055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200069 : List Nat := [1, 3, 1, 1, 3, 1, 6, 5]
def baseStart_200069 : Nat := 118140960795 + 200069 * 2 ^ 59
def prefixEnd_200069 : Nat := 4983230072969 + 3 ^ 40 * 200069 * 2
def baseEnd_200069 : Nat := 15219490528071550047023

theorem tailTrace_200069 : CollatzResearch.WordTrace tailWord_200069 prefixEnd_200069 15219490528071550047023 := by
  unfold tailWord_200069
  simp only [CollatzResearch.WordTrace]
  refine ⟨7297115912191656909971261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4864743941461104606647507 7297115912191656909971261)
  ·
    refine ⟨2736418467071871341239223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7297115912191656909971261 2736418467071871341239223)
    ·
      refine ⟨4104627700607807011858835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2736418467071871341239223 4104627700607807011858835)
      ·
        refine ⟨6156941550911710517788253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4104627700607807011858835 6156941550911710517788253)
        ·
          refine ⟨2308853081591891444170595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6156941550911710517788253 2308853081591891444170595)
          ·
            refine ⟨3463279622387837166255893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308853081591891444170595 3463279622387837166255893)
            ·
              refine ⟨162341232299429867168245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3463279622387837166255893 162341232299429867168245)
              ·
                refine ⟨15219490528071550047023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162341232299429867168245 15219490528071550047023)
                ·
                  rfl

theorem cell21_200069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 5].length) (baseStart_200069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200069 prefixEnd_200069 := by exact prefixLift 200069
  have htrace : WordTrace (prefixWord ++ tailWord_200069) baseStart_200069 baseEnd_200069 := by
    simpa [prefixWord, tailWord_200069, baseEnd_200069] using wordTrace_append hprefix tailTrace_200069
  have hstable : (prefixWord ++ tailWord_200069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200069).length < 2 ^ (prefixWord ++ tailWord_200069).sum := by decide
  have hdescent : baseEnd_200069 < baseStart_200069 := by decide
  rcases family_descends (prefixWord ++ tailWord_200069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200128 : List Nat := [2, 1, 1, 2, 3, 1, 4, 7]
def baseStart_200128 : Nat := 118140960795 + 200128 * 2 ^ 59
def prefixEnd_200128 : Nat := 4983230072969 + 3 ^ 40 * 200128 * 2
def baseEnd_200128 : Nat := 15223978729347886219205

theorem tailTrace_200128 : CollatzResearch.WordTrace tailWord_200128 prefixEnd_200128 15223978729347886219205 := by
  unfold tailWord_200128
  simp only [CollatzResearch.WordTrace]
  refine ⟨3649633909488954993184519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4866178545985273324246025 3649633909488954993184519)
  ·
    refine ⟨5474450864233432489776779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3649633909488954993184519 5474450864233432489776779)
    ·
      refine ⟨8211676296350148734665169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5474450864233432489776779 8211676296350148734665169)
      ·
        refine ⟨6158757222262611550998877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8211676296350148734665169 6158757222262611550998877)
        ·
          refine ⟨2309533958348479331624579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6158757222262611550998877 2309533958348479331624579)
          ·
            refine ⟨3464300937522718997436869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2309533958348479331624579 3464300937522718997436869)
            ·
              refine ⟨649556425785509812019413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3464300937522718997436869 649556425785509812019413)
              ·
                refine ⟨15223978729347886219205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 649556425785509812019413 15223978729347886219205)
                ·
                  rfl

theorem cell21_200128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 7].length) (baseStart_200128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200128 prefixEnd_200128 := by exact prefixLift 200128
  have htrace : WordTrace (prefixWord ++ tailWord_200128) baseStart_200128 baseEnd_200128 := by
    simpa [prefixWord, tailWord_200128, baseEnd_200128] using wordTrace_append hprefix tailTrace_200128
  have hstable : (prefixWord ++ tailWord_200128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200128).length < 2 ^ (prefixWord ++ tailWord_200128).sum := by decide
  have hdescent : baseEnd_200128 < baseStart_200128 := by decide
  rcases family_descends (prefixWord ++ tailWord_200128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200148 : List Nat := [2, 4, 1, 2, 3, 1, 2, 2, 4]
def baseStart_200148 : Nat := 118140960795 + 200148 * 2 ^ 59
def prefixEnd_200148 : Nat := 4983230072969 + 3 ^ 40 * 200148 * 2
def baseEnd_200148 : Nat := 45676500460528068324241

theorem tailTrace_200148 : CollatzResearch.WordTrace tailWord_200148 prefixEnd_200148 45676500460528068324241 := by
  unfold tailWord_200148
  simp only [CollatzResearch.WordTrace]
  refine ⟨3649998639452726701048549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4866664852603635601398065 3649998639452726701048549)
  ·
    refine ⟨684374744897386256446603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3649998639452726701048549 684374744897386256446603)
    ·
      refine ⟨1026562117346079384669905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 684374744897386256446603 1026562117346079384669905)
      ·
        refine ⟨769921588009559538502429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1026562117346079384669905 769921588009559538502429)
        ·
          refine ⟨288720595503584826938411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 769921588009559538502429 288720595503584826938411)
          ·
            refine ⟨433080893255377240407617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288720595503584826938411 433080893255377240407617)
            ·
              refine ⟨324810669941532930305713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433080893255377240407617 324810669941532930305713)
              ·
                refine ⟨243608002456149697729285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324810669941532930305713 243608002456149697729285)
                ·
                  refine ⟨45676500460528068324241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243608002456149697729285 45676500460528068324241)
                  ·
                    rfl

theorem cell21_200148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_200148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200148 prefixEnd_200148 := by exact prefixLift 200148
  have htrace : WordTrace (prefixWord ++ tailWord_200148) baseStart_200148 baseEnd_200148 := by
    simpa [prefixWord, tailWord_200148, baseEnd_200148] using wordTrace_append hprefix tailTrace_200148
  have hstable : (prefixWord ++ tailWord_200148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200148).length < 2 ^ (prefixWord ++ tailWord_200148).sum := by decide
  have hdescent : baseEnd_200148 < baseStart_200148 := by decide
  rcases family_descends (prefixWord ++ tailWord_200148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200159 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 5]
def baseStart_200159 : Nat := 118140960795 + 200159 * 2 ^ 59
def prefixEnd_200159 : Nat := 4983230072969 + 3 ^ 40 * 200159 * 2
def baseEnd_200159 : Nat := 45679010810394493640885

theorem tailTrace_200159 : CollatzResearch.WordTrace tailWord_200159 prefixEnd_200159 45679010810394493640885 := by
  unfold tailWord_200159
  simp only [CollatzResearch.WordTrace]
  refine ⟨7300398481865602280747531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4866932321243734853831687 7300398481865602280747531)
  ·
    refine ⟨10950597722798403421121297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7300398481865602280747531 10950597722798403421121297)
    ·
      refine ⟨8212948292098802565840973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10950597722798403421121297 8212948292098802565840973)
      ·
        refine ⟨3079855609537050962190365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8212948292098802565840973 3079855609537050962190365)
        ·
          refine ⟨1154945853576394110821387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3079855609537050962190365 1154945853576394110821387)
          ·
            refine ⟨1732418780364591166232081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154945853576394110821387 1732418780364591166232081)
            ·
              refine ⟨1299314085273443374674061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1732418780364591166232081 1299314085273443374674061)
              ·
                refine ⟨487242781977541265502773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1299314085273443374674061 487242781977541265502773)
                ·
                  refine ⟨45679010810394493640885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 487242781977541265502773 45679010810394493640885)
                  ·
                    rfl

theorem cell21_200159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 5].length) (baseStart_200159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200159 prefixEnd_200159 := by exact prefixLift 200159
  have htrace : WordTrace (prefixWord ++ tailWord_200159) baseStart_200159 baseEnd_200159 := by
    simpa [prefixWord, tailWord_200159, baseEnd_200159] using wordTrace_append hprefix tailTrace_200159
  have hstable : (prefixWord ++ tailWord_200159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200159).length < 2 ^ (prefixWord ++ tailWord_200159).sum := by decide
  have hdescent : baseEnd_200159 < baseStart_200159 := by decide
  rcases family_descends (prefixWord ++ tailWord_200159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200224 : List Nat := [2, 1, 1, 6, 1, 2, 3, 1, 4]
def baseStart_200224 : Nat := 118140960795 + 200224 * 2 ^ 59
def prefixEnd_200224 : Nat := 4983230072969 + 3 ^ 40 * 200224 * 2
def baseEnd_200224 : Nat := 45693844695968825057419

theorem tailTrace_200224 : CollatzResearch.WordTrace tailWord_200224 prefixEnd_200224 45693844695968825057419 := by
  unfold tailWord_200224
  simp only [CollatzResearch.WordTrace]
  refine ⟨3651384613315059190931863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4868512817753412254575817 3651384613315059190931863)
  ·
    refine ⟨5477076919972588786397795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3651384613315059190931863 5477076919972588786397795)
    ·
      refine ⟨8215615379958883179596693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5477076919972588786397795 8215615379958883179596693)
      ·
        refine ⟨385106970935572649043595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8215615379958883179596693 385106970935572649043595)
        ·
          refine ⟨577660456403358973565393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385106970935572649043595 577660456403358973565393)
          ·
            refine ⟨433245342302519230174045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 577660456403358973565393 433245342302519230174045)
            ·
              refine ⟨162467003363444711315267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 433245342302519230174045 162467003363444711315267)
              ·
                refine ⟨243700505045167066972901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162467003363444711315267 243700505045167066972901)
                ·
                  refine ⟨45693844695968825057419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243700505045167066972901 45693844695968825057419)
                  ·
                    rfl

theorem cell21_200224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 4].length) (baseStart_200224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200224 prefixEnd_200224 := by exact prefixLift 200224
  have htrace : WordTrace (prefixWord ++ tailWord_200224) baseStart_200224 baseEnd_200224 := by
    simpa [prefixWord, tailWord_200224, baseEnd_200224] using wordTrace_append hprefix tailTrace_200224
  have hstable : (prefixWord ++ tailWord_200224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200224).length < 2 ^ (prefixWord ++ tailWord_200224).sum := by decide
  have hdescent : baseEnd_200224 < baseStart_200224 := by decide
  rcases family_descends (prefixWord ++ tailWord_200224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200238 : List Nat := [4, 1, 3, 1, 2, 1, 4, 5]
def baseStart_200238 : Nat := 118140960795 + 200238 * 2 ^ 59
def prefixEnd_200238 : Nat := 4983230072969 + 3 ^ 40 * 200238 * 2
def baseEnd_200238 : Nat := 15232346562235970608019

theorem tailTrace_200238 : CollatzResearch.WordTrace tailWord_200238 prefixEnd_200238 15232346562235970608019 := by
  unfold tailWord_200238
  simp only [CollatzResearch.WordTrace]
  refine ⟨912909981072424846609171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4868853232386265848582245 912909981072424846609171)
  ·
    refine ⟨1369364971608637269913757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 912909981072424846609171 1369364971608637269913757)
    ·
      refine ⟨513511864353238976217659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1369364971608637269913757 513511864353238976217659)
      ·
        refine ⟨770267796529858464326489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513511864353238976217659 770267796529858464326489)
        ·
          refine ⟨577700847397393848244867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 770267796529858464326489 577700847397393848244867)
          ·
            refine ⟨866551271096090772367301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577700847397393848244867 866551271096090772367301)
            ·
              refine ⟨162478363330517019818869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 866551271096090772367301 162478363330517019818869)
              ·
                refine ⟨15232346562235970608019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162478363330517019818869 15232346562235970608019)
                ·
                  rfl

theorem cell21_200238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_200238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200238 prefixEnd_200238 := by exact prefixLift 200238
  have htrace : WordTrace (prefixWord ++ tailWord_200238) baseStart_200238 baseEnd_200238 := by
    simpa [prefixWord, tailWord_200238, baseEnd_200238] using wordTrace_append hprefix tailTrace_200238
  have hstable : (prefixWord ++ tailWord_200238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200238).length < 2 ^ (prefixWord ++ tailWord_200238).sum := by decide
  have hdescent : baseEnd_200238 < baseStart_200238 := by decide
  rcases family_descends (prefixWord ++ tailWord_200238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200266 : List Nat := [3, 1, 2, 1, 1, 3, 2, 4, 4]
def baseStart_200266 : Nat := 118140960795 + 200266 * 2 ^ 59
def prefixEnd_200266 : Nat := 4983230072969 + 3 ^ 40 * 200266 * 2
def baseEnd_200266 : Nat := 45703429668186085357333

theorem tailTrace_200266 : CollatzResearch.WordTrace tailWord_200266 prefixEnd_200266 45703429668186085357333 := by
  unfold tailWord_200266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1826075273119489888723163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4869534061651973036595101 1826075273119489888723163)
  ·
    refine ⟨2739112909679234833084745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1826075273119489888723163 2739112909679234833084745)
    ·
      refine ⟨2054334682259426124813559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2739112909679234833084745 2054334682259426124813559)
      ·
        refine ⟨3081502023389139187220339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2054334682259426124813559 3081502023389139187220339)
        ·
          refine ⟨4622253035083708780830509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3081502023389139187220339 4622253035083708780830509)
          ·
            refine ⟨1733344888156390792811441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4622253035083708780830509 1733344888156390792811441)
            ·
              refine ⟨1300008666117293094608581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1733344888156390792811441 1300008666117293094608581)
              ·
                refine ⟨243751624896992455239109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1300008666117293094608581 243751624896992455239109)
                ·
                  refine ⟨45703429668186085357333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243751624896992455239109 45703429668186085357333)
                  ·
                    rfl

theorem cell21_200266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_200266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200266 prefixEnd_200266 := by exact prefixLift 200266
  have htrace : WordTrace (prefixWord ++ tailWord_200266) baseStart_200266 baseEnd_200266 := by
    simpa [prefixWord, tailWord_200266, baseEnd_200266] using wordTrace_append hprefix tailTrace_200266
  have hstable : (prefixWord ++ tailWord_200266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200266).length < 2 ^ (prefixWord ++ tailWord_200266).sum := by decide
  have hdescent : baseEnd_200266 < baseStart_200266 := by decide
  rcases family_descends (prefixWord ++ tailWord_200266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200373 : List Nat := [1, 3, 3, 3, 2, 1, 8]
def baseStart_200373 : Nat := 118140960795 + 200373 * 2 ^ 59
def prefixEnd_200373 : Nat := 4983230072969 + 3 ^ 40 * 200373 * 2
def baseEnd_200373 : Nat := 5080872058441964119309

theorem tailTrace_200373 : CollatzResearch.WordTrace tailWord_200373 prefixEnd_200373 5080872058441964119309 := by
  unfold tailWord_200373
  simp only [CollatzResearch.WordTrace]
  refine ⟨7308203703090316829037773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4872135802060211219358515 7308203703090316829037773)
  ·
    refine ⟨2740576388658868810889165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7308203703090316829037773 2740576388658868810889165)
    ·
      refine ⟨1027716145747075804083437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2740576388658868810889165 1027716145747075804083437)
      ·
        refine ⟨385393554655153426531289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1027716145747075804083437 385393554655153426531289)
        ·
          refine ⟨289045165991365069898467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385393554655153426531289 289045165991365069898467)
          ·
            refine ⟨433567748987047604847701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289045165991365069898467 433567748987047604847701)
            ·
              refine ⟨5080872058441964119309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 433567748987047604847701 5080872058441964119309)
              ·
                rfl

theorem cell21_200373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 8].length) (baseStart_200373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200373 prefixEnd_200373 := by exact prefixLift 200373
  have htrace : WordTrace (prefixWord ++ tailWord_200373) baseStart_200373 baseEnd_200373 := by
    simpa [prefixWord, tailWord_200373, baseEnd_200373] using wordTrace_append hprefix tailTrace_200373
  have hstable : (prefixWord ++ tailWord_200373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200373).length < 2 ^ (prefixWord ++ tailWord_200373).sum := by decide
  have hdescent : baseEnd_200373 < baseStart_200373 := by decide
  rcases family_descends (prefixWord ++ tailWord_200373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200404 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 5]
def baseStart_200404 : Nat := 118140960795 + 200404 * 2 ^ 59
def prefixEnd_200404 : Nat := 4983230072969 + 3 ^ 40 * 200404 * 2
def baseEnd_200404 : Nat := 45734923148328512057051

theorem tailTrace_200404 : CollatzResearch.WordTrace tailWord_200404 prefixEnd_200404 45734923148328512057051 := by
  unfold tailWord_200404
  simp only [CollatzResearch.WordTrace]
  refine ⟨3654667182989004561708133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4872889577318672748944177 3654667182989004561708133)
  ·
    refine ⟨685250096810438355320275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3654667182989004561708133 685250096810438355320275)
    ·
      refine ⟨1027875145215657532980413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 685250096810438355320275 1027875145215657532980413)
      ·
        refine ⟨385453179455871574867655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1027875145215657532980413 385453179455871574867655)
        ·
          refine ⟨578179769183807362301483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385453179455871574867655 578179769183807362301483)
          ·
            refine ⟨867269653775711043452225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578179769183807362301483 867269653775711043452225)
            ·
              refine ⟨650452240331783282589169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 867269653775711043452225 650452240331783282589169)
              ·
                refine ⟨487839180248837461941877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650452240331783282589169 487839180248837461941877)
                ·
                  refine ⟨45734923148328512057051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 487839180248837461941877 45734923148328512057051)
                  ·
                    rfl

theorem cell21_200404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_200404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200404 prefixEnd_200404 := by exact prefixLift 200404
  have htrace : WordTrace (prefixWord ++ tailWord_200404) baseStart_200404 baseEnd_200404 := by
    simpa [prefixWord, tailWord_200404, baseEnd_200404] using wordTrace_append hprefix tailTrace_200404
  have hstable : (prefixWord ++ tailWord_200404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200404).length < 2 ^ (prefixWord ++ tailWord_200404).sum := by decide
  have hdescent : baseEnd_200404 < baseStart_200404 := by decide
  rcases family_descends (prefixWord ++ tailWord_200404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200438 : List Nat := [5, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_200438 : Nat := 118140960795 + 200438 * 2 ^ 59
def prefixEnd_200438 : Nat := 4983230072969 + 3 ^ 40 * 200438 * 2
def baseEnd_200438 : Nat := 45742682411552008490315

theorem tailTrace_200438 : CollatzResearch.WordTrace tailWord_200438 prefixEnd_200438 45742682411552008490315 := by
  unfold tailWord_200438
  simp only [CollatzResearch.WordTrace]
  refine ⟨456910902990927058134623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4873716298569888620102645 456910902990927058134623)
  ·
    refine ⟨685366354486390587201935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 456910902990927058134623 685366354486390587201935)
    ·
      refine ⟨1028049531729585880802903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 685366354486390587201935 1028049531729585880802903)
      ·
        refine ⟨1542074297594378821204355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1028049531729585880802903 1542074297594378821204355)
        ·
          refine ⟨2313111446391568231806533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542074297594378821204355 2313111446391568231806533)
          ·
            refine ⟨433708396198419043463725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2313111446391568231806533 433708396198419043463725)
            ·
              refine ⟨162640648574407141298897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 433708396198419043463725 162640648574407141298897)
              ·
                refine ⟨121980486430805355974173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162640648574407141298897 121980486430805355974173)
                ·
                  refine ⟨45742682411552008490315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121980486430805355974173 45742682411552008490315)
                  ·
                    rfl

theorem cell21_200438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_200438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200438 prefixEnd_200438 := by exact prefixLift 200438
  have htrace : WordTrace (prefixWord ++ tailWord_200438) baseStart_200438 baseEnd_200438 := by
    simpa [prefixWord, tailWord_200438, baseEnd_200438] using wordTrace_append hprefix tailTrace_200438
  have hstable : (prefixWord ++ tailWord_200438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200438).length < 2 ^ (prefixWord ++ tailWord_200438).sum := by decide
  have hdescent : baseEnd_200438 < baseStart_200438 := by decide
  rcases family_descends (prefixWord ++ tailWord_200438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200452 : List Nat := [2, 3, 2, 2, 1, 4, 2, 1, 4]
def baseStart_200452 : Nat := 118140960795 + 200452 * 2 ^ 59
def prefixEnd_200452 : Nat := 4983230072969 + 3 ^ 40 * 200452 * 2
def baseEnd_200452 : Nat := 45745877402291095256953

theorem tailTrace_200452 : CollatzResearch.WordTrace tailWord_200452 prefixEnd_200452 45745877402291095256953 := by
  unfold tailWord_200452
  simp only [CollatzResearch.WordTrace]
  refine ⟨3655542534902056660581805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4874056713202742214109073 3655542534902056660581805)
  ·
    refine ⟨1370828450588271247718177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3655542534902056660581805 1370828450588271247718177)
    ·
      refine ⟨1028121337941203435788633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1370828450588271247718177 1028121337941203435788633)
      ·
        refine ⟨771091003455902576841475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1028121337941203435788633 771091003455902576841475)
        ·
          refine ⟨1156636505183853865262213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771091003455902576841475 1156636505183853865262213)
          ·
            refine ⟨216869344721972599736665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1156636505183853865262213 216869344721972599736665)
            ·
              refine ⟨162652008541479449802499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216869344721972599736665 162652008541479449802499)
              ·
                refine ⟨243978012812219174703749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162652008541479449802499 243978012812219174703749)
                ·
                  refine ⟨45745877402291095256953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243978012812219174703749 45745877402291095256953)
                  ·
                    rfl

theorem cell21_200452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_200452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200452 prefixEnd_200452 := by exact prefixLift 200452
  have htrace : WordTrace (prefixWord ++ tailWord_200452) baseStart_200452 baseEnd_200452 := by
    simpa [prefixWord, tailWord_200452, baseEnd_200452] using wordTrace_append hprefix tailTrace_200452
  have hstable : (prefixWord ++ tailWord_200452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200452).length < 2 ^ (prefixWord ++ tailWord_200452).sum := by decide
  have hdescent : baseEnd_200452 < baseStart_200452 := by decide
  rcases family_descends (prefixWord ++ tailWord_200452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200480 : List Nat := [2, 1, 1, 5, 1, 1, 2, 5, 3]
def baseStart_200480 : Nat := 118140960795 + 200480 * 2 ^ 59
def prefixEnd_200480 : Nat := 4983230072969 + 3 ^ 40 * 200480 * 2
def baseEnd_200480 : Nat := 45752267383769268790229

theorem tailTrace_200480 : CollatzResearch.WordTrace tailWord_200480 prefixEnd_200480 45752267383769268790229 := by
  unfold tailWord_200480
  simp only [CollatzResearch.WordTrace]
  refine ⟨3656053156851337051591447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4874737542468449402121929 3656053156851337051591447)
  ·
    refine ⟨5484079735277005577387171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3656053156851337051591447 5484079735277005577387171)
    ·
      refine ⟨8226119602915508366080757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5484079735277005577387171 8226119602915508366080757)
      ·
        refine ⟨771198712773328909320071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8226119602915508366080757 771198712773328909320071)
        ·
          refine ⟨1156798069159993363980107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771198712773328909320071 1156798069159993363980107)
          ·
            refine ⟨1735197103739990045970161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156798069159993363980107 1735197103739990045970161)
            ·
              refine ⟨1301397827804992534477621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1735197103739990045970161 1301397827804992534477621)
              ·
                refine ⟨122006046356718050107277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1301397827804992534477621 122006046356718050107277)
                ·
                  refine ⟨45752267383769268790229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122006046356718050107277 45752267383769268790229)
                  ·
                    rfl

theorem cell21_200480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 3].length) (baseStart_200480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200480 prefixEnd_200480 := by exact prefixLift 200480
  have htrace : WordTrace (prefixWord ++ tailWord_200480) baseStart_200480 baseEnd_200480 := by
    simpa [prefixWord, tailWord_200480, baseEnd_200480] using wordTrace_append hprefix tailTrace_200480
  have hstable : (prefixWord ++ tailWord_200480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200480).length < 2 ^ (prefixWord ++ tailWord_200480).sum := by decide
  have hdescent : baseEnd_200480 < baseStart_200480 := by decide
  rcases family_descends (prefixWord ++ tailWord_200480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200497 : List Nat := [1, 2, 2, 3, 2, 2, 4, 2, 3]
def baseStart_200497 : Nat := 118140960795 + 200497 * 2 ^ 59
def prefixEnd_200497 : Nat := 4983230072969 + 3 ^ 40 * 200497 * 2
def baseEnd_200497 : Nat := 45756147015381017006861

theorem tailTrace_200497 : CollatzResearch.WordTrace tailWord_200497 prefixEnd_200497 45756147015381017006861 := by
  unfold tailWord_200497
  simp only [CollatzResearch.WordTrace]
  refine ⟨7312726354641086006551745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4875150903094057337701163 7312726354641086006551745)
  ·
    refine ⟨5484544765980814504913809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7312726354641086006551745 5484544765980814504913809)
    ·
      refine ⟨4113408574485610878685357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5484544765980814504913809 4113408574485610878685357)
      ·
        refine ⟨1542528215432104079507009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4113408574485610878685357 1542528215432104079507009)
        ·
          refine ⟨1156896161574078059630257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1542528215432104079507009 1156896161574078059630257)
          ·
            refine ⟨867672121180558544722693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1156896161574078059630257 867672121180558544722693)
            ·
              refine ⟨162688522721354727135505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 867672121180558544722693 162688522721354727135505)
              ·
                refine ⟨122016392041016045351629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162688522721354727135505 122016392041016045351629)
                ·
                  refine ⟨45756147015381017006861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122016392041016045351629 45756147015381017006861)
                  ·
                    rfl

theorem cell21_200497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 3].length) (baseStart_200497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200497 prefixEnd_200497 := by exact prefixLift 200497
  have htrace : WordTrace (prefixWord ++ tailWord_200497) baseStart_200497 baseEnd_200497 := by
    simpa [prefixWord, tailWord_200497, baseEnd_200497] using wordTrace_append hprefix tailTrace_200497
  have hstable : (prefixWord ++ tailWord_200497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200497).length < 2 ^ (prefixWord ++ tailWord_200497).sum := by decide
  have hdescent : baseEnd_200497 < baseStart_200497 := by decide
  rcases family_descends (prefixWord ++ tailWord_200497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200508 : List Nat := [2, 2, 2, 2, 1, 1, 5, 6]
def baseStart_200508 : Nat := 118140960795 + 200508 * 2 ^ 59
def prefixEnd_200508 : Nat := 4983230072969 + 3 ^ 40 * 200508 * 2
def baseEnd_200508 : Nat := 15252885788415814107835

theorem tailTrace_200508 : CollatzResearch.WordTrace tailWord_200508 prefixEnd_200508 15252885788415814107835 := by
  unfold tailWord_200508
  simp only [CollatzResearch.WordTrace]
  refine ⟨3656563778800617442601089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4875418371734156590134785 3656563778800617442601089)
  ·
    refine ⟨2742422834100463081950817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3656563778800617442601089 2742422834100463081950817)
    ·
      refine ⟨2056817125575347311463113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2742422834100463081950817 2056817125575347311463113)
      ·
        refine ⟨1542612844181510483597335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2056817125575347311463113 1542612844181510483597335)
        ·
          refine ⟨2313919266272265725396003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542612844181510483597335 2313919266272265725396003)
          ·
            refine ⟨3470878899408398588094005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313919266272265725396003 3470878899408398588094005)
            ·
              refine ⟨325394896819537367633813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3470878899408398588094005 325394896819537367633813)
              ·
                refine ⟨15252885788415814107835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 325394896819537367633813 15252885788415814107835)
                ·
                  rfl

theorem cell21_200508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 6].length) (baseStart_200508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200508 prefixEnd_200508 := by exact prefixLift 200508
  have htrace : WordTrace (prefixWord ++ tailWord_200508) baseStart_200508 baseEnd_200508 := by
    simpa [prefixWord, tailWord_200508, baseEnd_200508] using wordTrace_append hprefix tailTrace_200508
  have hstable : (prefixWord ++ tailWord_200508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200508).length < 2 ^ (prefixWord ++ tailWord_200508).sum := by decide
  have hdescent : baseEnd_200508 < baseStart_200508 := by decide
  rcases family_descends (prefixWord ++ tailWord_200508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200556 : List Nat := [2, 2, 1, 1, 4, 2, 2, 4, 3]
def baseStart_200556 : Nat := 118140960795 + 200556 * 2 ^ 59
def prefixEnd_200556 : Nat := 4983230072969 + 3 ^ 40 * 200556 * 2
def baseEnd_200556 : Nat := 45769611619210025523407

theorem tailTrace_200556 : CollatzResearch.WordTrace tailWord_200556 prefixEnd_200556 45769611619210025523407 := by
  unfold tailWord_200556
  simp only [CollatzResearch.WordTrace]
  refine ⟨3657439130713669541474761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4876585507618226055299681 3657439130713669541474761)
  ·
    refine ⟨2743079348035252156106071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3657439130713669541474761 2743079348035252156106071)
    ·
      refine ⟨4114619022052878234159107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2743079348035252156106071 4114619022052878234159107)
      ·
        refine ⟨6171928533079317351238661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4114619022052878234159107 6171928533079317351238661)
        ·
          refine ⟨1157236599952372003357249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6171928533079317351238661 1157236599952372003357249)
          ·
            refine ⟨867927449964279002517937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1157236599952372003357249 867927449964279002517937)
            ·
              refine ⟨650945587473209251888453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 867927449964279002517937 650945587473209251888453)
              ·
                refine ⟨122052297651226734729085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 650945587473209251888453 122052297651226734729085)
                ·
                  refine ⟨45769611619210025523407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122052297651226734729085 45769611619210025523407)
                  ·
                    rfl

theorem cell21_200556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_200556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200556 prefixEnd_200556 := by exact prefixLift 200556
  have htrace : WordTrace (prefixWord ++ tailWord_200556) baseStart_200556 baseEnd_200556 := by
    simpa [prefixWord, tailWord_200556, baseEnd_200556] using wordTrace_append hprefix tailTrace_200556
  have hstable : (prefixWord ++ tailWord_200556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200556).length < 2 ^ (prefixWord ++ tailWord_200556).sum := by decide
  have hdescent : baseEnd_200556 < baseStart_200556 := by decide
  rcases family_descends (prefixWord ++ tailWord_200556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200666 : List Nat := [3, 1, 1, 2, 5, 2, 2, 2, 3]
def baseStart_200666 : Nat := 118140960795 + 200666 * 2 ^ 59
def prefixEnd_200666 : Nat := 4983230072969 + 3 ^ 40 * 200666 * 2
def baseEnd_200666 : Nat := 45794715117874278689849

theorem tailTrace_200666 : CollatzResearch.WordTrace tailWord_200666 prefixEnd_200666 45794715117874278689849 := by
  unfold tailWord_200666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1829722572757206967363463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4879260194019218579635901 1829722572757206967363463)
  ·
    refine ⟨2744583859135810451045195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1829722572757206967363463 2744583859135810451045195)
    ·
      refine ⟨4116875788703715676567793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2744583859135810451045195 4116875788703715676567793)
      ·
        refine ⟨3087656841527786757425845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4116875788703715676567793 3087656841527786757425845)
        ·
          refine ⟨289467828893230008508673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3087656841527786757425845 289467828893230008508673)
          ·
            refine ⟨217100871669922506381505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289467828893230008508673 217100871669922506381505)
            ·
              refine ⟨162825653752441879786129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217100871669922506381505 162825653752441879786129)
              ·
                refine ⟨122119240314331409839597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162825653752441879786129 122119240314331409839597)
                ·
                  refine ⟨45794715117874278689849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122119240314331409839597 45794715117874278689849)
                  ·
                    rfl

theorem cell21_200666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_200666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200666 prefixEnd_200666 := by exact prefixLift 200666
  have htrace : WordTrace (prefixWord ++ tailWord_200666) baseStart_200666 baseEnd_200666 := by
    simpa [prefixWord, tailWord_200666, baseEnd_200666] using wordTrace_append hprefix tailTrace_200666
  have hstable : (prefixWord ++ tailWord_200666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200666).length < 2 ^ (prefixWord ++ tailWord_200666).sum := by decide
  have hdescent : baseEnd_200666 < baseStart_200666 := by decide
  rcases family_descends (prefixWord ++ tailWord_200666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200694 : List Nat := [5, 1, 1, 1, 4, 1, 3, 5]
def baseStart_200694 : Nat := 118140960795 + 200694 * 2 ^ 59
def prefixEnd_200694 : Nat := 4983230072969 + 3 ^ 40 * 200694 * 2
def baseEnd_200694 : Nat := 15267035033117484074375

theorem tailTrace_200694 : CollatzResearch.WordTrace tailWord_200694 prefixEnd_200694 15267035033117484074375 := by
  unfold tailWord_200694
  simp only [CollatzResearch.WordTrace]
  refine ⟨457494470932961790717071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4879941023284925767648757 457494470932961790717071)
  ·
    refine ⟨686241706399442686075607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 457494470932961790717071 686241706399442686075607)
    ·
      refine ⟨1029362559599164029113411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 686241706399442686075607 1029362559599164029113411)
      ·
        refine ⟨1544043839398746043670117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029362559599164029113411 1544043839398746043670117)
        ·
          refine ⟨289508219887264883188147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1544043839398746043670117 289508219887264883188147)
          ·
            refine ⟨434262329830897324782221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289508219887264883188147 434262329830897324782221)
            ·
              refine ⟨162848373686586496793333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434262329830897324782221 162848373686586496793333)
              ·
                refine ⟨15267035033117484074375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162848373686586496793333 15267035033117484074375)
                ·
                  rfl

theorem cell21_200694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_200694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200694 prefixEnd_200694 := by exact prefixLift 200694
  have htrace : WordTrace (prefixWord ++ tailWord_200694) baseStart_200694 baseEnd_200694 := by
    simpa [prefixWord, tailWord_200694, baseEnd_200694] using wordTrace_append hprefix tailTrace_200694
  have hstable : (prefixWord ++ tailWord_200694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200694).length < 2 ^ (prefixWord ++ tailWord_200694).sum := by decide
  have hdescent : baseEnd_200694 < baseStart_200694 := by decide
  rcases family_descends (prefixWord ++ tailWord_200694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200705 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 6]
def baseStart_200705 : Nat := 118140960795 + 200705 * 2 ^ 59
def prefixEnd_200705 : Nat := 4983230072969 + 3 ^ 40 * 200705 * 2
def baseEnd_200705 : Nat := 45803615449218877539769

theorem tailTrace_200705 : CollatzResearch.WordTrace tailWord_200705 prefixEnd_200705 45803615449218877539769 := by
  unfold tailWord_200705
  simp only [CollatzResearch.WordTrace]
  refine ⟨7320312737887537530123569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4880208491925025020082379 7320312737887537530123569)
  ·
    refine ⟨5490234553415653147592677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7320312737887537530123569 5490234553415653147592677)
    ·
      refine ⟨1029418978765434965173627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5490234553415653147592677 1029418978765434965173627)
      ·
        refine ⟨1544128468148152447760441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029418978765434965173627 1544128468148152447760441)
        ·
          refine ⟨1158096351111114335820331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1544128468148152447760441 1158096351111114335820331)
          ·
            refine ⟨1737144526666671503730497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158096351111114335820331 1737144526666671503730497)
            ·
              refine ⟨1302858395000003627797873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1737144526666671503730497 1302858395000003627797873)
              ·
                refine ⟨977143796250002720848405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302858395000003627797873 977143796250002720848405)
                ·
                  refine ⟨45803615449218877539769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 977143796250002720848405 45803615449218877539769)
                  ·
                    rfl

theorem cell21_200705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_200705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200705 prefixEnd_200705 := by exact prefixLift 200705
  have htrace : WordTrace (prefixWord ++ tailWord_200705) baseStart_200705 baseEnd_200705 := by
    simpa [prefixWord, tailWord_200705, baseEnd_200705] using wordTrace_append hprefix tailTrace_200705
  have hstable : (prefixWord ++ tailWord_200705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200705).length < 2 ^ (prefixWord ++ tailWord_200705).sum := by decide
  have hdescent : baseEnd_200705 < baseStart_200705 := by decide
  rcases family_descends (prefixWord ++ tailWord_200705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200753 : List Nat := [1, 2, 2, 3, 1, 5, 2, 5]
def baseStart_200753 : Nat := 118140960795 + 200753 * 2 ^ 59
def prefixEnd_200753 : Nat := 4983230072969 + 3 ^ 40 * 200753 * 2
def baseEnd_200753 : Nat := 15271523234393820246557

theorem tailTrace_200753 : CollatzResearch.WordTrace tailWord_200753 prefixEnd_200753 15271523234393820246557 := by
  unfold tailWord_200753
  simp only [CollatzResearch.WordTrace]
  refine ⟨7322063441713641727870913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4881375627809094485247275 7322063441713641727870913)
  ·
    refine ⟨5491547581285231295903185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7322063441713641727870913 5491547581285231295903185)
    ·
      refine ⟨4118660685963923471927389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5491547581285231295903185 4118660685963923471927389)
      ·
        refine ⟨1544497757236471301972771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4118660685963923471927389 1544497757236471301972771)
        ·
          refine ⟨2316746635854706952959157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1544497757236471301972771 2316746635854706952959157)
          ·
            refine ⟨217194997111378776839921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2316746635854706952959157 217194997111378776839921)
            ·
              refine ⟨162896247833534082629941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217194997111378776839921 162896247833534082629941)
              ·
                refine ⟨15271523234393820246557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162896247833534082629941 15271523234393820246557)
                ·
                  rfl

theorem cell21_200753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 5].length) (baseStart_200753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200753 prefixEnd_200753 := by exact prefixLift 200753
  have htrace : WordTrace (prefixWord ++ tailWord_200753) baseStart_200753 baseEnd_200753 := by
    simpa [prefixWord, tailWord_200753, baseEnd_200753] using wordTrace_append hprefix tailTrace_200753
  have hstable : (prefixWord ++ tailWord_200753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200753).length < 2 ^ (prefixWord ++ tailWord_200753).sum := by decide
  have hdescent : baseEnd_200753 < baseStart_200753 := by decide
  rcases family_descends (prefixWord ++ tailWord_200753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200846 : List Nat := [4, 1, 1, 3, 4, 1, 1, 6]
def baseStart_200846 : Nat := 118140960795 + 200846 * 2 ^ 59
def prefixEnd_200846 : Nat := 4983230072969 + 3 ^ 40 * 200846 * 2
def baseEnd_200846 : Nat := 15278597856744655229827

theorem tailTrace_200846 : CollatzResearch.WordTrace tailWord_200846 prefixEnd_200846 15278597856744655229827 := by
  unfold tailWord_200846
  simp only [CollatzResearch.WordTrace]
  refine ⟨915681928797089826375799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4883636953584479074004261 915681928797089826375799)
  ·
    refine ⟨1373522893195634739563699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 915681928797089826375799 1373522893195634739563699)
    ·
      refine ⟨2060284339793452109345549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1373522893195634739563699 2060284339793452109345549)
      ·
        refine ⟨772606627422544541004581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2060284339793452109345549 772606627422544541004581)
        ·
          refine ⟨144863742641727101438359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 772606627422544541004581 144863742641727101438359)
          ·
            refine ⟨217295613962590652157539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144863742641727101438359 217295613962590652157539)
            ·
              refine ⟨325943420943885978236309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217295613962590652157539 325943420943885978236309)
              ·
                refine ⟨15278597856744655229827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 325943420943885978236309 15278597856744655229827)
                ·
                  rfl

theorem cell21_200846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_200846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200846 prefixEnd_200846 := by exact prefixLift 200846
  have htrace : WordTrace (prefixWord ++ tailWord_200846) baseStart_200846 baseEnd_200846 := by
    simpa [prefixWord, tailWord_200846, baseEnd_200846] using wordTrace_append hprefix tailTrace_200846
  have hstable : (prefixWord ++ tailWord_200846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200846).length < 2 ^ (prefixWord ++ tailWord_200846).sum := by decide
  have hdescent : baseEnd_200846 < baseStart_200846 := by decide
  rcases family_descends (prefixWord ++ tailWord_200846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200877 : List Nat := [1, 5, 2, 1, 2, 2, 2, 3, 3]
def baseStart_200877 : Nat := 118140960795 + 200877 * 2 ^ 59
def prefixEnd_200877 : Nat := 4983230072969 + 3 ^ 40 * 200877 * 2
def baseEnd_200877 : Nat := 45842868192584800672751

theorem tailTrace_200877 : CollatzResearch.WordTrace tailWord_200877 prefixEnd_200877 45842868192584800672751 := by
  unfold tailWord_200877
  simp only [CollatzResearch.WordTrace]
  refine ⟨7326586093264410905384885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4884390728842940603589923 7326586093264410905384885)
  ·
    refine ⟨686867446243538522379833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7326586093264410905384885 686867446243538522379833)
    ·
      refine ⟨515150584682653891784875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 686867446243538522379833 515150584682653891784875)
      ·
        refine ⟨772725877023980837677313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515150584682653891784875 772725877023980837677313)
        ·
          refine ⟨579544407767985628257985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 772725877023980837677313 579544407767985628257985)
          ·
            refine ⟨434658305825989221193489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 579544407767985628257985 434658305825989221193489)
            ·
              refine ⟨325993729369491915895117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434658305825989221193489 325993729369491915895117)
              ·
                refine ⟨122247648513559468460669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325993729369491915895117 122247648513559468460669)
                ·
                  refine ⟨45842868192584800672751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122247648513559468460669 45842868192584800672751)
                  ·
                    rfl

theorem cell21_200877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_200877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200877 prefixEnd_200877 := by exact prefixLift 200877
  have htrace : WordTrace (prefixWord ++ tailWord_200877) baseStart_200877 baseEnd_200877 := by
    simpa [prefixWord, tailWord_200877, baseEnd_200877] using wordTrace_append hprefix tailTrace_200877
  have hstable : (prefixWord ++ tailWord_200877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200877).length < 2 ^ (prefixWord ++ tailWord_200877).sum := by decide
  have hdescent : baseEnd_200877 < baseStart_200877 := by decide
  rcases family_descends (prefixWord ++ tailWord_200877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200908 : List Nat := [2, 2, 1, 6, 1, 1, 3, 1, 4]
def baseStart_200908 : Nat := 118140960795 + 200908 * 2 ^ 59
def prefixEnd_200908 : Nat := 4983230072969 + 3 ^ 40 * 200908 * 2
def baseEnd_200908 : Nat := 45849942814935635656021

theorem tailTrace_200908 : CollatzResearch.WordTrace tailWord_200908 prefixEnd_200908 45849942814935635656021 := by
  unfold tailWord_200908
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663858378076051599881689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4885144504101402133175585 3663858378076051599881689)
  ·
    refine ⟨2747893783557038699911267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3663858378076051599881689 2747893783557038699911267)
    ·
      refine ⟨4121840675335558049866901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2747893783557038699911267 4121840675335558049866901)
      ·
        refine ⟨193211281656354283587511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4121840675335558049866901 193211281656354283587511)
        ·
          refine ⟨289816922484531425381267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193211281656354283587511 289816922484531425381267)
          ·
            refine ⟨434725383726797138071901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289816922484531425381267 434725383726797138071901)
            ·
              refine ⟨163022018897548926776963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434725383726797138071901 163022018897548926776963)
              ·
                refine ⟨244533028346323390165445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163022018897548926776963 244533028346323390165445)
                ·
                  refine ⟨45849942814935635656021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 244533028346323390165445 45849942814935635656021)
                  ·
                    rfl

theorem cell21_200908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_200908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200908 prefixEnd_200908 := by exact prefixLift 200908
  have htrace : WordTrace (prefixWord ++ tailWord_200908) baseStart_200908 baseEnd_200908 := by
    simpa [prefixWord, tailWord_200908, baseEnd_200908] using wordTrace_append hprefix tailTrace_200908
  have hstable : (prefixWord ++ tailWord_200908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200908).length < 2 ^ (prefixWord ++ tailWord_200908).sum := by decide
  have hdescent : baseEnd_200908 < baseStart_200908 := by decide
  rcases family_descends (prefixWord ++ tailWord_200908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200933 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 6]
def baseStart_200933 : Nat := 118140960795 + 200933 * 2 ^ 59
def prefixEnd_200933 : Nat := 4983230072969 + 3 ^ 40 * 200933 * 2
def baseEnd_200933 : Nat := 45855648155541147739303

theorem tailTrace_200933 : CollatzResearch.WordTrace tailWord_200933 prefixEnd_200933 45855648155541147739303 := by
  unfold tailWord_200933
  simp only [CollatzResearch.WordTrace]
  refine ⟨7328628581061532469423453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4885752387374354979615635 7328628581061532469423453)
  ·
    refine ⟨2748235717898074676033795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7328628581061532469423453 2748235717898074676033795)
    ·
      refine ⟨4122353576847112014050693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2748235717898074676033795 4122353576847112014050693)
      ·
        refine ⟨772941295658833502634505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4122353576847112014050693 772941295658833502634505)
        ·
          refine ⟨579705971744125126975879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 772941295658833502634505 579705971744125126975879)
          ·
            refine ⟨869558957616187690463819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579705971744125126975879 869558957616187690463819)
            ·
              refine ⟨1304338436424281535695729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869558957616187690463819 1304338436424281535695729)
              ·
                refine ⟨978253827318211151771797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304338436424281535695729 978253827318211151771797)
                ·
                  refine ⟨45855648155541147739303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 978253827318211151771797 45855648155541147739303)
                  ·
                    rfl

theorem cell21_200933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_200933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200933 prefixEnd_200933 := by exact prefixLift 200933
  have htrace : WordTrace (prefixWord ++ tailWord_200933) baseStart_200933 baseEnd_200933 := by
    simpa [prefixWord, tailWord_200933, baseEnd_200933] using wordTrace_append hprefix tailTrace_200933
  have hstable : (prefixWord ++ tailWord_200933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200933).length < 2 ^ (prefixWord ++ tailWord_200933).sum := by decide
  have hdescent : baseEnd_200933 < baseStart_200933 := by decide
  rcases family_descends (prefixWord ++ tailWord_200933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200936 : List Nat := [2, 1, 4, 1, 2, 2, 3, 3, 3]
def baseStart_200936 : Nat := 118140960795 + 200936 * 2 ^ 59
def prefixEnd_200936 : Nat := 4983230072969 + 3 ^ 40 * 200936 * 2
def baseEnd_200936 : Nat := 45856332796413809189297

theorem tailTrace_200936 : CollatzResearch.WordTrace tailWord_200936 prefixEnd_200936 45856332796413809189297 := by
  unfold tailWord_200936
  simp only [CollatzResearch.WordTrace]
  refine ⟨3664369000025331990891331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4885825333367109321188441 3664369000025331990891331)
  ·
    refine ⟨5496553500037997986336997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3664369000025331990891331 5496553500037997986336997)
    ·
      refine ⟨1030603781257124622438187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5496553500037997986336997 1030603781257124622438187)
      ·
        refine ⟨1545905671885686933657281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030603781257124622438187 1545905671885686933657281)
        ·
          refine ⟨1159429253914265200242961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1545905671885686933657281 1159429253914265200242961)
          ·
            refine ⟨869571940435698900182221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1159429253914265200242961 869571940435698900182221)
            ·
              refine ⟨326089477663387087568333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 869571940435698900182221 326089477663387087568333)
              ·
                refine ⟨122283554123770157838125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326089477663387087568333 122283554123770157838125)
                ·
                  refine ⟨45856332796413809189297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122283554123770157838125 45856332796413809189297)
                  ·
                    rfl

theorem cell21_200936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 3].length) (baseStart_200936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200936 prefixEnd_200936 := by exact prefixLift 200936
  have htrace : WordTrace (prefixWord ++ tailWord_200936) baseStart_200936 baseEnd_200936 := by
    simpa [prefixWord, tailWord_200936, baseEnd_200936] using wordTrace_append hprefix tailTrace_200936
  have hstable : (prefixWord ++ tailWord_200936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200936).length < 2 ^ (prefixWord ++ tailWord_200936).sum := by decide
  have hdescent : baseEnd_200936 < baseStart_200936 := by decide
  rcases family_descends (prefixWord ++ tailWord_200936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200967 : List Nat := [1, 1, 4, 5, 1, 1, 1, 3, 4]
def baseStart_200967 : Nat := 118140960795 + 200967 * 2 ^ 59
def prefixEnd_200967 : Nat := 4983230072969 + 3 ^ 40 * 200967 * 2
def baseEnd_200967 : Nat := 45863407418764644172567

theorem tailTrace_200967 : CollatzResearch.WordTrace tailWord_200967 prefixEnd_200967 45863407418764644172567 := by
  unfold tailWord_200967
  simp only [CollatzResearch.WordTrace]
  refine ⟨7329868662938356276161155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4886579108625570850774103 7329868662938356276161155)
  ·
    refine ⟨10994802994407534414241733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7329868662938356276161155 10994802994407534414241733)
    ·
      refine ⟨2061525561451412702670325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10994802994407534414241733 2061525561451412702670325)
      ·
        refine ⟨193268021386069940875343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2061525561451412702670325 193268021386069940875343)
        ·
          refine ⟨289902032079104911313015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193268021386069940875343 289902032079104911313015)
          ·
            refine ⟨434853048118657366969523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289902032079104911313015 434853048118657366969523)
            ·
              refine ⟨652279572177986050454285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434853048118657366969523 652279572177986050454285)
              ·
                refine ⟨244604839566744768920357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 652279572177986050454285 244604839566744768920357)
                ·
                  refine ⟨45863407418764644172567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 244604839566744768920357 45863407418764644172567)
                  ·
                    rfl

theorem cell21_200967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 4].length) (baseStart_200967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200967 prefixEnd_200967 := by exact prefixLift 200967
  have htrace : WordTrace (prefixWord ++ tailWord_200967) baseStart_200967 baseEnd_200967 := by
    simpa [prefixWord, tailWord_200967, baseEnd_200967] using wordTrace_append hprefix tailTrace_200967
  have hstable : (prefixWord ++ tailWord_200967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200967).length < 2 ^ (prefixWord ++ tailWord_200967).sum := by decide
  have hdescent : baseEnd_200967 < baseStart_200967 := by decide
  rcases family_descends (prefixWord ++ tailWord_200967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200995 : List Nat := [1, 1, 1, 4, 2, 2, 2, 5, 3]
def baseStart_200995 : Nat := 118140960795 + 200995 * 2 ^ 59
def prefixEnd_200995 : Nat := 4983230072969 + 3 ^ 40 * 200995 * 2
def baseEnd_200995 : Nat := 45869797400242817705843

theorem tailTrace_200995 : CollatzResearch.WordTrace tailWord_200995 prefixEnd_200995 45869797400242817705843 := by
  unfold tailWord_200995
  simp only [CollatzResearch.WordTrace]
  refine ⟨7330889906836917058180439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4887259937891278038786959 7330889906836917058180439)
  ·
    refine ⟨10996334860255375587270659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7330889906836917058180439 10996334860255375587270659)
    ·
      refine ⟨16494502290383063380905989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10996334860255375587270659 16494502290383063380905989)
      ·
        refine ⟨3092719179446824383919873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16494502290383063380905989 3092719179446824383919873)
        ·
          refine ⟨2319539384585118287939905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3092719179446824383919873 2319539384585118287939905)
          ·
            refine ⟨1739654538438838715954929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2319539384585118287939905 1739654538438838715954929)
            ·
              refine ⟨1304740903829129036966197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1739654538438838715954929 1304740903829129036966197)
              ·
                refine ⟨122319459733980847215581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1304740903829129036966197 122319459733980847215581)
                ·
                  refine ⟨45869797400242817705843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122319459733980847215581 45869797400242817705843)
                  ·
                    rfl

theorem cell21_200995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 3].length) (baseStart_200995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_200995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_200995 prefixEnd_200995 := by exact prefixLift 200995
  have htrace : WordTrace (prefixWord ++ tailWord_200995) baseStart_200995 baseEnd_200995 := by
    simpa [prefixWord, tailWord_200995, baseEnd_200995] using wordTrace_append hprefix tailTrace_200995
  have hstable : (prefixWord ++ tailWord_200995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200995).length < 2 ^ (prefixWord ++ tailWord_200995).sum := by decide
  have hdescent : baseEnd_200995 < baseStart_200995 := by decide
  rcases family_descends (prefixWord ++ tailWord_200995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201040 : List Nat := [2, 1, 1, 1, 1, 7, 3, 5]
def baseStart_201040 : Nat := 118140960795 + 201040 * 2 ^ 59
def prefixEnd_201040 : Nat := 4983230072969 + 3 ^ 40 * 201040 * 2
def baseEnd_201040 : Nat := 15293355671110913151917

theorem tailTrace_201040 : CollatzResearch.WordTrace tailWord_201040 prefixEnd_201040 15293355671110913151917 := by
  unfold tailWord_201040
  simp only [CollatzResearch.WordTrace]
  refine ⟨3666265595836944871784287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4888354127782593162379049 3666265595836944871784287)
  ·
    refine ⟨5499398393755417307676431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3666265595836944871784287 5499398393755417307676431)
    ·
      refine ⟨8249097590633125961514647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5499398393755417307676431 8249097590633125961514647)
      ·
        refine ⟨12373646385949688942271971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8249097590633125961514647 12373646385949688942271971)
        ·
          refine ⟨18560469578924533413407957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12373646385949688942271971 18560469578924533413407957)
          ·
            refine ⟨435011005756043751876749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 18560469578924533413407957 435011005756043751876749)
            ·
              refine ⟨163129127158516406953781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435011005756043751876749 163129127158516406953781)
              ·
                refine ⟨15293355671110913151917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163129127158516406953781 15293355671110913151917)
                ·
                  rfl

theorem cell21_201040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 5].length) (baseStart_201040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201040 prefixEnd_201040 := by exact prefixLift 201040
  have htrace : WordTrace (prefixWord ++ tailWord_201040) baseStart_201040 baseEnd_201040 := by
    simpa [prefixWord, tailWord_201040, baseEnd_201040] using wordTrace_append hprefix tailTrace_201040
  have hstable : (prefixWord ++ tailWord_201040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201040).length < 2 ^ (prefixWord ++ tailWord_201040).sum := by decide
  have hdescent : baseEnd_201040 < baseStart_201040 := by decide
  rcases family_descends (prefixWord ++ tailWord_201040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201099 : List Nat := [1, 1, 1, 1, 4, 5, 1, 7]
def baseStart_201099 : Nat := 118140960795 + 201099 * 2 ^ 59
def prefixEnd_201099 : Nat := 4983230072969 + 3 ^ 40 * 201099 * 2
def baseEnd_201099 : Nat := 15297843872387249324099

theorem tailTrace_201099 : CollatzResearch.WordTrace tailWord_201099 prefixEnd_201099 15297843872387249324099 := by
  unfold tailWord_201099
  simp only [CollatzResearch.WordTrace]
  refine ⟨7334683098460142819966351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4889788732306761879977567 7334683098460142819966351)
  ·
    refine ⟨11002024647690214229949527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7334683098460142819966351 11002024647690214229949527)
    ·
      refine ⟨16503036971535321344924291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11002024647690214229949527 16503036971535321344924291)
      ·
        refine ⟨24754555457302982017386437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16503036971535321344924291 24754555457302982017386437)
        ·
          refine ⟨4641479148244309128259957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24754555457302982017386437 4641479148244309128259957)
          ·
            refine ⟨435138670147903980774371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4641479148244309128259957 435138670147903980774371)
            ·
              refine ⟨652708005221855971161557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435138670147903980774371 652708005221855971161557)
              ·
                refine ⟨15297843872387249324099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 652708005221855971161557 15297843872387249324099)
                ·
                  rfl

theorem cell21_201099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 7].length) (baseStart_201099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201099 prefixEnd_201099 := by exact prefixLift 201099
  have htrace : WordTrace (prefixWord ++ tailWord_201099) baseStart_201099 baseEnd_201099 := by
    simpa [prefixWord, tailWord_201099, baseEnd_201099] using wordTrace_append hprefix tailTrace_201099
  have hstable : (prefixWord ++ tailWord_201099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201099).length < 2 ^ (prefixWord ++ tailWord_201099).sum := by decide
  have hdescent : baseEnd_201099 < baseStart_201099 := by decide
  rcases family_descends (prefixWord ++ tailWord_201099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201133 : List Nat := [1, 5, 2, 2, 2, 1, 2, 6]
def baseStart_201133 : Nat := 118140960795 + 201133 * 2 ^ 59
def prefixEnd_201133 : Nat := 4983230072969 + 3 ^ 40 * 201133 * 2
def baseEnd_201133 : Nat := 15300430293461748135187

theorem tailTrace_201133 : CollatzResearch.WordTrace tailWord_201133 prefixEnd_201133 15300430293461748135187 := by
  unfold tailWord_201133
  simp only [CollatzResearch.WordTrace]
  refine ⟨7335923180336966626704053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4890615453557977751136035 7335923180336966626704053)
  ·
    refine ⟨687742798156590621253505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7335923180336966626704053 687742798156590621253505)
    ·
      refine ⟨515807098617442965940129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 687742798156590621253505 515807098617442965940129)
      ·
        refine ⟨386855323963082224455097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515807098617442965940129 386855323963082224455097)
        ·
          refine ⟨290141492972311668341323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386855323963082224455097 290141492972311668341323)
          ·
            refine ⟨435212239458467502511985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290141492972311668341323 435212239458467502511985)
            ·
              refine ⟨326409179593850626883989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435212239458467502511985 326409179593850626883989)
              ·
                refine ⟨15300430293461748135187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 326409179593850626883989 15300430293461748135187)
                ·
                  rfl

theorem cell21_201133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 6].length) (baseStart_201133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201133 prefixEnd_201133 := by exact prefixLift 201133
  have htrace : WordTrace (prefixWord ++ tailWord_201133) baseStart_201133 baseEnd_201133 := by
    simpa [prefixWord, tailWord_201133, baseEnd_201133] using wordTrace_append hprefix tailTrace_201133
  have hstable : (prefixWord ++ tailWord_201133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201133).length < 2 ^ (prefixWord ++ tailWord_201133).sum := by decide
  have hdescent : baseEnd_201133 < baseStart_201133 := by decide
  rcases family_descends (prefixWord ++ tailWord_201133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201192 : List Nat := [2, 1, 4, 1, 1, 5, 1, 6]
def baseStart_201192 : Nat := 118140960795 + 201192 * 2 ^ 59
def prefixEnd_201192 : Nat := 4983230072969 + 3 ^ 40 * 201192 * 2
def baseEnd_201192 : Nat := 15304918494738084307369

theorem tailTrace_201192 : CollatzResearch.WordTrace tailWord_201192 prefixEnd_201192 15304918494738084307369 := by
  unfold tailWord_201192
  simp only [CollatzResearch.WordTrace]
  refine ⟨3669037543561609851550915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4892050058082146468734553 3669037543561609851550915)
  ·
    refine ⟨5503556315342414777326373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3669037543561609851550915 5503556315342414777326373)
    ·
      refine ⟨1031916809126702770748695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5503556315342414777326373 1031916809126702770748695)
      ·
        refine ⟨1547875213690054156123043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1031916809126702770748695 1547875213690054156123043)
        ·
          refine ⟨2321812820535081234184565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1547875213690054156123043 2321812820535081234184565)
          ·
            refine ⟨217669951925163865704803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2321812820535081234184565 217669951925163865704803)
            ·
              refine ⟨326504927887745798557205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217669951925163865704803 326504927887745798557205)
              ·
                refine ⟨15304918494738084307369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 326504927887745798557205 15304918494738084307369)
                ·
                  rfl

theorem cell21_201192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 6].length) (baseStart_201192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201192 prefixEnd_201192 := by exact prefixLift 201192
  have htrace : WordTrace (prefixWord ++ tailWord_201192) baseStart_201192 baseEnd_201192 := by
    simpa [prefixWord, tailWord_201192, baseEnd_201192] using wordTrace_append hprefix tailTrace_201192
  have hstable : (prefixWord ++ tailWord_201192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201192).length < 2 ^ (prefixWord ++ tailWord_201192).sum := by decide
  have hdescent : baseEnd_201192 < baseStart_201192 := by decide
  rcases family_descends (prefixWord ++ tailWord_201192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201313 : List Nat := [1, 2, 3, 1, 1, 5, 1, 3, 4]
def baseStart_201313 : Nat := 118140960795 + 201313 * 2 ^ 59
def prefixEnd_201313 : Nat := 4983230072969 + 3 ^ 40 * 201313 * 2
def baseEnd_201313 : Nat := 45942369332744931405193

theorem tailTrace_201313 : CollatzResearch.WordTrace tailWord_201313 prefixEnd_201313 45942369332744931405193 := by
  unfold tailWord_201313
  simp only [CollatzResearch.WordTrace]
  refine ⟨7342488319684857368256593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4894992213123238245504395 7342488319684857368256593)
  ·
    refine ⟨5506866239763643026192445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7342488319684857368256593 5506866239763643026192445)
    ·
      refine ⟨2065074839911366134822167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5506866239763643026192445 2065074839911366134822167)
      ·
        refine ⟨3097612259867049202233251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2065074839911366134822167 3097612259867049202233251)
        ·
          refine ⟨4646418389800573803349877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3097612259867049202233251 4646418389800573803349877)
          ·
            refine ⟨435601724043803794064051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4646418389800573803349877 435601724043803794064051)
            ·
              refine ⟨653402586065705691096077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435601724043803794064051 653402586065705691096077)
              ·
                refine ⟨245025969774639634161029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 653402586065705691096077 245025969774639634161029)
                ·
                  refine ⟨45942369332744931405193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245025969774639634161029 45942369332744931405193)
                  ·
                    rfl

theorem cell21_201313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_201313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201313 prefixEnd_201313 := by exact prefixLift 201313
  have htrace : WordTrace (prefixWord ++ tailWord_201313) baseStart_201313 baseEnd_201313 := by
    simpa [prefixWord, tailWord_201313, baseEnd_201313] using wordTrace_append hprefix tailTrace_201313
  have hstable : (prefixWord ++ tailWord_201313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201313).length < 2 ^ (prefixWord ++ tailWord_201313).sum := by decide
  have hdescent : baseEnd_201313 < baseStart_201313 := by decide
  rcases family_descends (prefixWord ++ tailWord_201313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201358 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_201358 : Nat := 118140960795 + 201358 * 2 ^ 59
def prefixEnd_201358 : Nat := 4983230072969 + 3 ^ 40 * 201358 * 2
def baseEnd_201358 : Nat := 45952638945834853155101

theorem tailTrace_201358 : CollatzResearch.WordTrace tailWord_201358 prefixEnd_201358 45952638945834853155101 := by
  unfold tailWord_201358
  simp only [CollatzResearch.WordTrace]
  refine ⟨918016200565228756705591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4896086403014553369096485 918016200565228756705591)
  ·
    refine ⟨1377024300847843135058387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 918016200565228756705591 1377024300847843135058387)
    ·
      refine ⟨2065536451271764702587581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1377024300847843135058387 2065536451271764702587581)
      ·
        refine ⟨774576169226911763470343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2065536451271764702587581 774576169226911763470343)
        ·
          refine ⟨1161864253840367645205515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774576169226911763470343 1161864253840367645205515)
          ·
            refine ⟨1742796380760551467808273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161864253840367645205515 1742796380760551467808273)
            ·
              refine ⟨1307097285570413600856205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1742796380760551467808273 1307097285570413600856205)
              ·
                refine ⟨490161482088905100321077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1307097285570413600856205 490161482088905100321077)
                ·
                  refine ⟨45952638945834853155101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 490161482088905100321077 45952638945834853155101)
                  ·
                    rfl

theorem cell21_201358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_201358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201358 prefixEnd_201358 := by exact prefixLift 201358
  have htrace : WordTrace (prefixWord ++ tailWord_201358) baseStart_201358 baseEnd_201358 := by
    simpa [prefixWord, tailWord_201358, baseEnd_201358] using wordTrace_append hprefix tailTrace_201358
  have hstable : (prefixWord ++ tailWord_201358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201358).length < 2 ^ (prefixWord ++ tailWord_201358).sum := by decide
  have hdescent : baseEnd_201358 < baseStart_201358 := by decide
  rcases family_descends (prefixWord ++ tailWord_201358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201468 : List Nat := [2, 2, 2, 1, 3, 3, 3, 2, 3]
def baseStart_201468 : Nat := 118140960795 + 201468 * 2 ^ 59
def prefixEnd_201468 : Nat := 4983230072969 + 3 ^ 40 * 201468 * 2
def baseEnd_201468 : Nat := 45977742444499106321543

theorem tailTrace_201468 : CollatzResearch.WordTrace tailWord_201468 prefixEnd_201468 45977742444499106321543 := by
  unfold tailWord_201468
  simp only [CollatzResearch.WordTrace]
  refine ⟨3674070817061659420074529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4898761089415545893432705 3674070817061659420074529)
  ·
    refine ⟨2755553112796244565055897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3674070817061659420074529 2755553112796244565055897)
    ·
      refine ⟨2066664834597183423791923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2755553112796244565055897 2066664834597183423791923)
      ·
        refine ⟨3099997251895775135687885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2066664834597183423791923 3099997251895775135687885)
        ·
          refine ⟨1162498969460915675882957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3099997251895775135687885 1162498969460915675882957)
          ·
            refine ⟨435937113547843378456109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1162498969460915675882957 435937113547843378456109)
            ·
              refine ⟨163476417580441266921041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435937113547843378456109 163476417580441266921041)
              ·
                refine ⟨122607313185330950190781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163476417580441266921041 122607313185330950190781)
                ·
                  refine ⟨45977742444499106321543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122607313185330950190781 45977742444499106321543)
                  ·
                    rfl

theorem cell21_201468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_201468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201468 prefixEnd_201468 := by exact prefixLift 201468
  have htrace : WordTrace (prefixWord ++ tailWord_201468) baseStart_201468 baseEnd_201468 := by
    simpa [prefixWord, tailWord_201468, baseEnd_201468] using wordTrace_append hprefix tailTrace_201468
  have hstable : (prefixWord ++ tailWord_201468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201468).length < 2 ^ (prefixWord ++ tailWord_201468).sum := by decide
  have hdescent : baseEnd_201468 < baseStart_201468 := by decide
  rcases family_descends (prefixWord ++ tailWord_201468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201479 : List Nat := [1, 1, 4, 4, 1, 1, 1, 8]
def baseStart_201479 : Nat := 118140960795 + 201479 * 2 ^ 59
def prefixEnd_201479 : Nat := 4983230072969 + 3 ^ 40 * 201479 * 2
def baseEnd_201479 : Nat := 15326750931455177212729

theorem tailTrace_201479 : CollatzResearch.WordTrace tailWord_201479 prefixEnd_201479 15326750931455177212729 := by
  unfold tailWord_201479
  simp only [CollatzResearch.WordTrace]
  refine ⟨7348542837083467718799491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4899028558055645145866327 7348542837083467718799491)
  ·
    refine ⟨11022814255625201578199237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7348542837083467718799491 11022814255625201578199237)
    ·
      refine ⟨2066777672929725295912357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11022814255625201578199237 2066777672929725295912357)
      ·
        refine ⟨387520813674323492983567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2066777672929725295912357 387520813674323492983567)
        ·
          refine ⟨581281220511485239475351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387520813674323492983567 581281220511485239475351)
          ·
            refine ⟨871921830767227859213027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581281220511485239475351 871921830767227859213027)
            ·
              refine ⟨1307882746150841788819541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871921830767227859213027 1307882746150841788819541)
              ·
                refine ⟨15326750931455177212729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1307882746150841788819541 15326750931455177212729)
                ·
                  rfl

theorem cell21_201479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 8].length) (baseStart_201479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201479 prefixEnd_201479 := by exact prefixLift 201479
  have htrace : WordTrace (prefixWord ++ tailWord_201479) baseStart_201479 baseEnd_201479 := by
    simpa [prefixWord, tailWord_201479, baseEnd_201479] using wordTrace_append hprefix tailTrace_201479
  have hstable : (prefixWord ++ tailWord_201479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201479).length < 2 ^ (prefixWord ++ tailWord_201479).sum := by decide
  have hdescent : baseEnd_201479 < baseStart_201479 := by decide
  rcases family_descends (prefixWord ++ tailWord_201479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201493 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 7]
def baseStart_201493 : Nat := 118140960795 + 201493 * 2 ^ 59
def prefixEnd_201493 : Nat := 4983230072969 + 3 ^ 40 * 201493 * 2
def baseEnd_201493 : Nat := 45983447785104618404825

theorem tailTrace_201493 : CollatzResearch.WordTrace tailWord_201493 prefixEnd_201493 45983447785104618404825 := by
  unfold tailWord_201493
  simp only [CollatzResearch.WordTrace]
  refine ⟨7349053459032748109809133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4899368972688498739872755 7349053459032748109809133)
  ·
    refine ⟨2755895047137280541178425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7349053459032748109809133 2755895047137280541178425)
    ·
      refine ⟨2066921285352960405883819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2755895047137280541178425 2066921285352960405883819)
      ·
        refine ⟨3100381928029440608825729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2066921285352960405883819 3100381928029440608825729)
        ·
          refine ⟨2325286446022080456619297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3100381928029440608825729 2325286446022080456619297)
          ·
            refine ⟨1743964834516560342464473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2325286446022080456619297 1743964834516560342464473)
            ·
              refine ⟨1307973625887420256848355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1743964834516560342464473 1307973625887420256848355)
              ·
                refine ⟨1961960438831130385272533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307973625887420256848355 1961960438831130385272533)
                ·
                  refine ⟨45983447785104618404825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1961960438831130385272533 45983447785104618404825)
                  ·
                    rfl

theorem cell21_201493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_201493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201493 prefixEnd_201493 := by exact prefixLift 201493
  have htrace : WordTrace (prefixWord ++ tailWord_201493) baseStart_201493 baseEnd_201493 := by
    simpa [prefixWord, tailWord_201493, baseEnd_201493] using wordTrace_append hprefix tailTrace_201493
  have hstable : (prefixWord ++ tailWord_201493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201493).length < 2 ^ (prefixWord ++ tailWord_201493).sum := by decide
  have hdescent : baseEnd_201493 < baseStart_201493 := by decide
  rcases family_descends (prefixWord ++ tailWord_201493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201631 : List Nat := [1, 1, 2, 5, 2, 3, 7]
def baseStart_201631 : Nat := 118140960795 + 201631 * 2 ^ 59
def prefixEnd_201631 : Nat := 4983230072969 + 3 ^ 40 * 201631 * 2
def baseEnd_201631 : Nat := 5112771251694116122727

theorem tailTrace_201631 : CollatzResearch.WordTrace tailWord_201631 prefixEnd_201631 5112771251694116122727 := by
  unfold tailWord_201631
  simp only [CollatzResearch.WordTrace]
  refine ⟨7354086732532797678332747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4902724488355198452221831 7354086732532797678332747)
  ·
    refine ⟨11031130098799196517499121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7354086732532797678332747 11031130098799196517499121)
    ·
      refine ⟨8273347574099397388124341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11031130098799196517499121 8273347574099397388124341)
      ·
        refine ⟨775626335071818505136657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8273347574099397388124341 775626335071818505136657)
        ·
          refine ⟨581719751303863878852493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775626335071818505136657 581719751303863878852493)
          ·
            refine ⟨218144906738948954569685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 581719751303863878852493 218144906738948954569685)
            ·
              refine ⟨5112771251694116122727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 218144906738948954569685 5112771251694116122727)
              ·
                rfl

theorem cell21_201631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 7].length) (baseStart_201631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201631 prefixEnd_201631 := by exact prefixLift 201631
  have htrace : WordTrace (prefixWord ++ tailWord_201631) baseStart_201631 baseEnd_201631 := by
    simpa [prefixWord, tailWord_201631, baseEnd_201631] using wordTrace_append hprefix tailTrace_201631
  have hstable : (prefixWord ++ tailWord_201631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201631).length < 2 ^ (prefixWord ++ tailWord_201631).sum := by decide
  have hdescent : baseEnd_201631 < baseStart_201631 := by decide
  rcases family_descends (prefixWord ++ tailWord_201631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201690 : List Nat := [3, 1, 1, 2, 4, 10]
def baseStart_201690 : Nat := 118140960795 + 201690 * 2 ^ 59
def prefixEnd_201690 : Nat := 4983230072969 + 3 ^ 40 * 201690 * 2
def baseEnd_201690 : Nat := 1704755772928742726707

theorem tailTrace_201690 : CollatzResearch.WordTrace tailWord_201690 prefixEnd_201690 1704755772928742726707 := by
  unfold tailWord_201690
  simp only [CollatzResearch.WordTrace]
  refine ⟨1839059659829762688682631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4904159092879367169820349 1839059659829762688682631)
  ·
    refine ⟨2758589489744644033023947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1839059659829762688682631 2758589489744644033023947)
    ·
      refine ⟨4137884234616966049535921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2758589489744644033023947 4137884234616966049535921)
      ·
        refine ⟨3103413175962724537151941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4137884234616966049535921 3103413175962724537151941)
        ·
          refine ⟨581889970493010850715989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3103413175962724537151941 581889970493010850715989)
          ·
            refine ⟨1704755772928742726707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 581889970493010850715989 1704755772928742726707)
            ·
              rfl

theorem cell21_201690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 10].length) (baseStart_201690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201690 prefixEnd_201690 := by exact prefixLift 201690
  have htrace : WordTrace (prefixWord ++ tailWord_201690) baseStart_201690 baseEnd_201690 := by
    simpa [prefixWord, tailWord_201690, baseEnd_201690] using wordTrace_append hprefix tailTrace_201690
  have hstable : (prefixWord ++ tailWord_201690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201690).length < 2 ^ (prefixWord ++ tailWord_201690).sum := by decide
  have hdescent : baseEnd_201690 < baseStart_201690 := by decide
  rcases family_descends (prefixWord ++ tailWord_201690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201693 : List Nat := [1, 4, 3, 1, 2, 1, 1, 4, 4]
def baseStart_201693 : Nat := 118140960795 + 201693 * 2 ^ 59
def prefixEnd_201693 : Nat := 4983230072969 + 3 ^ 40 * 201693 * 2
def baseEnd_201693 : Nat := 46029090509948715071083

theorem tailTrace_201693 : CollatzResearch.WordTrace tailWord_201693 prefixEnd_201693 46029090509948715071083 := by
  unfold tailWord_201693
  simp only [CollatzResearch.WordTrace]
  refine ⟨7356348058308182267089733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4904232038872121511393155 7356348058308182267089733)
  ·
    refine ⟨1379315260932784175079325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7356348058308182267089733 1379315260932784175079325)
    ·
      refine ⟨517243222849794065654747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1379315260932784175079325 517243222849794065654747)
      ·
        refine ⟨775864834274691098482121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517243222849794065654747 775864834274691098482121)
        ·
          refine ⟨581898625706018323861591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775864834274691098482121 581898625706018323861591)
          ·
            refine ⟨872847938559027485792387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581898625706018323861591 872847938559027485792387)
            ·
              refine ⟨1309271907838541228688581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872847938559027485792387 1309271907838541228688581)
              ·
                refine ⟨245488482719726480379109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1309271907838541228688581 245488482719726480379109)
                ·
                  refine ⟨46029090509948715071083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245488482719726480379109 46029090509948715071083)
                  ·
                    rfl

theorem cell21_201693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_201693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201693 prefixEnd_201693 := by exact prefixLift 201693
  have htrace : WordTrace (prefixWord ++ tailWord_201693) baseStart_201693 baseEnd_201693 := by
    simpa [prefixWord, tailWord_201693, baseEnd_201693] using wordTrace_append hprefix tailTrace_201693
  have hstable : (prefixWord ++ tailWord_201693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201693).length < 2 ^ (prefixWord ++ tailWord_201693).sum := by decide
  have hdescent : baseEnd_201693 < baseStart_201693 := by decide
  rcases family_descends (prefixWord ++ tailWord_201693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201721 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 5]
def baseStart_201721 : Nat := 118140960795 + 201721 * 2 ^ 59
def prefixEnd_201721 : Nat := 4983230072969 + 3 ^ 40 * 201721 * 2
def baseEnd_201721 : Nat := 46035480491426888604359

theorem tailTrace_201721 : CollatzResearch.WordTrace tailWord_201721 prefixEnd_201721 46035480491426888604359 := by
  unfold tailWord_201721
  simp only [CollatzResearch.WordTrace]
  refine ⟨7357369302206743049109017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4904912868137828699406011 7357369302206743049109017)
  ·
    refine ⟨5518026976655057286831763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7357369302206743049109017 5518026976655057286831763)
    ·
      refine ⟨8277040464982585930247645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5518026976655057286831763 8277040464982585930247645)
      ·
        refine ⟨3103890174368469723842867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8277040464982585930247645 3103890174368469723842867)
        ·
          refine ⟨4655835261552704585764301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3103890174368469723842867 4655835261552704585764301)
          ·
            refine ⟨1745938223082264219661613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4655835261552704585764301 1745938223082264219661613)
            ·
              refine ⟨654726833655849082373105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1745938223082264219661613 654726833655849082373105)
              ·
                refine ⟨491045125241886811779829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 654726833655849082373105 491045125241886811779829)
                ·
                  refine ⟨46035480491426888604359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 491045125241886811779829 46035480491426888604359)
                  ·
                    rfl

theorem cell21_201721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_201721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201721 prefixEnd_201721 := by exact prefixLift 201721
  have htrace : WordTrace (prefixWord ++ tailWord_201721) baseStart_201721 baseEnd_201721 := by
    simpa [prefixWord, tailWord_201721, baseEnd_201721] using wordTrace_append hprefix tailTrace_201721
  have hstable : (prefixWord ++ tailWord_201721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201721).length < 2 ^ (prefixWord ++ tailWord_201721).sum := by decide
  have hdescent : baseEnd_201721 < baseStart_201721 := by decide
  rcases family_descends (prefixWord ++ tailWord_201721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201752 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 6]
def baseStart_201752 : Nat := 118140960795 + 201752 * 2 ^ 59
def prefixEnd_201752 : Nat := 4983230072969 + 3 ^ 40 * 201752 * 2
def baseEnd_201752 : Nat := 46042555113777723587629

theorem tailTrace_201752 : CollatzResearch.WordTrace tailWord_201752 prefixEnd_201752 46042555113777723587629 := by
  unfold tailWord_201752
  simp only [CollatzResearch.WordTrace]
  refine ⟨3679249982547217671743755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4905666643396290228991673 3679249982547217671743755)
  ·
    refine ⟨5518874973820826507615633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3679249982547217671743755 5518874973820826507615633)
    ·
      refine ⟨4139156230365619880711725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5518874973820826507615633 4139156230365619880711725)
      ·
        refine ⟨1552183586387107455266897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4139156230365619880711725 1552183586387107455266897)
        ·
          refine ⟨1164137689790330591450173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1552183586387107455266897 1164137689790330591450173)
          ·
            refine ⟨436551633671373971793815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1164137689790330591450173 436551633671373971793815)
            ·
              refine ⟨654827450507060957690723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436551633671373971793815 654827450507060957690723)
              ·
                refine ⟨982241175760591436536085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654827450507060957690723 982241175760591436536085)
                ·
                  refine ⟨46042555113777723587629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 982241175760591436536085 46042555113777723587629)
                  ·
                    rfl

theorem cell21_201752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_201752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201752 prefixEnd_201752 := by exact prefixLift 201752
  have htrace : WordTrace (prefixWord ++ tailWord_201752) baseStart_201752 baseEnd_201752 := by
    simpa [prefixWord, tailWord_201752, baseEnd_201752] using wordTrace_append hprefix tailTrace_201752
  have hstable : (prefixWord ++ tailWord_201752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201752).length < 2 ^ (prefixWord ++ tailWord_201752).sum := by decide
  have hdescent : baseEnd_201752 < baseStart_201752 := by decide
  rcases family_descends (prefixWord ++ tailWord_201752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201842 : List Nat := [3, 2, 1, 2, 2, 1, 1, 9]
def baseStart_201842 : Nat := 118140960795 + 201842 * 2 ^ 59
def prefixEnd_201842 : Nat := 4983230072969 + 3 ^ 40 * 201842 * 2
def baseEnd_201842 : Nat := 15354364779985855695815

theorem tailTrace_201842 : CollatzResearch.WordTrace tailWord_201842 prefixEnd_201842 15354364779985855695815 := by
  unfold tailWord_201842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1840445633692095178565945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4907855023178920476175853 1840445633692095178565945)
  ·
    refine ⟨1380334225269071383924459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1840445633692095178565945 1380334225269071383924459)
    ·
      refine ⟨2070501337903607075886689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1380334225269071383924459 2070501337903607075886689)
      ·
        refine ⟨1552876003427705306915017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2070501337903607075886689 1552876003427705306915017)
        ·
          refine ⟨1164657002570778980186263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1552876003427705306915017 1164657002570778980186263)
          ·
            refine ⟨1746985503856168470279395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164657002570778980186263 1746985503856168470279395)
            ·
              refine ⟨2620478255784252705419093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1746985503856168470279395 2620478255784252705419093)
              ·
                refine ⟨15354364779985855695815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2620478255784252705419093 15354364779985855695815)
                ·
                  rfl

theorem cell21_201842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_201842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201842 prefixEnd_201842 := by exact prefixLift 201842
  have htrace : WordTrace (prefixWord ++ tailWord_201842) baseStart_201842 baseEnd_201842 := by
    simpa [prefixWord, tailWord_201842, baseEnd_201842] using wordTrace_append hprefix tailTrace_201842
  have hstable : (prefixWord ++ tailWord_201842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201842).length < 2 ^ (prefixWord ++ tailWord_201842).sum := by decide
  have hdescent : baseEnd_201842 < baseStart_201842 := by decide
  rcases family_descends (prefixWord ++ tailWord_201842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201921 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 6]
def baseStart_201921 : Nat := 118140960795 + 201921 * 2 ^ 59
def prefixEnd_201921 : Nat := 4983230072969 + 3 ^ 40 * 201921 * 2
def baseEnd_201921 : Nat := 46081123216270985270617

theorem tailTrace_201921 : CollatzResearch.WordTrace tailWord_201921 prefixEnd_201921 46081123216270985270617 := by
  unfold tailWord_201921
  simp only [CollatzResearch.WordTrace]
  refine ⟨7364663901482177206389617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4909775934321451470926411 7364663901482177206389617)
  ·
    refine ⟨5523497926111632904792213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7364663901482177206389617 5523497926111632904792213)
    ·
      refine ⟨258913965286482792412135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5523497926111632904792213 258913965286482792412135)
      ·
        refine ⟨388370947929724188618203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258913965286482792412135 388370947929724188618203)
        ·
          refine ⟨582556421894586282927305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388370947929724188618203 582556421894586282927305)
          ·
            refine ⟨436917316420939712195479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582556421894586282927305 436917316420939712195479)
            ·
              refine ⟨655375974631409568293219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436917316420939712195479 655375974631409568293219)
              ·
                refine ⟨983063961947114352439829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655375974631409568293219 983063961947114352439829)
                ·
                  refine ⟨46081123216270985270617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 983063961947114352439829 46081123216270985270617)
                  ·
                    rfl

theorem cell21_201921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_201921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201921 prefixEnd_201921 := by exact prefixLift 201921
  have htrace : WordTrace (prefixWord ++ tailWord_201921) baseStart_201921 baseEnd_201921 := by
    simpa [prefixWord, tailWord_201921, baseEnd_201921] using wordTrace_append hprefix tailTrace_201921
  have hstable : (prefixWord ++ tailWord_201921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201921).length < 2 ^ (prefixWord ++ tailWord_201921).sum := by decide
  have hdescent : baseEnd_201921 < baseStart_201921 := by decide
  rcases family_descends (prefixWord ++ tailWord_201921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201963 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 6]
def baseStart_201963 : Nat := 118140960795 + 201963 * 2 ^ 59
def prefixEnd_201963 : Nat := 4983230072969 + 3 ^ 40 * 201963 * 2
def baseEnd_201963 : Nat := 46090708188488245570531

theorem tailTrace_201963 : CollatzResearch.WordTrace tailWord_201963 prefixEnd_201963 46090708188488245570531 := by
  unfold tailWord_201963
  simp only [CollatzResearch.WordTrace]
  refine ⟨7366195767330018379418543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4910797178220012252945695 7366195767330018379418543)
  ·
    refine ⟨11049293650995027569127815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7366195767330018379418543 11049293650995027569127815)
    ·
      refine ⟨16573940476492541353691723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11049293650995027569127815 16573940476492541353691723)
      ·
        refine ⟨24860910714738812030537585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16573940476492541353691723 24860910714738812030537585)
        ·
          refine ⟨18645683036054109022903189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24860910714738812030537585 18645683036054109022903189)
          ·
            refine ⟨874016392315036360448587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18645683036054109022903189 874016392315036360448587)
            ·
              refine ⟨1311024588472554540672881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874016392315036360448587 1311024588472554540672881)
              ·
                refine ⟨983268441354415905504661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1311024588472554540672881 983268441354415905504661)
                ·
                  refine ⟨46090708188488245570531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 983268441354415905504661 46090708188488245570531)
                  ·
                    rfl

theorem cell21_201963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 6].length) (baseStart_201963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201963 prefixEnd_201963 := by exact prefixLift 201963
  have htrace : WordTrace (prefixWord ++ tailWord_201963) baseStart_201963 baseEnd_201963 := by
    simpa [prefixWord, tailWord_201963, baseEnd_201963] using wordTrace_append hprefix tailTrace_201963
  have hstable : (prefixWord ++ tailWord_201963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201963).length < 2 ^ (prefixWord ++ tailWord_201963).sum := by decide
  have hdescent : baseEnd_201963 < baseStart_201963 := by decide
  rcases family_descends (prefixWord ++ tailWord_201963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201983 : List Nat := [1, 1, 2, 2, 1, 6, 3, 2, 3]
def baseStart_201983 : Nat := 118140960795 + 201983 * 2 ^ 59
def prefixEnd_201983 : Nat := 4983230072969 + 3 ^ 40 * 201983 * 2
def baseEnd_201983 : Nat := 46095272460972655237157

theorem tailTrace_201983 : CollatzResearch.WordTrace tailWord_201983 prefixEnd_201983 46095272460972655237157 := by
  unfold tailWord_201983
  simp only [CollatzResearch.WordTrace]
  refine ⟨7366925227257561795146603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4911283484838374530097735 7366925227257561795146603)
  ·
    refine ⟨11050387840886342692719905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7366925227257561795146603 11050387840886342692719905)
    ·
      refine ⟨8287790880664757019539929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11050387840886342692719905 8287790880664757019539929)
      ·
        refine ⟨6215843160498567764654947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8287790880664757019539929 6215843160498567764654947)
        ·
          refine ⟨9323764740747851646982421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6215843160498567764654947 9323764740747851646982421)
          ·
            refine ⟨437051472222555545952301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9323764740747851646982421 437051472222555545952301)
            ·
              refine ⟨163894302083458329732113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 437051472222555545952301 163894302083458329732113)
              ·
                refine ⟨122920726562593747299085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163894302083458329732113 122920726562593747299085)
                ·
                  refine ⟨46095272460972655237157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122920726562593747299085 46095272460972655237157)
                  ·
                    rfl

theorem cell21_201983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 3].length) (baseStart_201983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_201983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_201983 prefixEnd_201983 := by exact prefixLift 201983
  have htrace : WordTrace (prefixWord ++ tailWord_201983) baseStart_201983 baseEnd_201983 := by
    simpa [prefixWord, tailWord_201983, baseEnd_201983] using wordTrace_append hprefix tailTrace_201983
  have hstable : (prefixWord ++ tailWord_201983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201983).length < 2 ^ (prefixWord ++ tailWord_201983).sum := by decide
  have hdescent : baseEnd_201983 < baseStart_201983 := by decide
  rcases family_descends (prefixWord ++ tailWord_201983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202042 : List Nat := [3, 1, 1, 1, 4, 1, 3, 4, 3]
def baseStart_202042 : Nat := 118140960795 + 202042 * 2 ^ 59
def prefixEnd_202042 : Nat := 4983230072969 + 3 ^ 40 * 202042 * 2
def baseEnd_202042 : Nat := 46108737064801663753703

theorem tailTrace_202042 : CollatzResearch.WordTrace tailWord_202042 prefixEnd_202042 46108737064801663753703 := by
  unfold tailWord_202042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1842269283510953717886095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4912718089362543247696253 1842269283510953717886095)
  ·
    refine ⟨2763403925266430576829143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1842269283510953717886095 2763403925266430576829143)
    ·
      refine ⟨4145105887899645865243715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2763403925266430576829143 4145105887899645865243715)
      ·
        refine ⟨6217658831849468797865573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4145105887899645865243715 6217658831849468797865573)
        ·
          refine ⟨1165811030971775399599795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6217658831849468797865573 1165811030971775399599795)
          ·
            refine ⟨1748716546457663099399693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165811030971775399599795 1748716546457663099399693)
            ·
              refine ⟨655768704921623662274885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1748716546457663099399693 655768704921623662274885)
              ·
                refine ⟨122956632172804436676541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 655768704921623662274885 122956632172804436676541)
                ·
                  refine ⟨46108737064801663753703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122956632172804436676541 46108737064801663753703)
                  ·
                    rfl

theorem cell21_202042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_202042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202042 prefixEnd_202042 := by exact prefixLift 202042
  have htrace : WordTrace (prefixWord ++ tailWord_202042) baseStart_202042 baseEnd_202042 := by
    simpa [prefixWord, tailWord_202042, baseEnd_202042] using wordTrace_append hprefix tailTrace_202042
  have hstable : (prefixWord ++ tailWord_202042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202042).length < 2 ^ (prefixWord ++ tailWord_202042).sum := by decide
  have hdescent : baseEnd_202042 < baseStart_202042 := by decide
  rcases family_descends (prefixWord ++ tailWord_202042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202045 : List Nat := [1, 4, 1, 5, 2, 1, 1, 6]
def baseStart_202045 : Nat := 118140960795 + 202045 * 2 ^ 59
def prefixEnd_202045 : Nat := 4983230072969 + 3 ^ 40 * 202045 * 2
def baseEnd_202045 : Nat := 15369807235224775067899

theorem tailTrace_202045 : CollatzResearch.WordTrace tailWord_202045 prefixEnd_202045 15369807235224775067899 := by
  unfold tailWord_202045
  simp only [CollatzResearch.WordTrace]
  refine ⟨7369186553032946383903589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4912791035355297589269059 7369186553032946383903589)
  ·
    refine ⟨1381722478693677446981923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7369186553032946383903589 1381722478693677446981923)
    ·
      refine ⟨2072583718040516170472885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1381722478693677446981923 2072583718040516170472885)
      ·
        refine ⟨194304723566298390981833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2072583718040516170472885 194304723566298390981833)
        ·
          refine ⟨145728542674723793236375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194304723566298390981833 145728542674723793236375)
          ·
            refine ⟨218592814012085689854563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145728542674723793236375 218592814012085689854563)
            ·
              refine ⟨327889221018128534781845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218592814012085689854563 327889221018128534781845)
              ·
                refine ⟨15369807235224775067899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 327889221018128534781845 15369807235224775067899)
                ·
                  rfl

theorem cell21_202045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 6].length) (baseStart_202045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202045 prefixEnd_202045 := by exact prefixLift 202045
  have htrace : WordTrace (prefixWord ++ tailWord_202045) baseStart_202045 baseEnd_202045 := by
    simpa [prefixWord, tailWord_202045, baseEnd_202045] using wordTrace_append hprefix tailTrace_202045
  have hstable : (prefixWord ++ tailWord_202045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202045).length < 2 ^ (prefixWord ++ tailWord_202045).sum := by decide
  have hdescent : baseEnd_202045 < baseStart_202045 := by decide
  rcases family_descends (prefixWord ++ tailWord_202045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202090 : List Nat := [3, 1, 3, 3, 2, 2, 1, 2, 4]
def baseStart_202090 : Nat := 118140960795 + 202090 * 2 ^ 59
def prefixEnd_202090 : Nat := 4983230072969 + 3 ^ 40 * 202090 * 2
def baseEnd_202090 : Nat := 46119691318764246953605

theorem tailTrace_202090 : CollatzResearch.WordTrace tailWord_202090 prefixEnd_202090 46119691318764246953605 := by
  unfold tailWord_202090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1842706959467479767322931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4913885225246612712861149 1842706959467479767322931)
  ·
    refine ⟨2764060439201219650984397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1842706959467479767322931 2764060439201219650984397)
    ·
      refine ⟨1036522664700457369119149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2764060439201219650984397 1036522664700457369119149)
      ·
        refine ⟨388695999262671513419681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1036522664700457369119149 388695999262671513419681)
        ·
          refine ⟨291521999447003635064761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388695999262671513419681 291521999447003635064761)
          ·
            refine ⟨218641499585252726298571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291521999447003635064761 218641499585252726298571)
            ·
              refine ⟨327962249377879089447857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218641499585252726298571 327962249377879089447857)
              ·
                refine ⟨245971687033409317085893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327962249377879089447857 245971687033409317085893)
                ·
                  refine ⟨46119691318764246953605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245971687033409317085893 46119691318764246953605)
                  ·
                    rfl

theorem cell21_202090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_202090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202090 prefixEnd_202090 := by exact prefixLift 202090
  have htrace : WordTrace (prefixWord ++ tailWord_202090) baseStart_202090 baseEnd_202090 := by
    simpa [prefixWord, tailWord_202090, baseEnd_202090] using wordTrace_append hprefix tailTrace_202090
  have hstable : (prefixWord ++ tailWord_202090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202090).length < 2 ^ (prefixWord ++ tailWord_202090).sum := by decide
  have hdescent : baseEnd_202090 < baseStart_202090 := by decide
  rcases family_descends (prefixWord ++ tailWord_202090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202129 : List Nat := [1, 2, 2, 1, 1, 1, 2, 11]
def baseStart_202129 : Nat := 118140960795 + 202129 * 2 ^ 59
def prefixEnd_202129 : Nat := 4983230072969 + 3 ^ 40 * 202129 * 2
def baseEnd_202129 : Nat := 15376197216702948601175

theorem tailTrace_202129 : CollatzResearch.WordTrace tailWord_202129 prefixEnd_202129 15376197216702948601175 := by
  unfold tailWord_202129
  simp only [CollatzResearch.WordTrace]
  refine ⟨7372250284728628729961441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4914833523152419153307627 7372250284728628729961441)
  ·
    refine ⟨5529187713546471547471081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7372250284728628729961441 5529187713546471547471081)
    ·
      refine ⟨4146890785159853660603311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5529187713546471547471081 4146890785159853660603311)
      ·
        refine ⟨6220336177739780490904967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4146890785159853660603311 6220336177739780490904967)
        ·
          refine ⟨9330504266609670736357451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6220336177739780490904967 9330504266609670736357451)
          ·
            refine ⟨13995756399914506104536177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9330504266609670736357451 13995756399914506104536177)
            ·
              refine ⟨10496817299935879578402133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13995756399914506104536177 10496817299935879578402133)
              ·
                refine ⟨15376197216702948601175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 10496817299935879578402133 15376197216702948601175)
                ·
                  rfl

theorem cell21_202129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 11].length) (baseStart_202129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202129 prefixEnd_202129 := by exact prefixLift 202129
  have htrace : WordTrace (prefixWord ++ tailWord_202129) baseStart_202129 baseEnd_202129 := by
    simpa [prefixWord, tailWord_202129, baseEnd_202129] using wordTrace_append hprefix tailTrace_202129
  have hstable : (prefixWord ++ tailWord_202129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202129).length < 2 ^ (prefixWord ++ tailWord_202129).sum := by decide
  have hdescent : baseEnd_202129 < baseStart_202129 := by decide
  rcases family_descends (prefixWord ++ tailWord_202129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202132 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 6]
def baseStart_202132 : Nat := 118140960795 + 202132 * 2 ^ 59
def prefixEnd_202132 : Nat := 4983230072969 + 3 ^ 40 * 202132 * 2
def baseEnd_202132 : Nat := 46129276290981507253519

theorem tailTrace_202132 : CollatzResearch.WordTrace tailWord_202132 prefixEnd_202132 46129276290981507253519 := by
  unfold tailWord_202132
  simp only [CollatzResearch.WordTrace]
  refine ⟨3686179851858880121160325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4914906469145173494880433 3686179851858880121160325)
  ·
    refine ⟨691158722223540022717561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3686179851858880121160325 691158722223540022717561)
    ·
      refine ⟨518369041667655017038171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 691158722223540022717561 518369041667655017038171)
      ·
        refine ⟨777553562501482525557257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518369041667655017038171 777553562501482525557257)
        ·
          refine ⟨583165171876111894167943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 777553562501482525557257 583165171876111894167943)
          ·
            refine ⟨874747757814167841251915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583165171876111894167943 874747757814167841251915)
            ·
              refine ⟨1312121636721251761877873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874747757814167841251915 1312121636721251761877873)
              ·
                refine ⟨984091227540938821408405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1312121636721251761877873 984091227540938821408405)
                ·
                  refine ⟨46129276290981507253519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 984091227540938821408405 46129276290981507253519)
                  ·
                    rfl

theorem cell21_202132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_202132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202132 prefixEnd_202132 := by exact prefixLift 202132
  have htrace : WordTrace (prefixWord ++ tailWord_202132) baseStart_202132 baseEnd_202132 := by
    simpa [prefixWord, tailWord_202132, baseEnd_202132] using wordTrace_append hprefix tailTrace_202132
  have hstable : (prefixWord ++ tailWord_202132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202132).length < 2 ^ (prefixWord ++ tailWord_202132).sum := by decide
  have hdescent : baseEnd_202132 < baseStart_202132 := by decide
  rcases family_descends (prefixWord ++ tailWord_202132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202146 : List Nat := [3, 3, 1, 2, 1, 2, 9]
def baseStart_202146 : Nat := 118140960795 + 202146 * 2 ^ 59
def prefixEnd_202146 : Nat := 4983230072969 + 3 ^ 40 * 202146 * 2
def baseEnd_202146 : Nat := 5125830142413399335573

theorem tailTrace_202146 : CollatzResearch.WordTrace tailWord_202146 prefixEnd_202146 5125830142413399335573 := by
  unfold tailWord_202146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1843217581416760158332573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4915246883778027088886861 1843217581416760158332573)
  ·
    refine ⟨691206593031285059374715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1843217581416760158332573 691206593031285059374715)
    ·
      refine ⟨1036809889546927589062073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 691206593031285059374715 1036809889546927589062073)
      ·
        refine ⟨777607417160195691796555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1036809889546927589062073 777607417160195691796555)
        ·
          refine ⟨1166411125740293537694833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777607417160195691796555 1166411125740293537694833)
          ·
            refine ⟨874808344305220153271125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1166411125740293537694833 874808344305220153271125)
            ·
              refine ⟨5125830142413399335573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 874808344305220153271125 5125830142413399335573)
              ·
                rfl

theorem cell21_202146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 9].length) (baseStart_202146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202146 prefixEnd_202146 := by exact prefixLift 202146
  have htrace : WordTrace (prefixWord ++ tailWord_202146) baseStart_202146 baseEnd_202146 := by
    simpa [prefixWord, tailWord_202146, baseEnd_202146] using wordTrace_append hprefix tailTrace_202146
  have hstable : (prefixWord ++ tailWord_202146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202146).length < 2 ^ (prefixWord ++ tailWord_202146).sum := by decide
  have hdescent : baseEnd_202146 < baseStart_202146 := by decide
  rcases family_descends (prefixWord ++ tailWord_202146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202152 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 5]
def baseStart_202152 : Nat := 118140960795 + 202152 * 2 ^ 59
def prefixEnd_202152 : Nat := 4983230072969 + 3 ^ 40 * 202152 * 2
def baseEnd_202152 : Nat := 46133840563465916920145

theorem tailTrace_202152 : CollatzResearch.WordTrace tailWord_202152 prefixEnd_202152 46133840563465916920145 := by
  unfold tailWord_202152
  simp only [CollatzResearch.WordTrace]
  refine ⟨3686544581822651829024355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4915392775763535772032473 3686544581822651829024355)
  ·
    refine ⟨5529816872733977743536533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3686544581822651829024355 5529816872733977743536533)
    ·
      refine ⟨259210165909405206728275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5529816872733977743536533 259210165909405206728275)
      ·
        refine ⟨388815248864107810092413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259210165909405206728275 388815248864107810092413)
        ·
          refine ⟨145805718324040428784655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388815248864107810092413 145805718324040428784655)
          ·
            refine ⟨218708577486060643176983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145805718324040428784655 218708577486060643176983)
            ·
              refine ⟨328062866229090964765475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218708577486060643176983 328062866229090964765475)
              ·
                refine ⟨492094299343636447148213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328062866229090964765475 492094299343636447148213)
                ·
                  refine ⟨46133840563465916920145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 492094299343636447148213 46133840563465916920145)
                  ·
                    rfl

theorem cell21_202152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 5].length) (baseStart_202152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202152 prefixEnd_202152 := by exact prefixLift 202152
  have htrace : WordTrace (prefixWord ++ tailWord_202152) baseStart_202152 baseEnd_202152 := by
    simpa [prefixWord, tailWord_202152, baseEnd_202152] using wordTrace_append hprefix tailTrace_202152
  have hstable : (prefixWord ++ tailWord_202152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202152).length < 2 ^ (prefixWord ++ tailWord_202152).sum := by decide
  have hdescent : baseEnd_202152 < baseStart_202152 := by decide
  rcases family_descends (prefixWord ++ tailWord_202152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202160 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 5]
def baseStart_202160 : Nat := 118140960795 + 202160 * 2 ^ 59
def prefixEnd_202160 : Nat := 4983230072969 + 3 ^ 40 * 202160 * 2
def baseEnd_202160 : Nat := 46135666272459680786795

theorem tailTrace_202160 : CollatzResearch.WordTrace tailWord_202160 prefixEnd_202160 46135666272459680786795 := by
  unfold tailWord_202160
  simp only [CollatzResearch.WordTrace]
  refine ⟨3686690473808160512169967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4915587298410880682893289 3686690473808160512169967)
  ·
    refine ⟨5530035710712240768254951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3686690473808160512169967 5530035710712240768254951)
    ·
      refine ⟨8295053566068361152382427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5530035710712240768254951 8295053566068361152382427)
      ·
        refine ⟨12442580349102541728573641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8295053566068361152382427 12442580349102541728573641)
        ·
          refine ⟨9331935261826906296430231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12442580349102541728573641 9331935261826906296430231)
          ·
            refine ⟨13997902892740359444645347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9331935261826906296430231 13997902892740359444645347)
            ·
              refine ⟨20996854339110539166968021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13997902892740359444645347 20996854339110539166968021)
              ·
                refine ⟨492113773572903261725813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20996854339110539166968021 492113773572903261725813)
                ·
                  refine ⟨46135666272459680786795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 492113773572903261725813 46135666272459680786795)
                  ·
                    rfl

theorem cell21_202160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_202160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202160 prefixEnd_202160 := by exact prefixLift 202160
  have htrace : WordTrace (prefixWord ++ tailWord_202160) baseStart_202160 baseEnd_202160 := by
    simpa [prefixWord, tailWord_202160, baseEnd_202160] using wordTrace_append hprefix tailTrace_202160
  have hstable : (prefixWord ++ tailWord_202160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202160).length < 2 ^ (prefixWord ++ tailWord_202160).sum := by decide
  have hdescent : baseEnd_202160 < baseStart_202160 := by decide
  rcases family_descends (prefixWord ++ tailWord_202160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202211 : List Nat := [1, 1, 1, 6, 2, 1, 4, 2, 3]
def baseStart_202211 : Nat := 118140960795 + 202211 * 2 ^ 59
def prefixEnd_202211 : Nat := 4983230072969 + 3 ^ 40 * 202211 * 2
def baseEnd_202211 : Nat := 46147305167294925436691

theorem tailTrace_202211 : CollatzResearch.WordTrace tailWord_202211 prefixEnd_202211 46147305167294925436691 := by
  unfold tailWord_202211
  simp only [CollatzResearch.WordTrace]
  refine ⟨7375241070431556734446487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4916827380287704489630991 7375241070431556734446487)
  ·
    refine ⟨11062861605647335101669731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7375241070431556734446487 11062861605647335101669731)
    ·
      refine ⟨16594292408471002652504597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11062861605647335101669731 16594292408471002652504597)
      ·
        refine ⟨777857456647078249336153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16594292408471002652504597 777857456647078249336153)
        ·
          refine ⟨583393092485308687002115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 777857456647078249336153 583393092485308687002115)
          ·
            refine ⟨875089638727963030503173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583393092485308687002115 875089638727963030503173)
            ·
              refine ⟨164079307261493068219345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 875089638727963030503173 164079307261493068219345)
              ·
                refine ⟨123059480446119801164509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164079307261493068219345 123059480446119801164509)
                ·
                  refine ⟨46147305167294925436691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123059480446119801164509 46147305167294925436691)
                  ·
                    rfl

theorem cell21_202211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 3].length) (baseStart_202211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202211 prefixEnd_202211 := by exact prefixLift 202211
  have htrace : WordTrace (prefixWord ++ tailWord_202211) baseStart_202211 baseEnd_202211 := by
    simpa [prefixWord, tailWord_202211, baseEnd_202211] using wordTrace_append hprefix tailTrace_202211
  have hstable : (prefixWord ++ tailWord_202211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202211).length < 2 ^ (prefixWord ++ tailWord_202211).sum := by decide
  have hdescent : baseEnd_202211 < baseStart_202211 := by decide
  rcases family_descends (prefixWord ++ tailWord_202211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202236 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 7]
def baseStart_202236 : Nat := 118140960795 + 202236 * 2 ^ 59
def prefixEnd_202236 : Nat := 4983230072969 + 3 ^ 40 * 202236 * 2
def baseEnd_202236 : Nat := 46153010507900437519973

theorem tailTrace_202236 : CollatzResearch.WordTrace tailWord_202236 prefixEnd_202236 46153010507900437519973 := by
  unfold tailWord_202236
  simp only [CollatzResearch.WordTrace]
  refine ⟨3688076447670493002053281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4917435263560657336071041 3688076447670493002053281)
  ·
    refine ⟨2766057335752869751539961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3688076447670493002053281 2766057335752869751539961)
    ·
      refine ⟨2074543001814652313654971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2766057335752869751539961 2074543001814652313654971)
      ·
        refine ⟨3111814502721978470482457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2074543001814652313654971 3111814502721978470482457)
        ·
          refine ⟨2333860877041483852861843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3111814502721978470482457 2333860877041483852861843)
          ·
            refine ⟨3500791315562225779292765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2333860877041483852861843 3500791315562225779292765)
            ·
              refine ⟨1312796743335834667234787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3500791315562225779292765 1312796743335834667234787)
              ·
                refine ⟨1969195115003752000852181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1312796743335834667234787 1969195115003752000852181)
                ·
                  refine ⟨46153010507900437519973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1969195115003752000852181 46153010507900437519973)
                  ·
                    rfl

theorem cell21_202236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_202236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202236 prefixEnd_202236 := by exact prefixLift 202236
  have htrace : WordTrace (prefixWord ++ tailWord_202236) baseStart_202236 baseEnd_202236 := by
    simpa [prefixWord, tailWord_202236, baseEnd_202236] using wordTrace_append hprefix tailTrace_202236
  have hstable : (prefixWord ++ tailWord_202236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202236).length < 2 ^ (prefixWord ++ tailWord_202236).sum := by decide
  have hdescent : baseEnd_202236 < baseStart_202236 := by decide
  rcases family_descends (prefixWord ++ tailWord_202236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202329 : List Nat := [1, 2, 1, 2, 2, 1, 1, 8, 3]
def baseStart_202329 : Nat := 118140960795 + 202329 * 2 ^ 59
def prefixEnd_202329 : Nat := 4983230072969 + 3 ^ 40 * 202329 * 2
def baseEnd_202329 : Nat := 46174234374952942469783

theorem tailTrace_202329 : CollatzResearch.WordTrace tailWord_202329 prefixEnd_202329 46174234374952942469783 := by
  unfold tailWord_202329
  simp only [CollatzResearch.WordTrace]
  refine ⟨7379544884004062887242041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4919696589336041924828027 7379544884004062887242041)
  ·
    refine ⟨5534658663003047165431531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7379544884004062887242041 5534658663003047165431531)
    ·
      refine ⟨8301987994504570748147297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5534658663003047165431531 8301987994504570748147297)
      ·
        refine ⟨6226490995878428061110473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8301987994504570748147297 6226490995878428061110473)
        ·
          refine ⟨4669868246908821045832855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6226490995878428061110473 4669868246908821045832855)
          ·
            refine ⟨7004802370363231568749283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4669868246908821045832855 7004802370363231568749283)
            ·
              refine ⟨10507203555544847353123925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7004802370363231568749283 10507203555544847353123925)
              ·
                refine ⟨123131291666541179919421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10507203555544847353123925 123131291666541179919421)
                ·
                  refine ⟨46174234374952942469783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123131291666541179919421 46174234374952942469783)
                  ·
                    rfl

theorem cell21_202329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 3].length) (baseStart_202329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202329 prefixEnd_202329 := by exact prefixLift 202329
  have htrace : WordTrace (prefixWord ++ tailWord_202329) baseStart_202329 baseEnd_202329 := by
    simpa [prefixWord, tailWord_202329, baseEnd_202329] using wordTrace_append hprefix tailTrace_202329
  have hstable : (prefixWord ++ tailWord_202329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202329).length < 2 ^ (prefixWord ++ tailWord_202329).sum := by decide
  have hdescent : baseEnd_202329 < baseStart_202329 := by decide
  rcases family_descends (prefixWord ++ tailWord_202329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202464 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 5]
def baseStart_202464 : Nat := 118140960795 + 202464 * 2 ^ 59
def prefixEnd_202464 : Nat := 4983230072969 + 3 ^ 40 * 202464 * 2
def baseEnd_202464 : Nat := 46205043214222707719507

theorem tailTrace_202464 : CollatzResearch.WordTrace tailWord_202464 prefixEnd_202464 46205043214222707719507 := by
  unfold tailWord_202464
  simp only [CollatzResearch.WordTrace]
  refine ⟨3692234369257490471703223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4922979159009987295604297 3692234369257490471703223)
  ·
    refine ⟨5538351553886235707554835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3692234369257490471703223 5538351553886235707554835)
    ·
      refine ⟨8307527330829353561332253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5538351553886235707554835 8307527330829353561332253)
      ·
        refine ⟨3115322749061007585499595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8307527330829353561332253 3115322749061007585499595)
        ·
          refine ⟨4672984123591511378249393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3115322749061007585499595 4672984123591511378249393)
          ·
            refine ⟨3504738092693633533687045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4672984123591511378249393 3504738092693633533687045)
            ·
              refine ⟨657138392380056287566321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3504738092693633533687045 657138392380056287566321)
              ·
                refine ⟨492853794285042215674741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 657138392380056287566321 492853794285042215674741)
                ·
                  refine ⟨46205043214222707719507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 492853794285042215674741 46205043214222707719507)
                  ·
                    rfl

theorem cell21_202464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_202464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202464 prefixEnd_202464 := by exact prefixLift 202464
  have htrace : WordTrace (prefixWord ++ tailWord_202464) baseStart_202464 baseEnd_202464 := by
    simpa [prefixWord, tailWord_202464, baseEnd_202464] using wordTrace_append hprefix tailTrace_202464
  have hstable : (prefixWord ++ tailWord_202464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202464).length < 2 ^ (prefixWord ++ tailWord_202464).sum := by decide
  have hdescent : baseEnd_202464 < baseStart_202464 := by decide
  rcases family_descends (prefixWord ++ tailWord_202464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202484 : List Nat := [2, 6, 1, 1, 1, 3, 7]
def baseStart_202484 : Nat := 118140960795 + 202484 * 2 ^ 59
def prefixEnd_202484 : Nat := 4983230072969 + 3 ^ 40 * 202484 * 2
def baseEnd_202484 : Nat := 5134400831856346376237

theorem tailTrace_202484 : CollatzResearch.WordTrace tailWord_202484 prefixEnd_202484 5134400831856346376237 := by
  unfold tailWord_202484
  simp only [CollatzResearch.WordTrace]
  refine ⟨3692599099221262179567253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4923465465628349572756337 3692599099221262179567253)
  ·
    refine ⟨173090582775996664667215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3692599099221262179567253 173090582775996664667215)
    ·
      refine ⟨259635874163994997000823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173090582775996664667215 259635874163994997000823)
      ·
        refine ⟨389453811245992495501235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259635874163994997000823 389453811245992495501235)
        ·
          refine ⟨584180716868988743251853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389453811245992495501235 584180716868988743251853)
          ·
            refine ⟨219067768825870778719445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 584180716868988743251853 219067768825870778719445)
            ·
              refine ⟨5134400831856346376237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 219067768825870778719445 5134400831856346376237)
              ·
                rfl

theorem cell21_202484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 7].length) (baseStart_202484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202484 prefixEnd_202484 := by exact prefixLift 202484
  have htrace : WordTrace (prefixWord ++ tailWord_202484) baseStart_202484 baseEnd_202484 := by
    simpa [prefixWord, tailWord_202484, baseEnd_202484] using wordTrace_append hprefix tailTrace_202484
  have hstable : (prefixWord ++ tailWord_202484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202484).length < 2 ^ (prefixWord ++ tailWord_202484).sum := by decide
  have hdescent : baseEnd_202484 < baseStart_202484 := by decide
  rcases family_descends (prefixWord ++ tailWord_202484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202622 : List Nat := [4, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_202622 : Nat := 118140960795 + 202622 * 2 ^ 59
def prefixEnd_202622 : Nat := 4983230072969 + 3 ^ 40 * 202622 * 2
def baseEnd_202622 : Nat := 46241100966849544085851

theorem tailTrace_202622 : CollatzResearch.WordTrace tailWord_202622 prefixEnd_202622 46241100966849544085851 := by
  unfold tailWord_202622
  simp only [CollatzResearch.WordTrace]
  refine ⟨923778933992821740957265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4926820981295049285105413 923778933992821740957265)
  ·
    refine ⟨692834200494616305717949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 923778933992821740957265 692834200494616305717949)
    ·
      refine ⟨259812825185481114644231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 692834200494616305717949 259812825185481114644231)
      ·
        refine ⟨389719237778221671966347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259812825185481114644231 389719237778221671966347)
        ·
          refine ⟨584578856667332507949521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389719237778221671966347 584578856667332507949521)
          ·
            refine ⟨438434142500499380962141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 584578856667332507949521 438434142500499380962141)
            ·
              refine ⟨164412803437687267860803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 438434142500499380962141 164412803437687267860803)
              ·
                refine ⟨246619205156530901791205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164412803437687267860803 246619205156530901791205)
                ·
                  refine ⟨46241100966849544085851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246619205156530901791205 46241100966849544085851)
                  ·
                    rfl

theorem cell21_202622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_202622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202622 prefixEnd_202622 := by exact prefixLift 202622
  have htrace : WordTrace (prefixWord ++ tailWord_202622) baseStart_202622 baseEnd_202622 := by
    simpa [prefixWord, tailWord_202622, baseEnd_202622] using wordTrace_append hprefix tailTrace_202622
  have hstable : (prefixWord ++ tailWord_202622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202622).length < 2 ^ (prefixWord ++ tailWord_202622).sum := by decide
  have hdescent : baseEnd_202622 < baseStart_202622 := by decide
  rcases family_descends (prefixWord ++ tailWord_202622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202650 : List Nat := [3, 1, 1, 4, 2, 1, 3, 3, 3]
def baseStart_202650 : Nat := 118140960795 + 202650 * 2 ^ 59
def prefixEnd_202650 : Nat := 4983230072969 + 3 ^ 40 * 202650 * 2
def baseEnd_202650 : Nat := 46247490948327717619127

theorem tailTrace_202650 : CollatzResearch.WordTrace tailWord_202650 prefixEnd_202650 46247490948327717619127 := by
  unfold tailWord_202650
  simp only [CollatzResearch.WordTrace]
  refine ⟨1847813178960283677419351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4927501810560756473118269 1847813178960283677419351)
  ·
    refine ⟨2771719768440425516129027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1847813178960283677419351 2771719768440425516129027)
    ·
      refine ⟨4157579652660638274193541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2771719768440425516129027 4157579652660638274193541)
      ·
        refine ⟨779546184873869676411289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4157579652660638274193541 779546184873869676411289)
        ·
          refine ⟨584659638655402257308467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 779546184873869676411289 584659638655402257308467)
          ·
            refine ⟨876989457983103385962701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584659638655402257308467 876989457983103385962701)
            ·
              refine ⟨328871046743663769736013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 876989457983103385962701 328871046743663769736013)
              ·
                refine ⟨123326642528873913651005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328871046743663769736013 123326642528873913651005)
                ·
                  refine ⟨46247490948327717619127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123326642528873913651005 46247490948327717619127)
                  ·
                    rfl

theorem cell21_202650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_202650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202650 prefixEnd_202650 := by exact prefixLift 202650
  have htrace : WordTrace (prefixWord ++ tailWord_202650) baseStart_202650 baseEnd_202650 := by
    simpa [prefixWord, tailWord_202650, baseEnd_202650] using wordTrace_append hprefix tailTrace_202650
  have hstable : (prefixWord ++ tailWord_202650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202650).length < 2 ^ (prefixWord ++ tailWord_202650).sum := by decide
  have hdescent : baseEnd_202650 < baseStart_202650 := by decide
  rcases family_descends (prefixWord ++ tailWord_202650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202723 : List Nat := [1, 1, 1, 6, 1, 2, 1, 4, 4]
def baseStart_202723 : Nat := 118140960795 + 202723 * 2 ^ 59
def prefixEnd_202723 : Nat := 4983230072969 + 3 ^ 40 * 202723 * 2
def baseEnd_202723 : Nat := 46264150542895812902311

theorem tailTrace_202723 : CollatzResearch.WordTrace tailWord_202723 prefixEnd_202723 46264150542895812902311 := by
  unfold tailWord_202723
  simp only [CollatzResearch.WordTrace]
  refine ⟨7393915244576668177084823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4929276829717778784723215 7393915244576668177084823)
  ·
    refine ⟨11090872866865002265627235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7393915244576668177084823 11090872866865002265627235)
    ·
      refine ⟨16636309300297503398440853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11090872866865002265627235 16636309300297503398440853)
      ·
        refine ⟨779826998451445471801915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16636309300297503398440853 779826998451445471801915)
        ·
          refine ⟨1169740497677168207702873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779826998451445471801915 1169740497677168207702873)
          ·
            refine ⟨877305373257876155777155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1169740497677168207702873 877305373257876155777155)
            ·
              refine ⟨1315958059886814233665733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877305373257876155777155 1315958059886814233665733)
              ·
                refine ⟨246742136228777668812325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1315958059886814233665733 246742136228777668812325)
                ·
                  refine ⟨46264150542895812902311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246742136228777668812325 46264150542895812902311)
                  ·
                    rfl

theorem cell21_202723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 4].length) (baseStart_202723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202723 prefixEnd_202723 := by exact prefixLift 202723
  have htrace : WordTrace (prefixWord ++ tailWord_202723) baseStart_202723 baseEnd_202723 := by
    simpa [prefixWord, tailWord_202723, baseEnd_202723] using wordTrace_append hprefix tailTrace_202723
  have hstable : (prefixWord ++ tailWord_202723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202723).length < 2 ^ (prefixWord ++ tailWord_202723).sum := by decide
  have hdescent : baseEnd_202723 < baseStart_202723 := by decide
  rcases family_descends (prefixWord ++ tailWord_202723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202785 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 5]
def baseStart_202785 : Nat := 118140960795 + 202785 * 2 ^ 59
def prefixEnd_202785 : Nat := 4983230072969 + 3 ^ 40 * 202785 * 2
def baseEnd_202785 : Nat := 46278299787597482868851

theorem tailTrace_202785 : CollatzResearch.WordTrace tailWord_202785 prefixEnd_202785 46278299787597482868851 := by
  unfold tailWord_202785
  simp only [CollatzResearch.WordTrace]
  refine ⟨7396176570352052765841809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4930784380234701843894539 7396176570352052765841809)
  ·
    refine ⟨5547132427764039574381357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7396176570352052765841809 5547132427764039574381357)
    ·
      refine ⟨2080174660411514840393009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5547132427764039574381357 2080174660411514840393009)
      ·
        refine ⟨1560130995308636130294757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2080174660411514840393009 1560130995308636130294757)
        ·
          refine ⟨292524561620369274430267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1560130995308636130294757 292524561620369274430267)
          ·
            refine ⟨438786842430553911645401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292524561620369274430267 438786842430553911645401)
            ·
              refine ⟨329090131822915433734051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438786842430553911645401 329090131822915433734051)
              ·
                refine ⟨493635197734373150601077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329090131822915433734051 493635197734373150601077)
                ·
                  refine ⟨46278299787597482868851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 493635197734373150601077 46278299787597482868851)
                  ·
                    rfl

theorem cell21_202785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_202785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202785 prefixEnd_202785 := by exact prefixLift 202785
  have htrace : WordTrace (prefixWord ++ tailWord_202785) baseStart_202785 baseEnd_202785 := by
    simpa [prefixWord, tailWord_202785, baseEnd_202785] using wordTrace_append hprefix tailTrace_202785
  have hstable : (prefixWord ++ tailWord_202785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202785).length < 2 ^ (prefixWord ++ tailWord_202785).sum := by decide
  have hdescent : baseEnd_202785 < baseStart_202785 := by decide
  rcases family_descends (prefixWord ++ tailWord_202785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202813 : List Nat := [1, 4, 1, 3, 1, 1, 3, 7]
def baseStart_202813 : Nat := 118140960795 + 202813 * 2 ^ 59
def prefixEnd_202813 : Nat := 4983230072969 + 3 ^ 40 * 202813 * 2
def baseEnd_202813 : Nat := 15428229923025218800709

theorem tailTrace_202813 : CollatzResearch.WordTrace tailWord_202813 prefixEnd_202813 15428229923025218800709 := by
  unfold tailWord_202813
  simp only [CollatzResearch.WordTrace]
  refine ⟨7397197814250613547861093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4931465209500409031907395 7397197814250613547861093)
  ·
    refine ⟨1386974590171990040223955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7397197814250613547861093 1386974590171990040223955)
    ·
      refine ⟨2080461885257985060335933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1386974590171990040223955 2080461885257985060335933)
      ·
        refine ⟨780173206971744397625975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2080461885257985060335933 780173206971744397625975)
        ·
          refine ⟨1170259810457616596438963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780173206971744397625975 1170259810457616596438963)
          ·
            refine ⟨1755389715686424894658445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170259810457616596438963 1755389715686424894658445)
            ·
              refine ⟨658271143382409335496917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1755389715686424894658445 658271143382409335496917)
              ·
                refine ⟨15428229923025218800709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 658271143382409335496917 15428229923025218800709)
                ·
                  rfl

theorem cell21_202813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 7].length) (baseStart_202813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202813 prefixEnd_202813 := by exact prefixLift 202813
  have htrace : WordTrace (prefixWord ++ tailWord_202813) baseStart_202813 baseEnd_202813 := by
    simpa [prefixWord, tailWord_202813, baseEnd_202813] using wordTrace_append hprefix tailTrace_202813
  have hstable : (prefixWord ++ tailWord_202813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202813).length < 2 ^ (prefixWord ++ tailWord_202813).sum := by decide
  have hdescent : baseEnd_202813 < baseStart_202813 := by decide
  rcases family_descends (prefixWord ++ tailWord_202813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202850 : List Nat := [3, 3, 2, 2, 2, 2, 2, 1, 4]
def baseStart_202850 : Nat := 118140960795 + 202850 * 2 ^ 59
def prefixEnd_202850 : Nat := 4983230072969 + 3 ^ 40 * 202850 * 2
def baseEnd_202850 : Nat := 46293133673171814285385

theorem tailTrace_202850 : CollatzResearch.WordTrace tailWord_202850 prefixEnd_202850 46293133673171814285385 := by
  unfold tailWord_202850
  simp only [CollatzResearch.WordTrace]
  refine ⟨1849636828779142216739501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4932364876744379244638669 1849636828779142216739501)
  ·
    refine ⟨693613810792178331277313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1849636828779142216739501 693613810792178331277313)
    ·
      refine ⟨520210358094133748457985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 693613810792178331277313 520210358094133748457985)
      ·
        refine ⟨390157768570600311343489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520210358094133748457985 390157768570600311343489)
        ·
          refine ⟨292618326427950233507617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390157768570600311343489 292618326427950233507617)
          ·
            refine ⟨219463744820962675130713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292618326427950233507617 219463744820962675130713)
            ·
              refine ⟨164597808615722006348035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219463744820962675130713 164597808615722006348035)
              ·
                refine ⟨246896712923583009522053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164597808615722006348035 246896712923583009522053)
                ·
                  refine ⟨46293133673171814285385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246896712923583009522053 46293133673171814285385)
                  ·
                    rfl

theorem cell21_202850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_202850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202850 prefixEnd_202850 := by exact prefixLift 202850
  have htrace : WordTrace (prefixWord ++ tailWord_202850) baseStart_202850 baseEnd_202850 := by
    simpa [prefixWord, tailWord_202850, baseEnd_202850] using wordTrace_append hprefix tailTrace_202850
  have hstable : (prefixWord ++ tailWord_202850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202850).length < 2 ^ (prefixWord ++ tailWord_202850).sum := by decide
  have hdescent : baseEnd_202850 < baseStart_202850 := by decide
  rcases family_descends (prefixWord ++ tailWord_202850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202937 : List Nat := [1, 2, 1, 4, 1, 2, 4, 3, 3]
def baseStart_202937 : Nat := 118140960795 + 202937 * 2 ^ 59
def prefixEnd_202937 : Nat := 4983230072969 + 3 ^ 40 * 202937 * 2
def baseEnd_202937 : Nat := 46312988258478996335207

theorem tailTrace_202937 : CollatzResearch.WordTrace tailWord_202937 prefixEnd_202937 46312988258478996335207 := by
  unfold tailWord_202937
  simp only [CollatzResearch.WordTrace]
  refine ⟨7401720465801382725375065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4934480310534255150250043 7401720465801382725375065)
  ·
    refine ⟨5551290349351037044031299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7401720465801382725375065 5551290349351037044031299)
    ·
      refine ⟨8326935524026555566046949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5551290349351037044031299 8326935524026555566046949)
      ·
        refine ⟨1561300410754979168633803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8326935524026555566046949 1561300410754979168633803)
        ·
          refine ⟨2341950616132468752950705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1561300410754979168633803 2341950616132468752950705)
          ·
            refine ⟨1756462962099351564713029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2341950616132468752950705 1756462962099351564713029)
            ·
              refine ⟨329336805393628418383693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1756462962099351564713029 329336805393628418383693)
              ·
                refine ⟨123501302022610656893885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329336805393628418383693 123501302022610656893885)
                ·
                  refine ⟨46312988258478996335207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123501302022610656893885 46312988258478996335207)
                  ·
                    rfl

theorem cell21_202937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 3].length) (baseStart_202937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202937 prefixEnd_202937 := by exact prefixLift 202937
  have htrace : WordTrace (prefixWord ++ tailWord_202937) baseStart_202937 baseEnd_202937 := by
    simpa [prefixWord, tailWord_202937, baseEnd_202937] using wordTrace_append hprefix tailTrace_202937
  have hstable : (prefixWord ++ tailWord_202937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202937).length < 2 ^ (prefixWord ++ tailWord_202937).sum := by decide
  have hdescent : baseEnd_202937 < baseStart_202937 := by decide
  rcases family_descends (prefixWord ++ tailWord_202937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202968 : List Nat := [2, 1, 2, 2, 4, 2, 3, 1, 4]
def baseStart_202968 : Nat := 118140960795 + 202968 * 2 ^ 59
def prefixEnd_202968 : Nat := 4983230072969 + 3 ^ 40 * 202968 * 2
def baseEnd_202968 : Nat := 46320062880829831318477

theorem tailTrace_202968 : CollatzResearch.WordTrace tailWord_202968 prefixEnd_202968 46320062880829831318477 := by
  unfold tailWord_202968
  simp only [CollatzResearch.WordTrace]
  refine ⟨3701425564344537509876779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4935234085792716679835705 3701425564344537509876779)
  ·
    refine ⟨5552138346516806264815169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3701425564344537509876779 5552138346516806264815169)
    ·
      refine ⟨4164103759887604698611377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5552138346516806264815169 4164103759887604698611377)
      ·
        refine ⟨3123077819915703523958533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4164103759887604698611377 3123077819915703523958533)
        ·
          refine ⟨585577091234194410742225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3123077819915703523958533 585577091234194410742225)
          ·
            refine ⟨439182818425645808056669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585577091234194410742225 439182818425645808056669)
            ·
              refine ⟨164693556909617178021251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 439182818425645808056669 164693556909617178021251)
              ·
                refine ⟨247040335364425767031877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164693556909617178021251 247040335364425767031877)
                ·
                  refine ⟨46320062880829831318477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247040335364425767031877 46320062880829831318477)
                  ·
                    rfl

theorem cell21_202968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 4].length) (baseStart_202968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_202968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_202968 prefixEnd_202968 := by exact prefixLift 202968
  have htrace : WordTrace (prefixWord ++ tailWord_202968) baseStart_202968 baseEnd_202968 := by
    simpa [prefixWord, tailWord_202968, baseEnd_202968] using wordTrace_append hprefix tailTrace_202968
  have hstable : (prefixWord ++ tailWord_202968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202968).length < 2 ^ (prefixWord ++ tailWord_202968).sum := by decide
  have hdescent : baseEnd_202968 < baseStart_202968 := by decide
  rcases family_descends (prefixWord ++ tailWord_202968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203106 : List Nat := [3, 3, 2, 1, 1, 3, 2, 3, 3]
def baseStart_203106 : Nat := 118140960795 + 203106 * 2 ^ 59
def prefixEnd_203106 : Nat := 4983230072969 + 3 ^ 40 * 203106 * 2
def baseEnd_203106 : Nat := 46351556360972258018195

theorem tailTrace_203106 : CollatzResearch.WordTrace tailWord_203106 prefixEnd_203106 46351556360972258018195 := by
  unfold tailWord_203106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1851971100547281147069293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4938589601459416392184781 1851971100547281147069293)
  ·
    refine ⟨694489162705230430150985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1851971100547281147069293 694489162705230430150985)
    ·
      refine ⟨520866872028922822613239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 694489162705230430150985 520866872028922822613239)
      ·
        refine ⟨781300308043384233919859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520866872028922822613239 781300308043384233919859)
        ·
          refine ⟨1171950462065076350879789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781300308043384233919859 1171950462065076350879789)
          ·
            refine ⟨439481423274403631579921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1171950462065076350879789 439481423274403631579921)
            ·
              refine ⟨329611067455802723684941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439481423274403631579921 329611067455802723684941)
              ·
                refine ⟨123604150295926021381853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329611067455802723684941 123604150295926021381853)
                ·
                  refine ⟨46351556360972258018195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123604150295926021381853 46351556360972258018195)
                  ·
                    rfl

theorem cell21_203106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_203106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203106 prefixEnd_203106 := by exact prefixLift 203106
  have htrace : WordTrace (prefixWord ++ tailWord_203106) baseStart_203106 baseEnd_203106 := by
    simpa [prefixWord, tailWord_203106, baseEnd_203106] using wordTrace_append hprefix tailTrace_203106
  have hstable : (prefixWord ++ tailWord_203106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203106).length < 2 ^ (prefixWord ++ tailWord_203106).sum := by decide
  have hdescent : baseEnd_203106 < baseStart_203106 := by decide
  rcases family_descends (prefixWord ++ tailWord_203106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203131 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 5]
def baseStart_203131 : Nat := 118140960795 + 203131 * 2 ^ 59
def prefixEnd_203131 : Nat := 4983230072969 + 3 ^ 40 * 203131 * 2
def baseEnd_203131 : Nat := 46357261701577770101477

theorem tailTrace_203131 : CollatzResearch.WordTrace tailWord_203131 prefixEnd_203131 46357261701577770101477 := by
  unfold tailWord_203131
  simp only [CollatzResearch.WordTrace]
  refine ⟨7408796227098553857937247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4939197484732369238624831 7408796227098553857937247)
  ·
    refine ⟨11113194340647830786905871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7408796227098553857937247 11113194340647830786905871)
    ·
      refine ⟨16669791510971746180358807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11113194340647830786905871 16669791510971746180358807)
      ·
        refine ⟨25004687266457619270538211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16669791510971746180358807 25004687266457619270538211)
        ·
          refine ⟨37507030899686428905807317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25004687266457619270538211 37507030899686428905807317)
          ·
            refine ⟨879071036711400677479859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 37507030899686428905807317 879071036711400677479859)
            ·
              refine ⟨1318606555067101016219789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879071036711400677479859 1318606555067101016219789)
              ·
                refine ⟨494477458150162881082421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1318606555067101016219789 494477458150162881082421)
                ·
                  refine ⟨46357261701577770101477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 494477458150162881082421 46357261701577770101477)
                  ·
                    rfl

theorem cell21_203131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 5].length) (baseStart_203131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203131 prefixEnd_203131 := by exact prefixLift 203131
  have htrace : WordTrace (prefixWord ++ tailWord_203131) baseStart_203131 baseEnd_203131 := by
    simpa [prefixWord, tailWord_203131, baseEnd_203131] using wordTrace_append hprefix tailTrace_203131
  have hstable : (prefixWord ++ tailWord_203131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203131).length < 2 ^ (prefixWord ++ tailWord_203131).sum := by decide
  have hdescent : baseEnd_203131 < baseStart_203131 := by decide
  rcases family_descends (prefixWord ++ tailWord_203131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203162 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 6]
def baseStart_203162 : Nat := 118140960795 + 203162 * 2 ^ 59
def prefixEnd_203162 : Nat := 4983230072969 + 3 ^ 40 * 203162 * 2
def baseEnd_203162 : Nat := 46364336323928605084747

theorem tailTrace_203162 : CollatzResearch.WordTrace tailWord_203162 prefixEnd_203162 46364336323928605084747 := by
  unfold tailWord_203162
  simp only [CollatzResearch.WordTrace]
  refine ⟨1852481722496561538078935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4939951259990830768210493 1852481722496561538078935)
  ·
    refine ⟨2778722583744842307118403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1852481722496561538078935 2778722583744842307118403)
    ·
      refine ⟨4168083875617263460677605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2778722583744842307118403 4168083875617263460677605)
      ·
        refine ⟨781515726678236898877051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4168083875617263460677605 781515726678236898877051)
        ·
          refine ⟨1172273590017355348315577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781515726678236898877051 1172273590017355348315577)
          ·
            refine ⟨879205192513016511236683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1172273590017355348315577 879205192513016511236683)
            ·
              refine ⟨1318807788769524766855025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879205192513016511236683 1318807788769524766855025)
              ·
                refine ⟨989105841577143575141269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1318807788769524766855025 989105841577143575141269)
                ·
                  refine ⟨46364336323928605084747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 989105841577143575141269 46364336323928605084747)
                  ·
                    rfl

theorem cell21_203162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_203162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203162 prefixEnd_203162 := by exact prefixLift 203162
  have htrace : WordTrace (prefixWord ++ tailWord_203162) baseStart_203162 baseEnd_203162 := by
    simpa [prefixWord, tailWord_203162, baseEnd_203162] using wordTrace_append hprefix tailTrace_203162
  have hstable : (prefixWord ++ tailWord_203162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203162).length < 2 ^ (prefixWord ++ tailWord_203162).sum := by decide
  have hdescent : baseEnd_203162 < baseStart_203162 := by decide
  rcases family_descends (prefixWord ++ tailWord_203162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203193 : List Nat := [1, 2, 1, 4, 3, 2, 2, 6]
def baseStart_203193 : Nat := 118140960795 + 203193 * 2 ^ 59
def prefixEnd_203193 : Nat := 4983230072969 + 3 ^ 40 * 203193 * 2
def baseEnd_203193 : Nat := 15457136982093146689339

theorem tailTrace_203193 : CollatzResearch.WordTrace tailWord_203193 prefixEnd_203193 15457136982093146689339 := by
  unfold tailWord_203193
  simp only [CollatzResearch.WordTrace]
  refine ⟨7411057552873938446694233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4940705035249292297796155 7411057552873938446694233)
  ·
    refine ⟨5558293164655453835020675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7411057552873938446694233 5558293164655453835020675)
    ·
      refine ⟨8337439746983180752531013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5558293164655453835020675 8337439746983180752531013)
      ·
        refine ⟨1563269952559346391099565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8337439746983180752531013 1563269952559346391099565)
        ·
          refine ⟨586226232209754896662337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1563269952559346391099565 586226232209754896662337)
          ·
            refine ⟨439669674157316172496753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 586226232209754896662337 439669674157316172496753)
            ·
              refine ⟨329752255617987129372565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439669674157316172496753 329752255617987129372565)
              ·
                refine ⟨15457136982093146689339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 329752255617987129372565 15457136982093146689339)
                ·
                  rfl

theorem cell21_203193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 6].length) (baseStart_203193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203193 prefixEnd_203193 := by exact prefixLift 203193
  have htrace : WordTrace (prefixWord ++ tailWord_203193) baseStart_203193 baseEnd_203193 := by
    simpa [prefixWord, tailWord_203193, baseEnd_203193] using wordTrace_append hprefix tailTrace_203193
  have hstable : (prefixWord ++ tailWord_203193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203193).length < 2 ^ (prefixWord ++ tailWord_203193).sum := by decide
  have hdescent : baseEnd_203193 < baseStart_203193 := by decide
  rcases family_descends (prefixWord ++ tailWord_203193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203196 : List Nat := [2, 2, 2, 4, 1, 1, 4, 1, 4]
def baseStart_203196 : Nat := 118140960795 + 203196 * 2 ^ 59
def prefixEnd_203196 : Nat := 4983230072969 + 3 ^ 40 * 203196 * 2
def baseEnd_203196 : Nat := 46372095587152101518011

theorem tailTrace_203196 : CollatzResearch.WordTrace tailWord_203196 prefixEnd_203196 46372095587152101518011 := by
  unfold tailWord_203196
  simp only [CollatzResearch.WordTrace]
  refine ⟨3705583485931534979526721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4940777981242046639368961 3705583485931534979526721)
  ·
    refine ⟨2779187614448651234645041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3705583485931534979526721 2779187614448651234645041)
    ·
      refine ⟨2084390710836488425983781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2779187614448651234645041 2084390710836488425983781)
      ·
        refine ⟨390823258281841579871959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2084390710836488425983781 390823258281841579871959)
        ·
          refine ⟨586234887422762369807939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390823258281841579871959 586234887422762369807939)
          ·
            refine ⟨879352331134143554711909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586234887422762369807939 879352331134143554711909)
            ·
              refine ⟨164878562087651916508483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 879352331134143554711909 164878562087651916508483)
              ·
                refine ⟨247317843131477874762725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164878562087651916508483 247317843131477874762725)
                ·
                  refine ⟨46372095587152101518011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247317843131477874762725 46372095587152101518011)
                  ·
                    rfl

theorem cell21_203196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_203196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203196 prefixEnd_203196 := by exact prefixLift 203196
  have htrace : WordTrace (prefixWord ++ tailWord_203196) baseStart_203196 baseEnd_203196 := by
    simpa [prefixWord, tailWord_203196, baseEnd_203196] using wordTrace_append hprefix tailTrace_203196
  have hstable : (prefixWord ++ tailWord_203196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203196).length < 2 ^ (prefixWord ++ tailWord_203196).sum := by decide
  have hdescent : baseEnd_203196 < baseStart_203196 := by decide
  rcases family_descends (prefixWord ++ tailWord_203196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203224 : List Nat := [2, 1, 2, 2, 2, 1, 1, 7, 3]
def baseStart_203224 : Nat := 118140960795 + 203224 * 2 ^ 59
def prefixEnd_203224 : Nat := 4983230072969 + 3 ^ 40 * 203224 * 2
def baseEnd_203224 : Nat := 46378485568630275051287

theorem tailTrace_203224 : CollatzResearch.WordTrace tailWord_203224 prefixEnd_203224 46378485568630275051287 := by
  unfold tailWord_203224
  simp only [CollatzResearch.WordTrace]
  refine ⟨3706094107880815370536363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4941458810507753827381817 3706094107880815370536363)
  ·
    refine ⟨5559141161821223055804545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3706094107880815370536363 5559141161821223055804545)
    ·
      refine ⟨4169355871365917291853409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5559141161821223055804545 4169355871365917291853409)
      ·
        refine ⟨3127016903524437968890057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4169355871365917291853409 3127016903524437968890057)
        ·
          refine ⟨2345262677643328476667543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3127016903524437968890057 2345262677643328476667543)
          ·
            refine ⟨3517894016464992715001315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345262677643328476667543 3517894016464992715001315)
            ·
              refine ⟨5276841024697489072501973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517894016464992715001315 5276841024697489072501973)
              ·
                refine ⟨123675961516347400136765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5276841024697489072501973 123675961516347400136765)
                ·
                  refine ⟨46378485568630275051287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123675961516347400136765 46378485568630275051287)
                  ·
                    rfl

theorem cell21_203224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 3].length) (baseStart_203224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203224 prefixEnd_203224 := by exact prefixLift 203224
  have htrace : WordTrace (prefixWord ++ tailWord_203224) baseStart_203224 baseEnd_203224 := by
    simpa [prefixWord, tailWord_203224, baseEnd_203224] using wordTrace_append hprefix tailTrace_203224
  have hstable : (prefixWord ++ tailWord_203224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203224).length < 2 ^ (prefixWord ++ tailWord_203224).sum := by decide
  have hdescent : baseEnd_203224 < baseStart_203224 := by decide
  rcases family_descends (prefixWord ++ tailWord_203224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203314 : List Nat := [3, 2, 1, 1, 2, 1, 2, 5, 4]
def baseStart_203314 : Nat := 118140960795 + 203314 * 2 ^ 59
def prefixEnd_203314 : Nat := 4983230072969 + 3 ^ 40 * 203314 * 2
def baseEnd_203314 : Nat := 46399024794810118551103

theorem tailTrace_203314 : CollatzResearch.WordTrace tailWord_203314 prefixEnd_203314 46399024794810118551103 := by
  unfold tailWord_203314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853867696358894027962249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4943647190290384074565997 1853867696358894027962249)
  ·
    refine ⟨1390400772269170520971687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1853867696358894027962249 1390400772269170520971687)
    ·
      refine ⟨2085601158403755781457531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1390400772269170520971687 2085601158403755781457531)
      ·
        refine ⟨3128401737605633672186297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2085601158403755781457531 3128401737605633672186297)
        ·
          refine ⟨2346301303204225254139723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3128401737605633672186297 2346301303204225254139723)
          ·
            refine ⟨3519451954806337881209585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2346301303204225254139723 3519451954806337881209585)
            ·
              refine ⟨2639588966104753410907189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3519451954806337881209585 2639588966104753410907189)
              ·
                refine ⟨247461465572320632272549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2639588966104753410907189 247461465572320632272549)
                ·
                  refine ⟨46399024794810118551103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247461465572320632272549 46399024794810118551103)
                  ·
                    rfl

theorem cell21_203314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_203314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203314 prefixEnd_203314 := by exact prefixLift 203314
  have htrace : WordTrace (prefixWord ++ tailWord_203314) baseStart_203314 baseEnd_203314 := by
    simpa [prefixWord, tailWord_203314, baseEnd_203314] using wordTrace_append hprefix tailTrace_203314
  have hstable : (prefixWord ++ tailWord_203314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203314).length < 2 ^ (prefixWord ++ tailWord_203314).sum := by decide
  have hdescent : baseEnd_203314 < baseStart_203314 := by decide
  rcases family_descends (prefixWord ++ tailWord_203314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203365 : List Nat := [1, 3, 1, 3, 5, 1, 2, 1, 4]
def baseStart_203365 : Nat := 118140960795 + 203365 * 2 ^ 59
def prefixEnd_203365 : Nat := 4983230072969 + 3 ^ 40 * 203365 * 2
def baseEnd_203365 : Nat := 46410663689645363200999

theorem tailTrace_203365 : CollatzResearch.WordTrace tailWord_203365 prefixEnd_203365 46410663689645363200999 := by
  unfold tailWord_203365
  simp only [CollatzResearch.WordTrace]
  refine ⟨7417330908250811821955549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4944887272167207881303699 7417330908250811821955549)
  ·
    refine ⟨2781499090594054433233331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7417330908250811821955549 2781499090594054433233331)
    ·
      refine ⟨4172248635891081649849997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2781499090594054433233331 4172248635891081649849997)
      ·
        refine ⟨1564593238459155618693749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4172248635891081649849997 1564593238459155618693749)
        ·
          refine ⟨146680616105545839252539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1564593238459155618693749 146680616105545839252539)
          ·
            refine ⟨220020924158318758878809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146680616105545839252539 220020924158318758878809)
            ·
              refine ⟨165015693118739069159107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220020924158318758878809 165015693118739069159107)
              ·
                refine ⟨247523539678108603738661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165015693118739069159107 247523539678108603738661)
                ·
                  refine ⟨46410663689645363200999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247523539678108603738661 46410663689645363200999)
                  ·
                    rfl

theorem cell21_203365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_203365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203365 prefixEnd_203365 := by exact prefixLift 203365
  have htrace : WordTrace (prefixWord ++ tailWord_203365) baseStart_203365 baseEnd_203365 := by
    simpa [prefixWord, tailWord_203365, baseEnd_203365] using wordTrace_append hprefix tailTrace_203365
  have hstable : (prefixWord ++ tailWord_203365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203365).length < 2 ^ (prefixWord ++ tailWord_203365).sum := by decide
  have hdescent : baseEnd_203365 < baseStart_203365 := by decide
  rcases family_descends (prefixWord ++ tailWord_203365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203410 : List Nat := [3, 2, 3, 1, 2, 1, 4, 2, 3]
def baseStart_203410 : Nat := 118140960795 + 203410 * 2 ^ 59
def prefixEnd_203410 : Nat := 4983230072969 + 3 ^ 40 * 203410 * 2
def baseEnd_203410 : Nat := 46420933302735284950907

theorem tailTrace_203410 : CollatzResearch.WordTrace tailWord_203410 prefixEnd_203410 46420933302735284950907 := by
  unfold tailWord_203410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1854743048271946126835921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4945981462058523004895789 1854743048271946126835921)
  ·
    refine ⟨1391057286203959595126941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1854743048271946126835921 1391057286203959595126941)
    ·
      refine ⟨521646482326484848172603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1391057286203959595126941 521646482326484848172603)
      ·
        refine ⟨782469723489727272258905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521646482326484848172603 782469723489727272258905)
        ·
          refine ⟨586852292617295454194179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 782469723489727272258905 586852292617295454194179)
          ·
            refine ⟨880278438925943181291269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586852292617295454194179 880278438925943181291269)
            ·
              refine ⟨165052207298614346492113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 880278438925943181291269 165052207298614346492113)
              ·
                refine ⟨123789155473960759869085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165052207298614346492113 123789155473960759869085)
                ·
                  refine ⟨46420933302735284950907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123789155473960759869085 46420933302735284950907)
                  ·
                    rfl

theorem cell21_203410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_203410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203410 prefixEnd_203410 := by exact prefixLift 203410
  have htrace : WordTrace (prefixWord ++ tailWord_203410) baseStart_203410 baseEnd_203410 := by
    simpa [prefixWord, tailWord_203410, baseEnd_203410] using wordTrace_append hprefix tailTrace_203410
  have hstable : (prefixWord ++ tailWord_203410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203410).length < 2 ^ (prefixWord ++ tailWord_203410).sum := by decide
  have hdescent : baseEnd_203410 < baseStart_203410 := by decide
  rcases family_descends (prefixWord ++ tailWord_203410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203449 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 6]
def baseStart_203449 : Nat := 118140960795 + 203449 * 2 ^ 59
def prefixEnd_203449 : Nat := 4983230072969 + 3 ^ 40 * 203449 * 2
def baseEnd_203449 : Nat := 46429833634079883800827

theorem tailTrace_203449 : CollatzResearch.WordTrace tailWord_203449 prefixEnd_203449 46429833634079883800827 := by
  unfold tailWord_203449
  simp only [CollatzResearch.WordTrace]
  refine ⟨7420394639946494168013401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4946929759964329445342267 7420394639946494168013401)
  ·
    refine ⟨5565295979959870626010051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7420394639946494168013401 5565295979959870626010051)
    ·
      refine ⟨8347943969939805939015077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5565295979959870626010051 8347943969939805939015077)
      ·
        refine ⟨1565239494363713613565327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8347943969939805939015077 1565239494363713613565327)
        ·
          refine ⟨2347859241545570420347991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1565239494363713613565327 2347859241545570420347991)
          ·
            refine ⟨3521788862318355630521987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2347859241545570420347991 3521788862318355630521987)
            ·
              refine ⟨5282683293477533445782981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3521788862318355630521987 5282683293477533445782981)
              ·
                refine ⟨990503117527037521084309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5282683293477533445782981 990503117527037521084309)
                ·
                  refine ⟨46429833634079883800827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 990503117527037521084309 46429833634079883800827)
                  ·
                    rfl

theorem cell21_203449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_203449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203449 prefixEnd_203449 := by exact prefixLift 203449
  have htrace : WordTrace (prefixWord ++ tailWord_203449) baseStart_203449 baseEnd_203449 := by
    simpa [prefixWord, tailWord_203449, baseEnd_203449] using wordTrace_append hprefix tailTrace_203449
  have hstable : (prefixWord ++ tailWord_203449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203449).length < 2 ^ (prefixWord ++ tailWord_203449).sum := by decide
  have hdescent : baseEnd_203449 < baseStart_203449 := by decide
  rcases family_descends (prefixWord ++ tailWord_203449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203466 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 6]
def baseStart_203466 : Nat := 118140960795 + 203466 * 2 ^ 59
def prefixEnd_203466 : Nat := 4983230072969 + 3 ^ 40 * 203466 * 2
def baseEnd_203466 : Nat := 46433713265691632017459

theorem tailTrace_203466 : CollatzResearch.WordTrace tailWord_203466 prefixEnd_203466 46433713265691632017459 := by
  unfold tailWord_203466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1855253670221226517845563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4947343120589937380921501 1855253670221226517845563)
  ·
    refine ⟨2782880505331839776768345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1855253670221226517845563 2782880505331839776768345)
    ·
      refine ⟨2087160378998879832576259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2782880505331839776768345 2087160378998879832576259)
      ·
        refine ⟨3130740568498319748864389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2087160378998879832576259 3130740568498319748864389)
        ·
          refine ⟨587013856593434952912073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3130740568498319748864389 587013856593434952912073)
          ·
            refine ⟨440260392445076214684055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 587013856593434952912073 440260392445076214684055)
            ·
              refine ⟨660390588667614322026083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440260392445076214684055 660390588667614322026083)
              ·
                refine ⟨990585883001421483039125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660390588667614322026083 990585883001421483039125)
                ·
                  refine ⟨46433713265691632017459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 990585883001421483039125 46433713265691632017459)
                  ·
                    rfl

theorem cell21_203466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_203466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203466 prefixEnd_203466 := by exact prefixLift 203466
  have htrace : WordTrace (prefixWord ++ tailWord_203466) baseStart_203466 baseEnd_203466 := by
    simpa [prefixWord, tailWord_203466, baseEnd_203466] using wordTrace_append hprefix tailTrace_203466
  have hstable : (prefixWord ++ tailWord_203466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203466).length < 2 ^ (prefixWord ++ tailWord_203466).sum := by decide
  have hdescent : baseEnd_203466 < baseStart_203466 := by decide
  rcases family_descends (prefixWord ++ tailWord_203466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203528 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 5]
def baseStart_203528 : Nat := 118140960795 + 203528 * 2 ^ 59
def prefixEnd_203528 : Nat := 4983230072969 + 3 ^ 40 * 203528 * 2
def baseEnd_203528 : Nat := 46447862510393301983999

theorem tailTrace_203528 : CollatzResearch.WordTrace tailWord_203528 prefixEnd_203528 46447862510393301983999 := by
  unfold tailWord_203528
  simp only [CollatzResearch.WordTrace]
  refine ⟨3711638003330145330069619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4948850671106860440092825 3711638003330145330069619)
  ·
    refine ⟨5567457004995217995104429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3711638003330145330069619 5567457004995217995104429)
    ·
      refine ⟨2087796376873206748164161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5567457004995217995104429 2087796376873206748164161)
      ·
        refine ⟨1565847282654905061123121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2087796376873206748164161 1565847282654905061123121)
        ·
          refine ⟨1174385461991178795842341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1565847282654905061123121 1174385461991178795842341)
          ·
            refine ⟨220197274123346024220439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1174385461991178795842341 220197274123346024220439)
            ·
              refine ⟨330295911185019036330659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220197274123346024220439 330295911185019036330659)
              ·
                refine ⟨495443866777528554495989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330295911185019036330659 495443866777528554495989)
                ·
                  refine ⟨46447862510393301983999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 495443866777528554495989 46447862510393301983999)
                  ·
                    rfl

theorem cell21_203528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_203528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203528 prefixEnd_203528 := by exact prefixLift 203528
  have htrace : WordTrace (prefixWord ++ tailWord_203528) baseStart_203528 baseEnd_203528 := by
    simpa [prefixWord, tailWord_203528, baseEnd_203528] using wordTrace_append hprefix tailTrace_203528
  have hstable : (prefixWord ++ tailWord_203528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203528).length < 2 ^ (prefixWord ++ tailWord_203528).sum := by decide
  have hdescent : baseEnd_203528 < baseStart_203528 := by decide
  rcases family_descends (prefixWord ++ tailWord_203528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203604 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 5]
def baseStart_203604 : Nat := 118140960795 + 203604 * 2 ^ 59
def prefixEnd_203604 : Nat := 4983230072969 + 3 ^ 40 * 203604 * 2
def baseEnd_203604 : Nat := 46465206745834058717177

theorem tailTrace_203604 : CollatzResearch.WordTrace tailWord_203604 prefixEnd_203604 46465206745834058717177 := by
  unfold tailWord_203604
  simp only [CollatzResearch.WordTrace]
  refine ⟨3713023977192477819952933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4950698636256637093270577 3713023977192477819952933)
  ·
    refine ⟨696191995723589591241175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3713023977192477819952933 696191995723589591241175)
    ·
      refine ⟨1044287993585384386861763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 696191995723589591241175 1044287993585384386861763)
      ·
        refine ⟨1566431990378076580292645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044287993585384386861763 1566431990378076580292645)
        ·
          refine ⟨293705998195889358804871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1566431990378076580292645 293705998195889358804871)
          ·
            refine ⟨440558997293834038207307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293705998195889358804871 440558997293834038207307)
            ·
              refine ⟨660838495940751057310961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440558997293834038207307 660838495940751057310961)
              ·
                refine ⟨495628871955563292983221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 660838495940751057310961 495628871955563292983221)
                ·
                  refine ⟨46465206745834058717177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 495628871955563292983221 46465206745834058717177)
                  ·
                    rfl

theorem cell21_203604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_203604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203604 prefixEnd_203604 := by exact prefixLift 203604
  have htrace : WordTrace (prefixWord ++ tailWord_203604) baseStart_203604 baseEnd_203604 := by
    simpa [prefixWord, tailWord_203604, baseEnd_203604] using wordTrace_append hprefix tailTrace_203604
  have hstable : (prefixWord ++ tailWord_203604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203604).length < 2 ^ (prefixWord ++ tailWord_203604).sum := by decide
  have hdescent : baseEnd_203604 < baseStart_203604 := by decide
  rcases family_descends (prefixWord ++ tailWord_203604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203677 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 8]
def baseStart_203677 : Nat := 118140960795 + 203677 * 2 ^ 59
def prefixEnd_203677 : Nat := 4983230072969 + 3 ^ 40 * 203677 * 2
def baseEnd_203677 : Nat := 46481866340402154000361

theorem tailTrace_203677 : CollatzResearch.WordTrace tailWord_203677 prefixEnd_203677 46481866340402154000361 := by
  unfold tailWord_203677
  simp only [CollatzResearch.WordTrace]
  refine ⟨7428710483120489107313285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4952473655413659404875523 7428710483120489107313285)
  ·
    refine ⟨1392883215585091707621241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7428710483120489107313285 1392883215585091707621241)
    ·
      refine ⟨1044662411688818780715931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1392883215585091707621241 1044662411688818780715931)
      ·
        refine ⟨1566993617533228171073897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044662411688818780715931 1566993617533228171073897)
        ·
          refine ⟨1175245213149921128305423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1566993617533228171073897 1175245213149921128305423)
          ·
            refine ⟨1762867819724881692458135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175245213149921128305423 1762867819724881692458135)
            ·
              refine ⟨2644301729587322538687203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762867819724881692458135 2644301729587322538687203)
              ·
                refine ⟨3966452594380983808030805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644301729587322538687203 3966452594380983808030805)
                ·
                  refine ⟨46481866340402154000361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3966452594380983808030805 46481866340402154000361)
                  ·
                    rfl

theorem cell21_203677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_203677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203677 prefixEnd_203677 := by exact prefixLift 203677
  have htrace : WordTrace (prefixWord ++ tailWord_203677) baseStart_203677 baseEnd_203677 := by
    simpa [prefixWord, tailWord_203677, baseEnd_203677] using wordTrace_append hprefix tailTrace_203677
  have hstable : (prefixWord ++ tailWord_203677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203677).length < 2 ^ (prefixWord ++ tailWord_203677).sum := by decide
  have hdescent : baseEnd_203677 < baseStart_203677 := by decide
  rcases family_descends (prefixWord ++ tailWord_203677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203680 : List Nat := [2, 1, 1, 4, 1, 1, 5, 3, 3]
def baseStart_203680 : Nat := 118140960795 + 203680 * 2 ^ 59
def prefixEnd_203680 : Nat := 4983230072969 + 3 ^ 40 * 203680 * 2
def baseEnd_203680 : Nat := 46482550981274815450355

theorem tailTrace_203680 : CollatzResearch.WordTrace tailWord_203680 prefixEnd_203680 46482550981274815450355 := by
  unfold tailWord_203680
  simp only [CollatzResearch.WordTrace]
  refine ⟨3714409951054810309836247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4952546601406413746448329 3714409951054810309836247)
  ·
    refine ⟨5571614926582215464754371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3714409951054810309836247 5571614926582215464754371)
    ·
      refine ⟨8357422389873323197131557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5571614926582215464754371 8357422389873323197131557)
      ·
        refine ⟨1567016698101248099462167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8357422389873323197131557 1567016698101248099462167)
        ·
          refine ⟨2350525047151872149193251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567016698101248099462167 2350525047151872149193251)
          ·
            refine ⟨3525787570727808223789877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350525047151872149193251 3525787570727808223789877)
            ·
              refine ⟨330542584755732020980301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3525787570727808223789877 330542584755732020980301)
              ·
                refine ⟨123953469283399507867613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330542584755732020980301 123953469283399507867613)
                ·
                  refine ⟨46482550981274815450355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123953469283399507867613 46482550981274815450355)
                  ·
                    rfl

theorem cell21_203680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 3].length) (baseStart_203680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203680 prefixEnd_203680 := by exact prefixLift 203680
  have htrace : WordTrace (prefixWord ++ tailWord_203680) baseStart_203680 baseEnd_203680 := by
    simpa [prefixWord, tailWord_203680, baseEnd_203680] using wordTrace_append hprefix tailTrace_203680
  have hstable : (prefixWord ++ tailWord_203680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203680).length < 2 ^ (prefixWord ++ tailWord_203680).sum := by decide
  have hdescent : baseEnd_203680 < baseStart_203680 := by decide
  rcases family_descends (prefixWord ++ tailWord_203680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203697 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 5]
def baseStart_203697 : Nat := 118140960795 + 203697 * 2 ^ 59
def prefixEnd_203697 : Nat := 4983230072969 + 3 ^ 40 * 203697 * 2
def baseEnd_203697 : Nat := 46486430612886563666987

theorem tailTrace_203697 : CollatzResearch.WordTrace tailWord_203697 prefixEnd_203697 46486430612886563666987 := by
  unfold tailWord_203697
  simp only [CollatzResearch.WordTrace]
  refine ⟨7429439943048032523041345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4952959962032021682027563 7429439943048032523041345)
  ·
    refine ⟨5572079957286024392281009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7429439943048032523041345 5572079957286024392281009)
    ·
      refine ⟨4179059967964518294210757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5572079957286024392281009 4179059967964518294210757)
      ·
        refine ⟨783573743993347180164517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4179059967964518294210757 783573743993347180164517)
        ·
          refine ⟨146920076998752596280847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 783573743993347180164517 146920076998752596280847)
          ·
            refine ⟨220380115498128894421271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146920076998752596280847 220380115498128894421271)
            ·
              refine ⟨330570173247193341631907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220380115498128894421271 330570173247193341631907)
              ·
                refine ⟨495855259870790012447861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330570173247193341631907 495855259870790012447861)
                ·
                  refine ⟨46486430612886563666987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 495855259870790012447861 46486430612886563666987)
                  ·
                    rfl

theorem cell21_203697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 5].length) (baseStart_203697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203697 prefixEnd_203697 := by exact prefixLift 203697
  have htrace : WordTrace (prefixWord ++ tailWord_203697) baseStart_203697 baseEnd_203697 := by
    simpa [prefixWord, tailWord_203697, baseEnd_203697] using wordTrace_append hprefix tailTrace_203697
  have hstable : (prefixWord ++ tailWord_203697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203697).length < 2 ^ (prefixWord ++ tailWord_203697).sum := by decide
  have hdescent : baseEnd_203697 < baseStart_203697 := by decide
  rcases family_descends (prefixWord ++ tailWord_203697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203722 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 7]
def baseStart_203722 : Nat := 118140960795 + 203722 * 2 ^ 59
def prefixEnd_203722 : Nat := 4983230072969 + 3 ^ 40 * 203722 * 2
def baseEnd_203722 : Nat := 46492135953492075750269

theorem tailTrace_203722 : CollatzResearch.WordTrace tailWord_203722 prefixEnd_203722 46492135953492075750269 := by
  unfold tailWord_203722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1857587941989365448175355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4953567845304974528467613 1857587941989365448175355)
  ·
    refine ⟨2786381912984048172263033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1857587941989365448175355 2786381912984048172263033)
    ·
      refine ⟨2089786434738036129197275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2786381912984048172263033 2089786434738036129197275)
      ·
        refine ⟨3134679652107054193795913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2089786434738036129197275 3134679652107054193795913)
        ·
          refine ⟨2351009739080290645346935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3134679652107054193795913 2351009739080290645346935)
          ·
            refine ⟨3526514608620435968020403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351009739080290645346935 3526514608620435968020403)
            ·
              refine ⟨5289771912930653952030605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3526514608620435968020403 5289771912930653952030605)
              ·
                refine ⟨1983664467348995232011477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5289771912930653952030605 1983664467348995232011477)
                ·
                  refine ⟨46492135953492075750269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1983664467348995232011477 46492135953492075750269)
                  ·
                    rfl

theorem cell21_203722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_203722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203722 prefixEnd_203722 := by exact prefixLift 203722
  have htrace : WordTrace (prefixWord ++ tailWord_203722) baseStart_203722 baseEnd_203722 := by
    simpa [prefixWord, tailWord_203722, baseEnd_203722] using wordTrace_append hprefix tailTrace_203722
  have hstable : (prefixWord ++ tailWord_203722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203722).length < 2 ^ (prefixWord ++ tailWord_203722).sum := by decide
  have hdescent : baseEnd_203722 < baseStart_203722 := by decide
  rcases family_descends (prefixWord ++ tailWord_203722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203804 : List Nat := [2, 2, 3, 1, 5, 1, 1, 2, 4]
def baseStart_203804 : Nat := 118140960795 + 203804 * 2 ^ 59
def prefixEnd_203804 : Nat := 4983230072969 + 3 ^ 40 * 203804 * 2
def baseEnd_203804 : Nat := 46510849470678155383435

theorem tailTrace_203804 : CollatzResearch.WordTrace tailWord_203804 prefixEnd_203804 46510849470678155383435 := by
  unfold tailWord_203804
  simp only [CollatzResearch.WordTrace]
  refine ⟨3716671276830194898593233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4955561702440259864790977 3716671276830194898593233)
  ·
    refine ⟨2787503457622646173944925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3716671276830194898593233 2787503457622646173944925)
    ·
      refine ⟨1045313796608492315229347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2787503457622646173944925 1045313796608492315229347)
      ·
        refine ⟨1567970694912738472844021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1045313796608492315229347 1567970694912738472844021)
        ·
          refine ⟨146997252648069231829127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1567970694912738472844021 146997252648069231829127)
          ·
            refine ⟨220495878972103847743691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146997252648069231829127 220495878972103847743691)
            ·
              refine ⟨330743818458155771615537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220495878972103847743691 330743818458155771615537)
              ·
                refine ⟨248057863843616828711653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330743818458155771615537 248057863843616828711653)
                ·
                  refine ⟨46510849470678155383435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248057863843616828711653 46510849470678155383435)
                  ·
                    rfl

theorem cell21_203804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_203804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203804 prefixEnd_203804 := by exact prefixLift 203804
  have htrace : WordTrace (prefixWord ++ tailWord_203804) baseStart_203804 baseEnd_203804 := by
    simpa [prefixWord, tailWord_203804, baseEnd_203804] using wordTrace_append hprefix tailTrace_203804
  have hstable : (prefixWord ++ tailWord_203804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203804).length < 2 ^ (prefixWord ++ tailWord_203804).sum := by decide
  have hdescent : baseEnd_203804 < baseStart_203804 := by decide
  rcases family_descends (prefixWord ++ tailWord_203804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203843 : List Nat := [1, 1, 1, 3, 1, 2, 5, 7]
def baseStart_203843 : Nat := 118140960795 + 203843 * 2 ^ 59
def prefixEnd_203843 : Nat := 4983230072969 + 3 ^ 40 * 203843 * 2
def baseEnd_203843 : Nat := 15506583267340918077785

theorem tailTrace_203843 : CollatzResearch.WordTrace tailWord_203843 prefixEnd_203843 15506583267340918077785 := by
  unfold tailWord_203843
  simp only [CollatzResearch.WordTrace]
  refine ⟨7434765000519099457856183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4956510000346066305237455 7434765000519099457856183)
  ·
    refine ⟨11152147500778649186784275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7434765000519099457856183 11152147500778649186784275)
    ·
      refine ⟨16728221251167973780176413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11152147500778649186784275 16728221251167973780176413)
      ·
        refine ⟨6273082969187990167566155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16728221251167973780176413 6273082969187990167566155)
        ·
          refine ⟨9409624453781985251349233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6273082969187990167566155 9409624453781985251349233)
          ·
            refine ⟨7057218340336488938511925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9409624453781985251349233 7057218340336488938511925)
            ·
              refine ⟨661614219406545837985493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7057218340336488938511925 661614219406545837985493)
              ·
                refine ⟨15506583267340918077785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 661614219406545837985493 15506583267340918077785)
                ·
                  rfl

theorem cell21_203843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 7].length) (baseStart_203843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203843 prefixEnd_203843 := by exact prefixLift 203843
  have htrace : WordTrace (prefixWord ++ tailWord_203843) baseStart_203843 baseEnd_203843 := by
    simpa [prefixWord, tailWord_203843, baseEnd_203843] using wordTrace_append hprefix tailTrace_203843
  have hstable : (prefixWord ++ tailWord_203843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203843).length < 2 ^ (prefixWord ++ tailWord_203843).sum := by decide
  have hdescent : baseEnd_203843 < baseStart_203843 := by decide
  rcases family_descends (prefixWord ++ tailWord_203843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203922 : List Nat := [3, 2, 3, 1, 1, 2, 1, 4, 4]
def baseStart_203922 : Nat := 118140960795 + 203922 * 2 ^ 59
def prefixEnd_203922 : Nat := 4983230072969 + 3 ^ 40 * 203922 * 2
def baseEnd_203922 : Nat := 46537778678336172416527

theorem tailTrace_203922 : CollatzResearch.WordTrace tailWord_203922 prefixEnd_203922 46537778678336172416527 := by
  unfold tailWord_203922
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859411591808223987495505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4958430911488597299988013 1859411591808223987495505)
  ·
    refine ⟨1394558693856167990621629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1859411591808223987495505 1394558693856167990621629)
    ·
      refine ⟨522959510196062996483111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1394558693856167990621629 522959510196062996483111)
      ·
        refine ⟨784439265294094494724667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522959510196062996483111 784439265294094494724667)
        ·
          refine ⟨1176658897941141742087001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784439265294094494724667 1176658897941141742087001)
          ·
            refine ⟨882494173455856306565251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1176658897941141742087001 882494173455856306565251)
            ·
              refine ⟨1323741260183784459847877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882494173455856306565251 1323741260183784459847877)
              ·
                refine ⟨248201486284459586221477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1323741260183784459847877 248201486284459586221477)
                ·
                  refine ⟨46537778678336172416527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248201486284459586221477 46537778678336172416527)
                  ·
                    rfl

theorem cell21_203922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_203922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203922 prefixEnd_203922 := by exact prefixLift 203922
  have htrace : WordTrace (prefixWord ++ tailWord_203922) baseStart_203922 baseEnd_203922 := by
    simpa [prefixWord, tailWord_203922, baseEnd_203922] using wordTrace_append hprefix tailTrace_203922
  have hstable : (prefixWord ++ tailWord_203922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203922).length < 2 ^ (prefixWord ++ tailWord_203922).sum := by decide
  have hdescent : baseEnd_203922 < baseStart_203922 := by decide
  rcases family_descends (prefixWord ++ tailWord_203922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203953 : List Nat := [1, 2, 2, 5, 1, 2, 3, 5]
def baseStart_203953 : Nat := 118140960795 + 203953 * 2 ^ 59
def prefixEnd_203953 : Nat := 4983230072969 + 3 ^ 40 * 203953 * 2
def baseEnd_203953 : Nat := 15514951100229002466599

theorem tailTrace_203953 : CollatzResearch.WordTrace tailWord_203953 prefixEnd_203953 15514951100229002466599 := by
  unfold tailWord_203953
  simp only [CollatzResearch.WordTrace]
  refine ⟨7438777030120588244360513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4959184686747058829573675 7438777030120588244360513)
  ·
    refine ⟨5579082772590441183270385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7438777030120588244360513 5579082772590441183270385)
    ·
      refine ⟨4184312079442830887452789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5579082772590441183270385 4184312079442830887452789)
      ·
        refine ⟨392279257447765395698699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4184312079442830887452789 392279257447765395698699)
        ·
          refine ⟨588418886171648093548049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392279257447765395698699 588418886171648093548049)
          ·
            refine ⟨441314164628736070161037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588418886171648093548049 441314164628736070161037)
            ·
              refine ⟨165492811735776026310389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 441314164628736070161037 165492811735776026310389)
              ·
                refine ⟨15514951100229002466599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165492811735776026310389 15514951100229002466599)
                ·
                  rfl

theorem cell21_203953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 5].length) (baseStart_203953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203953 prefixEnd_203953 := by exact prefixLift 203953
  have htrace : WordTrace (prefixWord ++ tailWord_203953) baseStart_203953 baseEnd_203953 := by
    simpa [prefixWord, tailWord_203953, baseEnd_203953] using wordTrace_append hprefix tailTrace_203953
  have hstable : (prefixWord ++ tailWord_203953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203953).length < 2 ^ (prefixWord ++ tailWord_203953).sum := by decide
  have hdescent : baseEnd_203953 < baseStart_203953 := by decide
  rcases family_descends (prefixWord ++ tailWord_203953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203967 : List Nat := [1, 1, 2, 2, 2, 2, 3, 5, 3]
def baseStart_203967 : Nat := 118140960795 + 203967 * 2 ^ 59
def prefixEnd_203967 : Nat := 4983230072969 + 3 ^ 40 * 203967 * 2
def baseEnd_203967 : Nat := 46548048291426094166435

theorem tailTrace_203967 : CollatzResearch.WordTrace tailWord_203967 prefixEnd_203967 46548048291426094166435 := by
  unfold tailWord_203967
  simp only [CollatzResearch.WordTrace]
  refine ⟨7439287652069868635370155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4959525101379912423580103 7439287652069868635370155)
  ·
    refine ⟨11158931478104802953055233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7439287652069868635370155 11158931478104802953055233)
    ·
      refine ⟨8369198608578602214791425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11158931478104802953055233 8369198608578602214791425)
      ·
        refine ⟨6276898956433951661093569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8369198608578602214791425 6276898956433951661093569)
        ·
          refine ⟨4707674217325463745820177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6276898956433951661093569 4707674217325463745820177)
          ·
            refine ⟨3530755662994097809365133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4707674217325463745820177 3530755662994097809365133)
            ·
              refine ⟨1324033373622786678511925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3530755662994097809365133 1324033373622786678511925)
              ·
                refine ⟨124128128777136251110493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1324033373622786678511925 124128128777136251110493)
                ·
                  refine ⟨46548048291426094166435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124128128777136251110493 46548048291426094166435)
                  ·
                    rfl

theorem cell21_203967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 3].length) (baseStart_203967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203967 prefixEnd_203967 := by exact prefixLift 203967
  have htrace : WordTrace (prefixWord ++ tailWord_203967) baseStart_203967 baseEnd_203967 := by
    simpa [prefixWord, tailWord_203967, baseEnd_203967] using wordTrace_append hprefix tailTrace_203967
  have hstable : (prefixWord ++ tailWord_203967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203967).length < 2 ^ (prefixWord ++ tailWord_203967).sum := by decide
  have hdescent : baseEnd_203967 < baseStart_203967 := by decide
  rcases family_descends (prefixWord ++ tailWord_203967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203970 : List Nat := [3, 5, 1, 1, 2, 1, 8]
def baseStart_203970 : Nat := 118140960795 + 203970 * 2 ^ 59
def prefixEnd_203970 : Nat := 4983230072969 + 3 ^ 40 * 203970 * 2
def baseEnd_203970 : Nat := 5172081436922083957381

theorem tailTrace_203970 : CollatzResearch.WordTrace tailWord_203970 prefixEnd_203970 5172081436922083957381 := by
  unfold tailWord_203970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859849267764750036932341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4959598047372666765152909 1859849267764750036932341)
  ·
    refine ⟨174360868852945315962407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1859849267764750036932341 174360868852945315962407)
    ·
      refine ⟨261541303279417973943611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174360868852945315962407 261541303279417973943611)
      ·
        refine ⟨392311954919126960915417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261541303279417973943611 392311954919126960915417)
        ·
          refine ⟨294233966189345220686563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392311954919126960915417 294233966189345220686563)
          ·
            refine ⟨441350949284017831029845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294233966189345220686563 441350949284017831029845)
            ·
              refine ⟨5172081436922083957381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 441350949284017831029845 5172081436922083957381)
              ·
                rfl

theorem cell21_203970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 8].length) (baseStart_203970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_203970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_203970 prefixEnd_203970 := by exact prefixLift 203970
  have htrace : WordTrace (prefixWord ++ tailWord_203970) baseStart_203970 baseEnd_203970 := by
    simpa [prefixWord, tailWord_203970, baseEnd_203970] using wordTrace_append hprefix tailTrace_203970
  have hstable : (prefixWord ++ tailWord_203970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203970).length < 2 ^ (prefixWord ++ tailWord_203970).sum := by decide
  have hdescent : baseEnd_203970 < baseStart_203970 := by decide
  rcases family_descends (prefixWord ++ tailWord_203970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204012 : List Nat := [2, 2, 1, 1, 2, 4, 4, 5]
def baseStart_204012 : Nat := 118140960795 + 204012 * 2 ^ 59
def prefixEnd_204012 : Nat := 4983230072969 + 3 ^ 40 * 204012 * 2
def baseEnd_204012 : Nat := 15519439301505338638781

theorem tailTrace_204012 : CollatzResearch.WordTrace tailWord_204012 prefixEnd_204012 15519439301505338638781 := by
  unfold tailWord_204012
  simp only [CollatzResearch.WordTrace]
  refine ⟨3720464468453420660379145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4960619291271227547172193 3720464468453420660379145)
  ·
    refine ⟨2790348351340065495284359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3720464468453420660379145 2790348351340065495284359)
    ·
      refine ⟨4185522527010098242926539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2790348351340065495284359 4185522527010098242926539)
      ·
        refine ⟨6278283790515147364389809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4185522527010098242926539 6278283790515147364389809)
        ·
          refine ⟨4708712842886360523292357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6278283790515147364389809 4708712842886360523292357)
          ·
            refine ⟨882883658041192598117317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4708712842886360523292357 882883658041192598117317)
            ·
              refine ⟨165540685882723612146997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 882883658041192598117317 165540685882723612146997)
              ·
                refine ⟨15519439301505338638781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165540685882723612146997 15519439301505338638781)
                ·
                  rfl

theorem cell21_204012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 5].length) (baseStart_204012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204012 prefixEnd_204012 := by exact prefixLift 204012
  have htrace : WordTrace (prefixWord ++ tailWord_204012) baseStart_204012 baseEnd_204012 := by
    simpa [prefixWord, tailWord_204012, baseEnd_204012] using wordTrace_append hprefix tailTrace_204012
  have hstable : (prefixWord ++ tailWord_204012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204012).length < 2 ^ (prefixWord ++ tailWord_204012).sum := by decide
  have hdescent : baseEnd_204012 < baseStart_204012 := by decide
  rcases family_descends (prefixWord ++ tailWord_204012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204018 : List Nat := [3, 2, 1, 3, 4, 1, 1, 3, 3]
def baseStart_204018 : Nat := 118140960795 + 204018 * 2 ^ 59
def prefixEnd_204018 : Nat := 4983230072969 + 3 ^ 40 * 204018 * 2
def baseEnd_204018 : Nat := 46559687186261338816331

theorem tailTrace_204018 : CollatzResearch.WordTrace tailWord_204018 prefixEnd_204018 46559687186261338816331 := by
  unfold tailWord_204018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860286943721276086369177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4960765183256736230317805 1860286943721276086369177)
  ·
    refine ⟨1395215207790957064776883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1860286943721276086369177 1395215207790957064776883)
    ·
      refine ⟨2092822811686435597165325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1395215207790957064776883 2092822811686435597165325)
      ·
        refine ⟨784808554382413348936997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2092822811686435597165325 784808554382413348936997)
        ·
          refine ⟨147151603946702502925687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 784808554382413348936997 147151603946702502925687)
          ·
            refine ⟨220727405920053754388531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147151603946702502925687 220727405920053754388531)
            ·
              refine ⟨331091108880080631582797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220727405920053754388531 331091108880080631582797)
              ·
                refine ⟨124159165830030236843549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331091108880080631582797 124159165830030236843549)
                ·
                  refine ⟨46559687186261338816331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124159165830030236843549 46559687186261338816331)
                  ·
                    rfl

theorem cell21_204018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_204018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204018 prefixEnd_204018 := by exact prefixLift 204018
  have htrace : WordTrace (prefixWord ++ tailWord_204018) baseStart_204018 baseEnd_204018 := by
    simpa [prefixWord, tailWord_204018, baseEnd_204018] using wordTrace_append hprefix tailTrace_204018
  have hstable : (prefixWord ++ tailWord_204018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204018).length < 2 ^ (prefixWord ++ tailWord_204018).sum := by decide
  have hdescent : baseEnd_204018 < baseStart_204018 := by decide
  rcases family_descends (prefixWord ++ tailWord_204018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204043 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 5]
def baseStart_204043 : Nat := 118140960795 + 204043 * 2 ^ 59
def prefixEnd_204043 : Nat := 4983230072969 + 3 ^ 40 * 204043 * 2
def baseEnd_204043 : Nat := 46565392526866850899613

theorem tailTrace_204043 : CollatzResearch.WordTrace tailWord_204043 prefixEnd_204043 46565392526866850899613 := by
  unfold tailWord_204043
  simp only [CollatzResearch.WordTrace]
  refine ⟨7442059599794533615136783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4961373066529689076757855 7442059599794533615136783)
  ·
    refine ⟨11163089399691800422705175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7442059599794533615136783 11163089399691800422705175)
    ·
      refine ⟨16744634099537700634057763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11163089399691800422705175 16744634099537700634057763)
      ·
        refine ⟨25116951149306550951086645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16744634099537700634057763 25116951149306550951086645)
        ·
          refine ⟨2354714170247489151664373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25116951149306550951086645 2354714170247489151664373)
          ·
            refine ⟨220754453460702107968535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2354714170247489151664373 220754453460702107968535)
            ·
              refine ⟨331131680191053161952803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220754453460702107968535 331131680191053161952803)
              ·
                refine ⟨496697520286579742929205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331131680191053161952803 496697520286579742929205)
                ·
                  refine ⟨46565392526866850899613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 496697520286579742929205 46565392526866850899613)
                  ·
                    rfl

theorem cell21_204043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 5].length) (baseStart_204043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204043 prefixEnd_204043 := by exact prefixLift 204043
  have htrace : WordTrace (prefixWord ++ tailWord_204043) baseStart_204043 baseEnd_204043 := by
    simpa [prefixWord, tailWord_204043, baseEnd_204043] using wordTrace_append hprefix tailTrace_204043
  have hstable : (prefixWord ++ tailWord_204043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204043).length < 2 ^ (prefixWord ++ tailWord_204043).sum := by decide
  have hdescent : baseEnd_204043 < baseStart_204043 := by decide
  rcases family_descends (prefixWord ++ tailWord_204043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204192 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 8]
def baseStart_204192 : Nat := 118140960795 + 204192 * 2 ^ 59
def prefixEnd_204192 : Nat := 4983230072969 + 3 ^ 40 * 204192 * 2
def baseEnd_204192 : Nat := 46599396356875702915975

theorem tailTrace_204192 : CollatzResearch.WordTrace tailWord_204192 prefixEnd_204192 46599396356875702915975 := by
  unfold tailWord_204192
  simp only [CollatzResearch.WordTrace]
  refine ⟨3723747038127366031155415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4964996050836488041540553 3723747038127366031155415)
  ·
    refine ⟨5585620557191049046733123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3723747038127366031155415 5585620557191049046733123)
    ·
      refine ⟨8378430835786573570099685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5585620557191049046733123 8378430835786573570099685)
      ·
        refine ⟨1570955781709982544393691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8378430835786573570099685 1570955781709982544393691)
        ·
          refine ⟨2356433672564973816590537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570955781709982544393691 2356433672564973816590537)
          ·
            refine ⟨1767325254423730362442903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2356433672564973816590537 1767325254423730362442903)
            ·
              refine ⟨2650987881635595543664355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1767325254423730362442903 2650987881635595543664355)
              ·
                refine ⟨3976481822453393315496533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2650987881635595543664355 3976481822453393315496533)
                ·
                  refine ⟨46599396356875702915975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3976481822453393315496533 46599396356875702915975)
                  ·
                    rfl

theorem cell21_204192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_204192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204192 prefixEnd_204192 := by exact prefixLift 204192
  have htrace : WordTrace (prefixWord ++ tailWord_204192) baseStart_204192 baseEnd_204192 := by
    simpa [prefixWord, tailWord_204192, baseEnd_204192] using wordTrace_append hprefix tailTrace_204192
  have hstable : (prefixWord ++ tailWord_204192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204192).length < 2 ^ (prefixWord ++ tailWord_204192).sum := by decide
  have hdescent : baseEnd_204192 < baseStart_204192 := by decide
  rcases family_descends (prefixWord ++ tailWord_204192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204209 : List Nat := [1, 2, 2, 4, 1, 1, 2, 4, 4]
def baseStart_204209 : Nat := 118140960795 + 204209 * 2 ^ 59
def prefixEnd_204209 : Nat := 4983230072969 + 3 ^ 40 * 204209 * 2
def baseEnd_204209 : Nat := 46603275988487451132607

theorem tailTrace_204209 : CollatzResearch.WordTrace tailWord_204209 prefixEnd_204209 46603275988487451132607 := by
  unfold tailWord_204209
  simp only [CollatzResearch.WordTrace]
  refine ⟨7448114117193143965679681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4965409411462095977119787 7448114117193143965679681)
  ·
    refine ⟨5586085587894857974259761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7448114117193143965679681 5586085587894857974259761)
    ·
      refine ⟨4189564190921143480694821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5586085587894857974259761 4189564190921143480694821)
      ·
        refine ⟨785543285797714402630279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4189564190921143480694821 785543285797714402630279)
        ·
          refine ⟨1178314928696571603945419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785543285797714402630279 1178314928696571603945419)
          ·
            refine ⟨1767472393044857405918129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178314928696571603945419 1767472393044857405918129)
            ·
              refine ⟨1325604294783643054438597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1767472393044857405918129 1325604294783643054438597)
              ·
                refine ⟨248550805271933072707237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1325604294783643054438597 248550805271933072707237)
                ·
                  refine ⟨46603275988487451132607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248550805271933072707237 46603275988487451132607)
                  ·
                    rfl

theorem cell21_204209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_204209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204209 prefixEnd_204209 := by exact prefixLift 204209
  have htrace : WordTrace (prefixWord ++ tailWord_204209) baseStart_204209 baseEnd_204209 := by
    simpa [prefixWord, tailWord_204209, baseEnd_204209] using wordTrace_append hprefix tailTrace_204209
  have hstable : (prefixWord ++ tailWord_204209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204209).length < 2 ^ (prefixWord ++ tailWord_204209).sum := by decide
  have hdescent : baseEnd_204209 < baseStart_204209 := by decide
  rcases family_descends (prefixWord ++ tailWord_204209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204285 : List Nat := [1, 4, 1, 1, 1, 4, 2, 3, 4]
def baseStart_204285 : Nat := 118140960795 + 204285 * 2 ^ 59
def prefixEnd_204285 : Nat := 4983230072969 + 3 ^ 40 * 204285 * 2
def baseEnd_204285 : Nat := 46620620223928207865785

theorem tailTrace_204285 : CollatzResearch.WordTrace tailWord_204285 prefixEnd_204285 46620620223928207865785 := by
  unfold tailWord_204285
  simp only [CollatzResearch.WordTrace]
  refine ⟨7450886064917808945446309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4967257376611872630297539 7450886064917808945446309)
  ·
    refine ⟨1397041137172089177271183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7450886064917808945446309 1397041137172089177271183)
    ·
      refine ⟨2095561705758133765906775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1397041137172089177271183 2095561705758133765906775)
      ·
        refine ⟨3143342558637200648860163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2095561705758133765906775 3143342558637200648860163)
        ·
          refine ⟨4715013837955800973290245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3143342558637200648860163 4715013837955800973290245)
          ·
            refine ⟨884065094616712682491921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4715013837955800973290245 884065094616712682491921)
            ·
              refine ⟨663048820962534511868941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884065094616712682491921 663048820962534511868941)
              ·
                refine ⟨248643307860950441950853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 663048820962534511868941 248643307860950441950853)
                ·
                  refine ⟨46620620223928207865785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248643307860950441950853 46620620223928207865785)
                  ·
                    rfl

theorem cell21_204285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_204285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204285 prefixEnd_204285 := by exact prefixLift 204285
  have htrace : WordTrace (prefixWord ++ tailWord_204285) baseStart_204285 baseEnd_204285 := by
    simpa [prefixWord, tailWord_204285, baseEnd_204285] using wordTrace_append hprefix tailTrace_204285
  have hstable : (prefixWord ++ tailWord_204285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204285).length < 2 ^ (prefixWord ++ tailWord_204285).sum := by decide
  have hdescent : baseEnd_204285 < baseStart_204285 := by decide
  rcases family_descends (prefixWord ++ tailWord_204285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204364 : List Nat := [2, 2, 1, 3, 1, 5, 1, 3, 3]
def baseStart_204364 : Nat := 118140960795 + 204364 * 2 ^ 59
def prefixEnd_204364 : Nat := 4983230072969 + 3 ^ 40 * 204364 * 2
def baseEnd_204364 : Nat := 46638649100241626048957

theorem tailTrace_204364 : CollatzResearch.WordTrace tailWord_204364 prefixEnd_204364 46638649100241626048957 := by
  unfold tailWord_204364
  simp only [CollatzResearch.WordTrace]
  refine ⟨3726883715815802718786073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4969178287754403625048097 3726883715815802718786073)
  ·
    refine ⟨2795162786861852039089555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3726883715815802718786073 2795162786861852039089555)
    ·
      refine ⟨4192744180292778058634333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2795162786861852039089555 4192744180292778058634333)
      ·
        refine ⟨1572279067609791771987875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4192744180292778058634333 1572279067609791771987875)
        ·
          refine ⟨2358418601414687657981813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1572279067609791771987875 2358418601414687657981813)
          ·
            refine ⟨221101743882626967935795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2358418601414687657981813 221101743882626967935795)
            ·
              refine ⟨331652615823940451903693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221101743882626967935795 331652615823940451903693)
              ·
                refine ⟨124369730933977669463885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331652615823940451903693 124369730933977669463885)
                ·
                  refine ⟨46638649100241626048957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124369730933977669463885 46638649100241626048957)
                  ·
                    rfl

theorem cell21_204364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_204364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204364 prefixEnd_204364 := by exact prefixLift 204364
  have htrace : WordTrace (prefixWord ++ tailWord_204364) baseStart_204364 baseEnd_204364 := by
    simpa [prefixWord, tailWord_204364, baseEnd_204364] using wordTrace_append hprefix tailTrace_204364
  have hstable : (prefixWord ++ tailWord_204364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204364).length < 2 ^ (prefixWord ++ tailWord_204364).sum := by decide
  have hdescent : baseEnd_204364 < baseStart_204364 := by decide
  rcases family_descends (prefixWord ++ tailWord_204364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204375 : List Nat := [1, 1, 3, 2, 2, 5, 7]
def baseStart_204375 : Nat := 118140960795 + 204375 * 2 ^ 59
def prefixEnd_204375 : Nat := 4983230072969 + 3 ^ 40 * 204375 * 2
def baseEnd_204375 : Nat := 5182351050012005707289

theorem tailTrace_204375 : CollatzResearch.WordTrace tailWord_204375 prefixEnd_204375 5182351050012005707289 := by
  unfold tailWord_204375
  simp only [CollatzResearch.WordTrace]
  refine ⟨7454168634591754316222579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4969445756394502877481719 7454168634591754316222579)
  ·
    refine ⟨11181252951887631474333869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7454168634591754316222579 11181252951887631474333869)
    ·
      refine ⟨4192969856957861802875201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11181252951887631474333869 4192969856957861802875201)
      ·
        refine ⟨3144727392718396352156401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4192969856957861802875201 3144727392718396352156401)
        ·
          refine ⟨2358545544538797264117301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3144727392718396352156401 2358545544538797264117301)
          ·
            refine ⟨221113644800512243510997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2358545544538797264117301 221113644800512243510997)
            ·
              refine ⟨5182351050012005707289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 221113644800512243510997 5182351050012005707289)
              ·
                rfl

theorem cell21_204375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 7].length) (baseStart_204375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204375 prefixEnd_204375 := by exact prefixLift 204375
  have htrace : WordTrace (prefixWord ++ tailWord_204375) baseStart_204375 baseEnd_204375 := by
    simpa [prefixWord, tailWord_204375, baseEnd_204375] using wordTrace_append hprefix tailTrace_204375
  have hstable : (prefixWord ++ tailWord_204375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204375).length < 2 ^ (prefixWord ++ tailWord_204375).sum := by decide
  have hdescent : baseEnd_204375 < baseStart_204375 := by decide
  rcases family_descends (prefixWord ++ tailWord_204375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204381 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 5]
def baseStart_204381 : Nat := 118140960795 + 204381 * 2 ^ 59
def prefixEnd_204381 : Nat := 4983230072969 + 3 ^ 40 * 204381 * 2
def baseEnd_204381 : Nat := 46642528731853374265589

theorem tailTrace_204381 : CollatzResearch.WordTrace tailWord_204381 prefixEnd_204381 46642528731853374265589 := by
  unfold tailWord_204381
  simp only [CollatzResearch.WordTrace]
  refine ⟨7454387472570017340940997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4969591648380011560627331 7454387472570017340940997)
  ·
    refine ⟨1397697651106878251426437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7454387472570017340940997 1397697651106878251426437)
    ·
      refine ⟨262068309582539672142457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1397697651106878251426437 262068309582539672142457)
      ·
        refine ⟨196551232186904754106843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262068309582539672142457 196551232186904754106843)
        ·
          refine ⟨294826848280357131160265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196551232186904754106843 294826848280357131160265)
          ·
            refine ⟨221120136210267848370199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294826848280357131160265 221120136210267848370199)
            ·
              refine ⟨331680204315401772555299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221120136210267848370199 331680204315401772555299)
              ·
                refine ⟨497520306473102658832949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331680204315401772555299 497520306473102658832949)
                ·
                  refine ⟨46642528731853374265589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 497520306473102658832949 46642528731853374265589)
                  ·
                    rfl

theorem cell21_204381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_204381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204381 prefixEnd_204381 := by exact prefixLift 204381
  have htrace : WordTrace (prefixWord ++ tailWord_204381) baseStart_204381 baseEnd_204381 := by
    simpa [prefixWord, tailWord_204381, baseEnd_204381] using wordTrace_append hprefix tailTrace_204381
  have hstable : (prefixWord ++ tailWord_204381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204381).length < 2 ^ (prefixWord ++ tailWord_204381).sum := by decide
  have hdescent : baseEnd_204381 < baseStart_204381 := by decide
  rcases family_descends (prefixWord ++ tailWord_204381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204392 : List Nat := [2, 1, 4, 3, 1, 2, 2, 6]
def baseStart_204392 : Nat := 118140960795 + 204392 * 2 ^ 59
def prefixEnd_204392 : Nat := 4983230072969 + 3 ^ 40 * 204392 * 2
def baseEnd_204392 : Nat := 15548346360573266527411

theorem tailTrace_204392 : CollatzResearch.WordTrace tailWord_204392 prefixEnd_204392 15548346360573266527411 := by
  unfold tailWord_204392
  simp only [CollatzResearch.WordTrace]
  refine ⟨3727394337765083109795715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4969859117020110813060953 3727394337765083109795715)
  ·
    refine ⟨5591091506647624664693573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3727394337765083109795715 5591091506647624664693573)
    ·
      refine ⟨1048329657496429624630045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5591091506647624664693573 1048329657496429624630045)
      ·
        refine ⟨393123621561161109236267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1048329657496429624630045 393123621561161109236267)
        ·
          refine ⟨589685432341741663854401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393123621561161109236267 589685432341741663854401)
          ·
            refine ⟨442264074256306247890801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 589685432341741663854401 442264074256306247890801)
            ·
              refine ⟨331698055692229685918101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442264074256306247890801 331698055692229685918101)
              ·
                refine ⟨15548346360573266527411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 331698055692229685918101 15548346360573266527411)
                ·
                  rfl

theorem cell21_204392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 6].length) (baseStart_204392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204392 prefixEnd_204392 := by exact prefixLift 204392
  have htrace : WordTrace (prefixWord ++ tailWord_204392) baseStart_204392 baseEnd_204392 := by
    simpa [prefixWord, tailWord_204392, baseEnd_204392] using wordTrace_append hprefix tailTrace_204392
  have hstable : (prefixWord ++ tailWord_204392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204392).length < 2 ^ (prefixWord ++ tailWord_204392).sum := by decide
  have hdescent : baseEnd_204392 < baseStart_204392 := by decide
  rcases family_descends (prefixWord ++ tailWord_204392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204440 : List Nat := [2, 1, 2, 4, 1, 2, 4, 2, 3]
def baseStart_204440 : Nat := 118140960795 + 204440 * 2 ^ 59
def prefixEnd_204440 : Nat := 4983230072969 + 3 ^ 40 * 204440 * 2
def baseEnd_204440 : Nat := 46655993335682382782135

theorem tailTrace_204440 : CollatzResearch.WordTrace tailWord_204440 prefixEnd_204440 46655993335682382782135 := by
  unfold tailWord_204440
  simp only [CollatzResearch.WordTrace]
  refine ⟨3728269689678135208669387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4971026252904180278225849 3728269689678135208669387)
  ·
    refine ⟨5592404534517202813004081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3728269689678135208669387 5592404534517202813004081)
    ·
      refine ⟨4194303400887902109753061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5592404534517202813004081 4194303400887902109753061)
      ·
        refine ⟨786431887666481645578699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4194303400887902109753061 786431887666481645578699)
        ·
          refine ⟨1179647831499722468368049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 786431887666481645578699 1179647831499722468368049)
          ·
            refine ⟨884735873624791851276037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1179647831499722468368049 884735873624791851276037)
            ·
              refine ⟨165887976304648472114257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 884735873624791851276037 165887976304648472114257)
              ·
                refine ⟨124415982228486354085693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165887976304648472114257 124415982228486354085693)
                ·
                  refine ⟨46655993335682382782135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124415982228486354085693 46655993335682382782135)
                  ·
                    rfl

theorem cell21_204440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 3].length) (baseStart_204440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204440 prefixEnd_204440 := by exact prefixLift 204440
  have htrace : WordTrace (prefixWord ++ tailWord_204440) baseStart_204440 baseEnd_204440 := by
    simpa [prefixWord, tailWord_204440, baseEnd_204440] using wordTrace_append hprefix tailTrace_204440
  have hstable : (prefixWord ++ tailWord_204440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204440).length < 2 ^ (prefixWord ++ tailWord_204440).sum := by decide
  have hdescent : baseEnd_204440 < baseStart_204440 := by decide
  rcases family_descends (prefixWord ++ tailWord_204440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204496 : List Nat := [2, 1, 1, 1, 1, 2, 1, 8, 4]
def baseStart_204496 : Nat := 118140960795 + 204496 * 2 ^ 59
def prefixEnd_204496 : Nat := 4983230072969 + 3 ^ 40 * 204496 * 2
def baseEnd_204496 : Nat := 46668773298638729848687

theorem tailTrace_204496 : CollatzResearch.WordTrace tailWord_204496 prefixEnd_204496 46668773298638729848687 := by
  unfold tailWord_204496
  simp only [CollatzResearch.WordTrace]
  refine ⟨3729290933576695990688671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4972387911435594654251561 3729290933576695990688671)
  ·
    refine ⟨5593936400365043986033007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3729290933576695990688671 5593936400365043986033007)
    ·
      refine ⟨8390904600547565979049511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5593936400365043986033007 8390904600547565979049511)
      ·
        refine ⟨12586356900821348968574267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8390904600547565979049511 12586356900821348968574267)
        ·
          refine ⟨18879535351232023452861401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12586356900821348968574267 18879535351232023452861401)
          ·
            refine ⟨14159651513424017589646051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18879535351232023452861401 14159651513424017589646051)
            ·
              refine ⟨21239477270136026384469077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14159651513424017589646051 21239477270136026384469077)
              ·
                refine ⟨248900124259406559192997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 21239477270136026384469077 248900124259406559192997)
                ·
                  refine ⟨46668773298638729848687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248900124259406559192997 46668773298638729848687)
                  ·
                    rfl

theorem cell21_204496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_204496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204496 prefixEnd_204496 := by exact prefixLift 204496
  have htrace : WordTrace (prefixWord ++ tailWord_204496) baseStart_204496 baseEnd_204496 := by
    simpa [prefixWord, tailWord_204496, baseEnd_204496] using wordTrace_append hprefix tailTrace_204496
  have hstable : (prefixWord ++ tailWord_204496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204496).length < 2 ^ (prefixWord ++ tailWord_204496).sum := by decide
  have hdescent : baseEnd_204496 < baseStart_204496 := by decide
  rcases family_descends (prefixWord ++ tailWord_204496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204558 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_204558 : Nat := 118140960795 + 204558 * 2 ^ 59
def prefixEnd_204558 : Nat := 4983230072969 + 3 ^ 40 * 204558 * 2
def baseEnd_204558 : Nat := 46682922543340399815227

theorem tailTrace_204558 : CollatzResearch.WordTrace tailWord_204558 prefixEnd_204558 46682922543340399815227 := by
  unfold tailWord_204558
  simp only [CollatzResearch.WordTrace]
  refine ⟨932605399116097071266791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4973895461952517713422885 932605399116097071266791)
  ·
    refine ⟨1398908098674145606900187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 932605399116097071266791 1398908098674145606900187)
    ·
      refine ⟨2098362148011218410350281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1398908098674145606900187 2098362148011218410350281)
      ·
        refine ⟨1573771611008413807762711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2098362148011218410350281 1573771611008413807762711)
        ·
          refine ⟨2360657416512620711644067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573771611008413807762711 2360657416512620711644067)
          ·
            refine ⟨3540986124768931067466101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360657416512620711644067 3540986124768931067466101)
            ·
              refine ⟨331967449197087287574947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3540986124768931067466101 331967449197087287574947)
              ·
                refine ⟨497951173795630931362421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331967449197087287574947 497951173795630931362421)
                ·
                  refine ⟨46682922543340399815227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 497951173795630931362421 46682922543340399815227)
                  ·
                    rfl

theorem cell21_204558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_204558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204558 prefixEnd_204558 := by exact prefixLift 204558
  have htrace : WordTrace (prefixWord ++ tailWord_204558) baseStart_204558 baseEnd_204558 := by
    simpa [prefixWord, tailWord_204558, baseEnd_204558] using wordTrace_append hprefix tailTrace_204558
  have hstable : (prefixWord ++ tailWord_204558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204558).length < 2 ^ (prefixWord ++ tailWord_204558).sum := by decide
  have hdescent : baseEnd_204558 < baseStart_204558 := by decide
  rcases family_descends (prefixWord ++ tailWord_204558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204564 : List Nat := [2, 4, 4, 1, 1, 1, 1, 3, 4]
def baseStart_204564 : Nat := 118140960795 + 204564 * 2 ^ 59
def prefixEnd_204564 : Nat := 4983230072969 + 3 ^ 40 * 204564 * 2
def baseEnd_204564 : Nat := 46684291825085722715215

theorem tailTrace_204564 : CollatzResearch.WordTrace tailWord_204564 prefixEnd_204564 46684291825085722715215 := by
  unfold tailWord_204564
  simp only [CollatzResearch.WordTrace]
  refine ⟨3730531015453519797426373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4974041353938026396568497 3730531015453519797426373)
  ·
    refine ⟨699474565397534962017445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3730531015453519797426373 699474565397534962017445)
    ·
      refine ⟨131151481012037805378271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 699474565397534962017445 131151481012037805378271)
      ·
        refine ⟨196727221518056708067407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131151481012037805378271 196727221518056708067407)
        ·
          refine ⟨295090832277085062101111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196727221518056708067407 295090832277085062101111)
          ·
            refine ⟨442636248415627593151667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295090832277085062101111 442636248415627593151667)
            ·
              refine ⟨663954372623441389727501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442636248415627593151667 663954372623441389727501)
              ·
                refine ⟨248982889733790521147813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 663954372623441389727501 248982889733790521147813)
                ·
                  refine ⟨46684291825085722715215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248982889733790521147813 46684291825085722715215)
                  ·
                    rfl

theorem cell21_204564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_204564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204564 prefixEnd_204564 := by exact prefixLift 204564
  have htrace : WordTrace (prefixWord ++ tailWord_204564) baseStart_204564 baseEnd_204564 := by
    simpa [prefixWord, tailWord_204564, baseEnd_204564] using wordTrace_append hprefix tailTrace_204564
  have hstable : (prefixWord ++ tailWord_204564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204564).length < 2 ^ (prefixWord ++ tailWord_204564).sum := by decide
  have hdescent : baseEnd_204564 < baseStart_204564 := by decide
  rcases family_descends (prefixWord ++ tailWord_204564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204606 : List Nat := [4, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_204606 : Nat := 118140960795 + 204606 * 2 ^ 59
def prefixEnd_204606 : Nat := 4983230072969 + 3 ^ 40 * 204606 * 2
def baseEnd_204606 : Nat := 46693876797302983015129

theorem tailTrace_204606 : CollatzResearch.WordTrace tailWord_204606 prefixEnd_204606 46693876797302983015129 := by
  unfold tailWord_204606
  simp only [CollatzResearch.WordTrace]
  refine ⟨932824237094360095985209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4975062597836587178587781 932824237094360095985209)
  ·
    refine ⟨699618177820770071988907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 932824237094360095985209 699618177820770071988907)
    ·
      refine ⟨1049427266731155107983361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 699618177820770071988907 1049427266731155107983361)
      ·
        refine ⟨787070450048366330987521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1049427266731155107983361 787070450048366330987521)
        ·
          refine ⟨590302837536274748240641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 787070450048366330987521 590302837536274748240641)
          ·
            refine ⟨442727128152206061180481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 590302837536274748240641 442727128152206061180481)
            ·
              refine ⟨332045346114154545885361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442727128152206061180481 332045346114154545885361)
              ·
                refine ⟨249034009585615909414021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 332045346114154545885361 249034009585615909414021)
                ·
                  refine ⟨46693876797302983015129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 249034009585615909414021 46693876797302983015129)
                  ·
                    rfl

theorem cell21_204606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_204606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204606 prefixEnd_204606 := by exact prefixLift 204606
  have htrace : WordTrace (prefixWord ++ tailWord_204606) baseStart_204606 baseEnd_204606 := by
    simpa [prefixWord, tailWord_204606, baseEnd_204606] using wordTrace_append hprefix tailTrace_204606
  have hstable : (prefixWord ++ tailWord_204606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204606).length < 2 ^ (prefixWord ++ tailWord_204606).sum := by decide
  have hdescent : baseEnd_204606 < baseStart_204606 := by decide
  rcases family_descends (prefixWord ++ tailWord_204606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204617 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 5]
def baseStart_204617 : Nat := 118140960795 + 204617 * 2 ^ 59
def prefixEnd_204617 : Nat := 4983230072969 + 3 ^ 40 * 204617 * 2
def baseEnd_204617 : Nat := 46696387147169408331773

theorem tailTrace_204617 : CollatzResearch.WordTrace tailWord_204617 prefixEnd_204617 46696387147169408331773 := by
  unfold tailWord_204617
  simp only [CollatzResearch.WordTrace]
  refine ⟨7462995099715029646532105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4975330066476686431021403 7462995099715029646532105)
  ·
    refine ⟨5597246324786272234899079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7462995099715029646532105 5597246324786272234899079)
    ·
      refine ⟨8395869487179408352348619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5597246324786272234899079 8395869487179408352348619)
      ·
        refine ⟨12593804230769112528522929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8395869487179408352348619 12593804230769112528522929)
        ·
          refine ⟨9445353173076834396392197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12593804230769112528522929 9445353173076834396392197)
          ·
            refine ⟨1771003719951906449323537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9445353173076834396392197 1771003719951906449323537)
            ·
              refine ⟨1328252789963929836992653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1771003719951906449323537 1328252789963929836992653)
              ·
                refine ⟨498094796236473688872245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1328252789963929836992653 498094796236473688872245)
                ·
                  refine ⟨46696387147169408331773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 498094796236473688872245 46696387147169408331773)
                  ·
                    rfl

theorem cell21_204617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_204617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204617 prefixEnd_204617 := by exact prefixLift 204617
  have htrace : WordTrace (prefixWord ++ tailWord_204617) baseStart_204617 baseEnd_204617 := by
    simpa [prefixWord, tailWord_204617, baseEnd_204617] using wordTrace_append hprefix tailTrace_204617
  have hstable : (prefixWord ++ tailWord_204617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204617).length < 2 ^ (prefixWord ++ tailWord_204617).sum := by decide
  have hdescent : baseEnd_204617 < baseStart_204617 := by decide
  rcases family_descends (prefixWord ++ tailWord_204617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204620 : List Nat := [2, 2, 1, 3, 4, 2, 1, 6]
def baseStart_204620 : Nat := 118140960795 + 204620 * 2 ^ 59
def prefixEnd_204620 : Nat := 4983230072969 + 3 ^ 40 * 204620 * 2
def baseEnd_204620 : Nat := 15565690596014023260589

theorem tailTrace_204620 : CollatzResearch.WordTrace tailWord_204620 prefixEnd_204620 15565690596014023260589 := by
  unfold tailWord_204620
  simp only [CollatzResearch.WordTrace]
  refine ⟨3731552259352080579445657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4975403012469440772594209 3731552259352080579445657)
  ·
    refine ⟨2798664194514060434584243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3731552259352080579445657 2798664194514060434584243)
    ·
      refine ⟨4197996291771090651876365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2798664194514060434584243 4197996291771090651876365)
      ·
        refine ⟨1574248609414158994453637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4197996291771090651876365 1574248609414158994453637)
        ·
          refine ⟨295171614265154811460057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1574248609414158994453637 295171614265154811460057)
          ·
            refine ⟨221378710698866108595043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295171614265154811460057 221378710698866108595043)
            ·
              refine ⟨332068066048299162892565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221378710698866108595043 332068066048299162892565)
              ·
                refine ⟨15565690596014023260589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 332068066048299162892565 15565690596014023260589)
                ·
                  rfl

theorem cell21_204620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 6].length) (baseStart_204620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204620 prefixEnd_204620 := by exact prefixLift 204620
  have htrace : WordTrace (prefixWord ++ tailWord_204620) baseStart_204620 baseEnd_204620 := by
    simpa [prefixWord, tailWord_204620, baseEnd_204620] using wordTrace_append hprefix tailTrace_204620
  have hstable : (prefixWord ++ tailWord_204620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204620).length < 2 ^ (prefixWord ++ tailWord_204620).sum := by decide
  have hdescent : baseEnd_204620 < baseStart_204620 := by decide
  rcases family_descends (prefixWord ++ tailWord_204620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204648 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 6]
def baseStart_204648 : Nat := 118140960795 + 204648 * 2 ^ 59
def prefixEnd_204648 : Nat := 4983230072969 + 3 ^ 40 * 204648 * 2
def baseEnd_204648 : Nat := 46703461769520243315043

theorem tailTrace_204648 : CollatzResearch.WordTrace tailWord_204648 prefixEnd_204648 46703461769520243315043 := by
  unfold tailWord_204648
  simp only [CollatzResearch.WordTrace]
  refine ⟨3732062881301360970455299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4976083841735147960607065 3732062881301360970455299)
  ·
    refine ⟨5598094321952041455682949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3732062881301360970455299 5598094321952041455682949)
    ·
      refine ⟨1049642685366007772940553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5598094321952041455682949 1049642685366007772940553)
      ·
        refine ⟨787232014024505829705415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1049642685366007772940553 787232014024505829705415)
        ·
          refine ⟨1180848021036758744558123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787232014024505829705415 1180848021036758744558123)
          ·
            refine ⟨1771272031555138116837185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180848021036758744558123 1771272031555138116837185)
            ·
              refine ⟨1328454023666353587627889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1771272031555138116837185 1328454023666353587627889)
              ·
                refine ⟨996340517749765190720917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1328454023666353587627889 996340517749765190720917)
                ·
                  refine ⟨46703461769520243315043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 996340517749765190720917 46703461769520243315043)
                  ·
                    rfl

theorem cell21_204648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_204648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204648 prefixEnd_204648 := by exact prefixLift 204648
  have htrace : WordTrace (prefixWord ++ tailWord_204648) baseStart_204648 baseEnd_204648 := by
    simpa [prefixWord, tailWord_204648, baseEnd_204648] using wordTrace_append hprefix tailTrace_204648
  have hstable : (prefixWord ++ tailWord_204648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204648).length < 2 ^ (prefixWord ++ tailWord_204648).sum := by decide
  have hdescent : baseEnd_204648 < baseStart_204648 := by decide
  rcases family_descends (prefixWord ++ tailWord_204648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204693 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 5]
def baseStart_204693 : Nat := 118140960795 + 204693 * 2 ^ 59
def prefixEnd_204693 : Nat := 4983230072969 + 3 ^ 40 * 204693 * 2
def baseEnd_204693 : Nat := 46713731382610165064951

theorem tailTrace_204693 : CollatzResearch.WordTrace tailWord_204693 prefixEnd_204693 46713731382610165064951 := by
  unfold tailWord_204693
  simp only [CollatzResearch.WordTrace]
  refine ⟨7465767047439694626298733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4977178031626463084199155 7465767047439694626298733)
  ·
    refine ⟨2799662642789885484862025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7465767047439694626298733 2799662642789885484862025)
    ·
      refine ⟨2099746982092414113646519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2799662642789885484862025 2099746982092414113646519)
      ·
        refine ⟨3149620473138621170469779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2099746982092414113646519 3149620473138621170469779)
        ·
          refine ⟨4724430709707931755704669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149620473138621170469779 4724430709707931755704669)
          ·
            refine ⟨1771661516140474408389251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4724430709707931755704669 1771661516140474408389251)
            ·
              refine ⟨2657492274210711612583877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771661516140474408389251 2657492274210711612583877)
              ·
                refine ⟨498279801414508427359477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2657492274210711612583877 498279801414508427359477)
                ·
                  refine ⟨46713731382610165064951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 498279801414508427359477 46713731382610165064951)
                  ·
                    rfl

theorem cell21_204693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_204693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204693 prefixEnd_204693 := by exact prefixLift 204693
  have htrace : WordTrace (prefixWord ++ tailWord_204693) baseStart_204693 baseEnd_204693 := by
    simpa [prefixWord, tailWord_204693, baseEnd_204693] using wordTrace_append hprefix tailTrace_204693
  have hstable : (prefixWord ++ tailWord_204693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204693).length < 2 ^ (prefixWord ++ tailWord_204693).sum := by decide
  have hdescent : baseEnd_204693 < baseStart_204693 := by decide
  rcases family_descends (prefixWord ++ tailWord_204693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204696 : List Nat := [2, 1, 2, 6, 1, 1, 1, 7]
def baseStart_204696 : Nat := 118140960795 + 204696 * 2 ^ 59
def prefixEnd_204696 : Nat := 4983230072969 + 3 ^ 40 * 204696 * 2
def baseEnd_204696 : Nat := 15571472007827608838315

theorem tailTrace_204696 : CollatzResearch.WordTrace tailWord_204696 prefixEnd_204696 15571472007827608838315 := by
  unfold tailWord_204696
  simp only [CollatzResearch.WordTrace]
  refine ⟨3732938233214413069328971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4977250977619217425771961 3732938233214413069328971)
  ·
    refine ⟨5599407349821619603993457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3732938233214413069328971 5599407349821619603993457)
    ·
      refine ⟨4199555512366214702995093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5599407349821619603993457 4199555512366214702995093)
      ·
        refine ⟨196854164642166314202895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4199555512366214702995093 196854164642166314202895)
        ·
          refine ⟨295281246963249471304343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196854164642166314202895 295281246963249471304343)
          ·
            refine ⟨442921870444874206956515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295281246963249471304343 442921870444874206956515)
            ·
              refine ⟨664382805667311310434773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442921870444874206956515 664382805667311310434773)
              ·
                refine ⟨15571472007827608838315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 664382805667311310434773 15571472007827608838315)
                ·
                  rfl

theorem cell21_204696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 7].length) (baseStart_204696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204696 prefixEnd_204696 := by exact prefixLift 204696
  have htrace : WordTrace (prefixWord ++ tailWord_204696) baseStart_204696 baseEnd_204696 := by
    simpa [prefixWord, tailWord_204696, baseEnd_204696] using wordTrace_append hprefix tailTrace_204696
  have hstable : (prefixWord ++ tailWord_204696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204696).length < 2 ^ (prefixWord ++ tailWord_204696).sum := by decide
  have hdescent : baseEnd_204696 < baseStart_204696 := by decide
  rcases family_descends (prefixWord ++ tailWord_204696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204702 : List Nat := [4, 3, 1, 3, 1, 2, 1, 3, 3]
def baseStart_204702 : Nat := 118140960795 + 204702 * 2 ^ 59
def prefixEnd_204702 : Nat := 4983230072969 + 3 ^ 40 * 204702 * 2
def baseEnd_204702 : Nat := 46715785305228149414933

theorem tailTrace_204702 : CollatzResearch.WordTrace tailWord_204702 prefixEnd_204702 46715785305228149414933 := by
  unfold tailWord_204702
  simp only [CollatzResearch.WordTrace]
  refine ⟨933261913050886145422045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4977396869604726108917573 933261913050886145422045)
  ·
    refine ⟨349973217394082304533267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 933261913050886145422045 349973217394082304533267)
    ·
      refine ⟨524959826091123456799901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349973217394082304533267 524959826091123456799901)
      ·
        refine ⟨196859934784171296299963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 524959826091123456799901 196859934784171296299963)
        ·
          refine ⟨295289902176256944449945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196859934784171296299963 295289902176256944449945)
          ·
            refine ⟨221467426632192708337459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295289902176256944449945 221467426632192708337459)
            ·
              refine ⟨332201139948289062506189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221467426632192708337459 332201139948289062506189)
              ·
                refine ⟨124575427480608398439821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332201139948289062506189 124575427480608398439821)
                ·
                  refine ⟨46715785305228149414933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124575427480608398439821 46715785305228149414933)
                  ·
                    rfl

theorem cell21_204702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_204702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204702 prefixEnd_204702 := by exact prefixLift 204702
  have htrace : WordTrace (prefixWord ++ tailWord_204702) baseStart_204702 baseEnd_204702 := by
    simpa [prefixWord, tailWord_204702, baseEnd_204702] using wordTrace_append hprefix tailTrace_204702
  have hstable : (prefixWord ++ tailWord_204702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204702).length < 2 ^ (prefixWord ++ tailWord_204702).sum := by decide
  have hdescent : baseEnd_204702 < baseStart_204702 := by decide
  rcases family_descends (prefixWord ++ tailWord_204702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204893 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 6]
def baseStart_204893 : Nat := 118140960795 + 204893 * 2 ^ 59
def prefixEnd_204893 : Nat := 4983230072969 + 3 ^ 40 * 204893 * 2
def baseEnd_204893 : Nat := 46759374107454261731209

theorem tailTrace_204893 : CollatzResearch.WordTrace tailWord_204893 prefixEnd_204893 46759374107454261731209 := by
  unfold tailWord_204893
  simp only [CollatzResearch.WordTrace]
  refine ⟨7473061646715128783579333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4982041097810085855719555 7473061646715128783579333)
  ·
    refine ⟨1401199058759086646921125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7473061646715128783579333 1401199058759086646921125)
    ·
      refine ⟨262724823517328746297711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1401199058759086646921125 262724823517328746297711)
      ·
        refine ⟨394087235275993119446567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262724823517328746297711 394087235275993119446567)
        ·
          refine ⟨591130852913989679169851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394087235275993119446567 591130852913989679169851)
          ·
            refine ⟨886696279370984518754777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591130852913989679169851 886696279370984518754777)
            ·
              refine ⟨665022209528238389066083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 886696279370984518754777 665022209528238389066083)
              ·
                refine ⟨997533314292357583599125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665022209528238389066083 997533314292357583599125)
                ·
                  refine ⟨46759374107454261731209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 997533314292357583599125 46759374107454261731209)
                  ·
                    rfl

theorem cell21_204893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_204893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204893 prefixEnd_204893 := by exact prefixLift 204893
  have htrace : WordTrace (prefixWord ++ tailWord_204893) baseStart_204893 baseEnd_204893 := by
    simpa [prefixWord, tailWord_204893, baseEnd_204893] using wordTrace_append hprefix tailTrace_204893
  have hstable : (prefixWord ++ tailWord_204893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204893).length < 2 ^ (prefixWord ++ tailWord_204893).sum := by decide
  have hdescent : baseEnd_204893 < baseStart_204893 := by decide
  rcases family_descends (prefixWord ++ tailWord_204893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204935 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 8]
def baseStart_204935 : Nat := 118140960795 + 204935 * 2 ^ 59
def prefixEnd_204935 : Nat := 4983230072969 + 3 ^ 40 * 204935 * 2
def baseEnd_204935 : Nat := 46768959079671522031123

theorem tailTrace_204935 : CollatzResearch.WordTrace tailWord_204935 prefixEnd_204935 46768959079671522031123 := by
  unfold tailWord_204935
  simp only [CollatzResearch.WordTrace]
  refine ⟨7474593512562969956608259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4983062341708646637738839 7474593512562969956608259)
  ·
    refine ⟨11211890268844454934912389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7474593512562969956608259 11211890268844454934912389)
    ·
      refine ⟨2102229425408335300296073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11211890268844454934912389 2102229425408335300296073)
      ·
        refine ⟨1576672069056251475222055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2102229425408335300296073 1576672069056251475222055)
        ·
          refine ⟨2365008103584377212833083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1576672069056251475222055 2365008103584377212833083)
          ·
            refine ⟨3547512155376565819249625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2365008103584377212833083 3547512155376565819249625)
            ·
              refine ⟨2660634116532424364437219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3547512155376565819249625 2660634116532424364437219)
              ·
                refine ⟨3990951174798636546655829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2660634116532424364437219 3990951174798636546655829)
                ·
                  refine ⟨46768959079671522031123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3990951174798636546655829 46768959079671522031123)
                  ·
                    rfl

theorem cell21_204935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 8].length) (baseStart_204935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204935 prefixEnd_204935 := by exact prefixLift 204935
  have htrace : WordTrace (prefixWord ++ tailWord_204935) baseStart_204935 baseEnd_204935 := by
    simpa [prefixWord, tailWord_204935, baseEnd_204935] using wordTrace_append hprefix tailTrace_204935
  have hstable : (prefixWord ++ tailWord_204935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204935).length < 2 ^ (prefixWord ++ tailWord_204935).sum := by decide
  have hdescent : baseEnd_204935 < baseStart_204935 := by decide
  rcases family_descends (prefixWord ++ tailWord_204935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204983 : List Nat := [1, 1, 3, 1, 4, 3, 3, 5]
def baseStart_204983 : Nat := 118140960795 + 204983 * 2 ^ 59
def prefixEnd_204983 : Nat := 4983230072969 + 3 ^ 40 * 204983 * 2
def baseEnd_204983 : Nat := 15593304444544701743675

theorem tailTrace_204983 : CollatzResearch.WordTrace tailWord_204983 prefixEnd_204983 15593304444544701743675 := by
  unfold tailWord_204983
  simp only [CollatzResearch.WordTrace]
  refine ⟨7476344216389074154355603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4984229477592716102903735 7476344216389074154355603)
  ·
    refine ⟨11214516324583611231533405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7476344216389074154355603 11214516324583611231533405)
    ·
      refine ⟨4205443621718854211825027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11214516324583611231533405 4205443621718854211825027)
      ·
        refine ⟨6308165432578281317737541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4205443621718854211825027 6308165432578281317737541)
        ·
          refine ⟨1182781018608427747075789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6308165432578281317737541 1182781018608427747075789)
          ·
            refine ⟨443542881978160405153421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1182781018608427747075789 443542881978160405153421)
            ·
              refine ⟨166328580741810151932533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 443542881978160405153421 166328580741810151932533)
              ·
                refine ⟨15593304444544701743675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166328580741810151932533 15593304444544701743675)
                ·
                  rfl

theorem cell21_204983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 5].length) (baseStart_204983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_204983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_204983 prefixEnd_204983 := by exact prefixLift 204983
  have htrace : WordTrace (prefixWord ++ tailWord_204983) baseStart_204983 baseEnd_204983 := by
    simpa [prefixWord, tailWord_204983, baseEnd_204983] using wordTrace_append hprefix tailTrace_204983
  have hstable : (prefixWord ++ tailWord_204983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204983).length < 2 ^ (prefixWord ++ tailWord_204983).sum := by decide
  have hdescent : baseEnd_204983 < baseStart_204983 := by decide
  rcases family_descends (prefixWord ++ tailWord_204983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205056 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 7]
def baseStart_205056 : Nat := 118140960795 + 205056 * 2 ^ 59
def prefixEnd_205056 : Nat := 4983230072969 + 3 ^ 40 * 205056 * 2
def baseEnd_205056 : Nat := 46796572928202200514209

theorem tailTrace_205056 : CollatzResearch.WordTrace tailWord_205056 prefixEnd_205056 46796572928202200514209 := by
  unfold tailWord_205056
  simp only [CollatzResearch.WordTrace]
  refine ⟨3739503372562303810881511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4986004496749738414508681 3739503372562303810881511)
  ·
    refine ⟨5609255058843455716322267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3739503372562303810881511 5609255058843455716322267)
    ·
      refine ⟨8413882588265183574483401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5609255058843455716322267 8413882588265183574483401)
      ·
        refine ⟨6310411941198887680862551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8413882588265183574483401 6310411941198887680862551)
        ·
          refine ⟨9465617911798331521293827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6310411941198887680862551 9465617911798331521293827)
          ·
            refine ⟨14198426867697497281940741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9465617911798331521293827 14198426867697497281940741)
            ·
              refine ⟨2662205037693280740363889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14198426867697497281940741 2662205037693280740363889)
              ·
                refine ⟨1996653778269960555272917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2662205037693280740363889 1996653778269960555272917)
                ·
                  refine ⟨46796572928202200514209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1996653778269960555272917 46796572928202200514209)
                  ·
                    rfl

theorem cell21_205056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_205056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205056 prefixEnd_205056 := by exact prefixLift 205056
  have htrace : WordTrace (prefixWord ++ tailWord_205056) baseStart_205056 baseEnd_205056 := by
    simpa [prefixWord, tailWord_205056, baseEnd_205056] using wordTrace_append hprefix tailTrace_205056
  have hstable : (prefixWord ++ tailWord_205056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205056).length < 2 ^ (prefixWord ++ tailWord_205056).sum := by decide
  have hdescent : baseEnd_205056 < baseStart_205056 := by decide
  rcases family_descends (prefixWord ++ tailWord_205056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205073 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 5]
def baseStart_205073 : Nat := 118140960795 + 205073 * 2 ^ 59
def prefixEnd_205073 : Nat := 4983230072969 + 3 ^ 40 * 205073 * 2
def baseEnd_205073 : Nat := 46800452559813948730841

theorem tailTrace_205073 : CollatzResearch.WordTrace tailWord_205073 prefixEnd_205073 46800452559813948730841 := by
  unfold tailWord_205073
  simp only [CollatzResearch.WordTrace]
  refine ⟨7479626786063019525131873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4986417857375346350087915 7479626786063019525131873)
  ·
    refine ⟨5609720089547264643848905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7479626786063019525131873 5609720089547264643848905)
    ·
      refine ⟨4207290067160448482886679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5609720089547264643848905 4207290067160448482886679)
      ·
        refine ⟨6310935100740672724330019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4207290067160448482886679 6310935100740672724330019)
        ·
          refine ⟨9466402651111009086495029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6310935100740672724330019 9466402651111009086495029)
          ·
            refine ⟨887475248541657101858909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9466402651111009086495029 887475248541657101858909)
            ·
              refine ⟨332803218203121413197091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 887475248541657101858909 332803218203121413197091)
              ·
                refine ⟨499204827304682119795637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332803218203121413197091 499204827304682119795637)
                ·
                  refine ⟨46800452559813948730841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 499204827304682119795637 46800452559813948730841)
                  ·
                    rfl

theorem cell21_205073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_205073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205073 prefixEnd_205073 := by exact prefixLift 205073
  have htrace : WordTrace (prefixWord ++ tailWord_205073) baseStart_205073 baseEnd_205073 := by
    simpa [prefixWord, tailWord_205073, baseEnd_205073] using wordTrace_append hprefix tailTrace_205073
  have hstable : (prefixWord ++ tailWord_205073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205073).length < 2 ^ (prefixWord ++ tailWord_205073).sum := by decide
  have hdescent : baseEnd_205073 < baseStart_205073 := by decide
  rcases family_descends (prefixWord ++ tailWord_205073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205118 : List Nat := [4, 2, 1, 2, 1, 11]
def baseStart_205118 : Nat := 118140960795 + 205118 * 2 ^ 59
def prefixEnd_205118 : Nat := 4983230072969 + 3 ^ 40 * 205118 * 2
def baseEnd_205118 : Nat := 1733730450848291499287

theorem tailTrace_205118 : CollatzResearch.WordTrace tailWord_205118 prefixEnd_205118 1733730450848291499287 := by
  unfold tailWord_205118
  simp only [CollatzResearch.WordTrace]
  refine ⟨935158508862499026315001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4987512047266661473680005 935158508862499026315001)
  ·
    refine ⟨701368881646874269736251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 935158508862499026315001 701368881646874269736251)
    ·
      refine ⟨1052053322470311404604377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 701368881646874269736251 1052053322470311404604377)
      ·
        refine ⟨789039991852733553453283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1052053322470311404604377 789039991852733553453283)
        ·
          refine ⟨1183559987779100330179925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789039991852733553453283 1183559987779100330179925)
          ·
            refine ⟨1733730450848291499287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1183559987779100330179925 1733730450848291499287)
            ·
              rfl

theorem cell21_205118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 11].length) (baseStart_205118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205118 prefixEnd_205118 := by exact prefixLift 205118
  have htrace : WordTrace (prefixWord ++ tailWord_205118) baseStart_205118 baseEnd_205118 := by
    simpa [prefixWord, tailWord_205118, baseEnd_205118] using wordTrace_append hprefix tailTrace_205118
  have hstable : (prefixWord ++ tailWord_205118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205118).length < 2 ^ (prefixWord ++ tailWord_205118).sum := by decide
  have hdescent : baseEnd_205118 < baseStart_205118 := by decide
  rcases family_descends (prefixWord ++ tailWord_205118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205124 : List Nat := [2, 3, 4, 1, 2, 1, 1, 4, 3]
def baseStart_205124 : Nat := 118140960795 + 205124 * 2 ^ 59
def prefixEnd_205124 : Nat := 4983230072969 + 3 ^ 40 * 205124 * 2
def baseEnd_205124 : Nat := 46812091454649193380737

theorem tailTrace_205124 : CollatzResearch.WordTrace tailWord_205124 prefixEnd_205124 46812091454649193380737 := by
  unfold tailWord_205124
  simp only [CollatzResearch.WordTrace]
  refine ⟨3740743454439127617619213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4987657939252170156825617 3740743454439127617619213)
  ·
    refine ⟨1402778795414672856607205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3740743454439127617619213 1402778795414672856607205)
    ·
      refine ⟨263021024140251160613851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1402778795414672856607205 263021024140251160613851)
      ·
        refine ⟨394531536210376740920777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263021024140251160613851 394531536210376740920777)
        ·
          refine ⟨295898652157782555690583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394531536210376740920777 295898652157782555690583)
          ·
            refine ⟨443847978236673833535875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295898652157782555690583 443847978236673833535875)
            ·
              refine ⟨665771967355010750303813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443847978236673833535875 665771967355010750303813)
              ·
                refine ⟨124832243879064515681965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 665771967355010750303813 124832243879064515681965)
                ·
                  refine ⟨46812091454649193380737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124832243879064515681965 46812091454649193380737)
                  ·
                    rfl

theorem cell21_205124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_205124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205124 prefixEnd_205124 := by exact prefixLift 205124
  have htrace : WordTrace (prefixWord ++ tailWord_205124) baseStart_205124 baseEnd_205124 := by
    simpa [prefixWord, tailWord_205124, baseEnd_205124] using wordTrace_append hprefix tailTrace_205124
  have hstable : (prefixWord ++ tailWord_205124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205124).length < 2 ^ (prefixWord ++ tailWord_205124).sum := by decide
  have hdescent : baseEnd_205124 < baseStart_205124 := by decide
  rcases family_descends (prefixWord ++ tailWord_205124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205217 : List Nat := [1, 2, 3, 5, 2, 1, 1, 3, 3]
def baseStart_205217 : Nat := 118140960795 + 205217 * 2 ^ 59
def prefixEnd_205217 : Nat := 4983230072969 + 3 ^ 40 * 205217 * 2
def baseEnd_205217 : Nat := 46833315321701698330547

theorem tailTrace_205217 : CollatzResearch.WordTrace tailWord_205217 prefixEnd_205217 46833315321701698330547 := by
  unfold tailWord_205217
  simp only [CollatzResearch.WordTrace]
  refine ⟨7484878897541332118373905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4989919265027554745582603 7484878897541332118373905)
  ·
    refine ⟨5613659173155999088780429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7484878897541332118373905 5613659173155999088780429)
    ·
      refine ⟨2105122189933499658292661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5613659173155999088780429 2105122189933499658292661)
      ·
        refine ⟨197355205306265592964937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2105122189933499658292661 197355205306265592964937)
        ·
          refine ⟨148016403979699194723703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197355205306265592964937 148016403979699194723703)
          ·
            refine ⟨222024605969548792085555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148016403979699194723703 222024605969548792085555)
            ·
              refine ⟨333036908954323188128333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222024605969548792085555 333036908954323188128333)
              ·
                refine ⟨124888840857871195548125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 333036908954323188128333 124888840857871195548125)
                ·
                  refine ⟨46833315321701698330547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124888840857871195548125 46833315321701698330547)
                  ·
                    rfl

theorem cell21_205217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 3].length) (baseStart_205217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205217 prefixEnd_205217 := by exact prefixLift 205217
  have htrace : WordTrace (prefixWord ++ tailWord_205217) baseStart_205217 baseEnd_205217 := by
    simpa [prefixWord, tailWord_205217, baseEnd_205217] using wordTrace_append hprefix tailTrace_205217
  have hstable : (prefixWord ++ tailWord_205217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205217).length < 2 ^ (prefixWord ++ tailWord_205217).sum := by decide
  have hdescent : baseEnd_205217 < baseStart_205217 := by decide
  rcases family_descends (prefixWord ++ tailWord_205217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205239 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 6]
def baseStart_205239 : Nat := 118140960795 + 205239 * 2 ^ 59
def prefixEnd_205239 : Nat := 4983230072969 + 3 ^ 40 * 205239 * 2
def baseEnd_205239 : Nat := 46838336021434548963835

theorem tailTrace_205239 : CollatzResearch.WordTrace tailWord_205239 prefixEnd_205239 46838336021434548963835 := by
  unfold tailWord_205239
  simp only [CollatzResearch.WordTrace]
  refine ⟨7485681303461629875674771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4990454202307753250449847 7485681303461629875674771)
  ·
    refine ⟨11228521955192444813512157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7485681303461629875674771 11228521955192444813512157)
    ·
      refine ⟨4210695733197166805067059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11228521955192444813512157 4210695733197166805067059)
      ·
        refine ⟨6316043599795750207600589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4210695733197166805067059 6316043599795750207600589)
        ·
          refine ⟨2368516349923406327850221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6316043599795750207600589 2368516349923406327850221)
          ·
            refine ⟨888193631221277372943833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2368516349923406327850221 888193631221277372943833)
            ·
              refine ⟨666145223415958029707875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888193631221277372943833 666145223415958029707875)
              ·
                refine ⟨999217835123937044561813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666145223415958029707875 999217835123937044561813)
                ·
                  refine ⟨46838336021434548963835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 999217835123937044561813 46838336021434548963835)
                  ·
                    rfl

theorem cell21_205239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 6].length) (baseStart_205239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205239 prefixEnd_205239 := by exact prefixLift 205239
  have htrace : WordTrace (prefixWord ++ tailWord_205239) baseStart_205239 baseEnd_205239 := by
    simpa [prefixWord, tailWord_205239, baseEnd_205239] using wordTrace_append hprefix tailTrace_205239
  have hstable : (prefixWord ++ tailWord_205239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205239).length < 2 ^ (prefixWord ++ tailWord_205239).sum := by decide
  have hdescent : baseEnd_205239 < baseStart_205239 := by decide
  rcases family_descends (prefixWord ++ tailWord_205239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205256 : List Nat := [2, 1, 3, 1, 3, 3, 1, 3, 4]
def baseStart_205256 : Nat := 118140960795 + 205256 * 2 ^ 59
def prefixEnd_205256 : Nat := 4983230072969 + 3 ^ 40 * 205256 * 2
def baseEnd_205256 : Nat := 46842215653046297180467

theorem tailTrace_205256 : CollatzResearch.WordTrace tailWord_205256 prefixEnd_205256 46842215653046297180467 := by
  unfold tailWord_205256
  simp only [CollatzResearch.WordTrace]
  refine ⟨3743150672200020889521811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4990867562933361186029081 3743150672200020889521811)
  ·
    refine ⟨5614726008300031334282717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3743150672200020889521811 5614726008300031334282717)
    ·
      refine ⟨2105522253112511750356019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5614726008300031334282717 2105522253112511750356019)
      ·
        refine ⟨3158283379668767625534029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2105522253112511750356019 3158283379668767625534029)
        ·
          refine ⟨1184356267375787859575261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3158283379668767625534029 1184356267375787859575261)
          ·
            refine ⟨444133600265920447340723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1184356267375787859575261 444133600265920447340723)
            ·
              refine ⟨666200400398880671011085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444133600265920447340723 666200400398880671011085)
              ·
                refine ⟨249825150149580251629157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 666200400398880671011085 249825150149580251629157)
                ·
                  refine ⟨46842215653046297180467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 249825150149580251629157 46842215653046297180467)
                  ·
                    rfl

theorem cell21_205256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_205256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205256 prefixEnd_205256 := by exact prefixLift 205256
  have htrace : WordTrace (prefixWord ++ tailWord_205256) baseStart_205256 baseEnd_205256 := by
    simpa [prefixWord, tailWord_205256, baseEnd_205256] using wordTrace_append hprefix tailTrace_205256
  have hstable : (prefixWord ++ tailWord_205256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205256).length < 2 ^ (prefixWord ++ tailWord_205256).sum := by decide
  have hdescent : baseEnd_205256 < baseStart_205256 := by decide
  rcases family_descends (prefixWord ++ tailWord_205256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205315 : List Nat := [1, 1, 1, 3, 2, 1, 3, 5, 4]
def baseStart_205315 : Nat := 118140960795 + 205315 * 2 ^ 59
def prefixEnd_205315 : Nat := 4983230072969 + 3 ^ 40 * 205315 * 2
def baseEnd_205315 : Nat := 46855680256875305697013

theorem tailTrace_205315 : CollatzResearch.WordTrace tailWord_205315 prefixEnd_205315 46855680256875305697013 := by
  unfold tailWord_205315
  simp only [CollatzResearch.WordTrace]
  refine ⟨7488453251186294855441399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4992302167457529903627599 7488453251186294855441399)
  ·
    refine ⟨11232679876779442283162099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7488453251186294855441399 11232679876779442283162099)
    ·
      refine ⟨16849019815169163424743149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11232679876779442283162099 16849019815169163424743149)
      ·
        refine ⟨6318382430688436284278681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16849019815169163424743149 6318382430688436284278681)
        ·
          refine ⟨4738786823016327213209011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6318382430688436284278681 4738786823016327213209011)
          ·
            refine ⟨7108180234524490819813517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4738786823016327213209011 7108180234524490819813517)
            ·
              refine ⟨2665567587946684057430069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7108180234524490819813517 2665567587946684057430069)
              ·
                refine ⟨249896961370001630384069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2665567587946684057430069 249896961370001630384069)
                ·
                  refine ⟨46855680256875305697013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 249896961370001630384069 46855680256875305697013)
                  ·
                    rfl

theorem cell21_205315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 4].length) (baseStart_205315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205315 prefixEnd_205315 := by exact prefixLift 205315
  have htrace : WordTrace (prefixWord ++ tailWord_205315) baseStart_205315 baseEnd_205315 := by
    simpa [prefixWord, tailWord_205315, baseEnd_205315] using wordTrace_append hprefix tailTrace_205315
  have hstable : (prefixWord ++ tailWord_205315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205315).length < 2 ^ (prefixWord ++ tailWord_205315).sum := by decide
  have hdescent : baseEnd_205315 < baseStart_205315 := by decide
  rcases family_descends (prefixWord ++ tailWord_205315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205360 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 5]
def baseStart_205360 : Nat := 118140960795 + 205360 * 2 ^ 59
def prefixEnd_205360 : Nat := 4983230072969 + 3 ^ 40 * 205360 * 2
def baseEnd_205360 : Nat := 46865949869965227446921

theorem tailTrace_205360 : CollatzResearch.WordTrace tailWord_205360 prefixEnd_205360 46865949869965227446921 := by
  unfold tailWord_205360
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745047268011633770414767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4993396357348845027219689 3745047268011633770414767)
  ·
    refine ⟨5617570902017450655622151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3745047268011633770414767 5617570902017450655622151)
    ·
      refine ⟨8426356353026175983433227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5617570902017450655622151 8426356353026175983433227)
      ·
        refine ⟨12639534529539263975149841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8426356353026175983433227 12639534529539263975149841)
        ·
          refine ⟨9479650897154447981362381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12639534529539263975149841 9479650897154447981362381)
          ·
            refine ⟨3554869086432917993010893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9479650897154447981362381 3554869086432917993010893)
            ·
              refine ⟨1333075907412344247379085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3554869086432917993010893 1333075907412344247379085)
              ·
                refine ⟨499903465279629092767157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1333075907412344247379085 499903465279629092767157)
                ·
                  refine ⟨46865949869965227446921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 499903465279629092767157 46865949869965227446921)
                  ·
                    rfl

theorem cell21_205360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_205360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205360 prefixEnd_205360 := by exact prefixLift 205360
  have htrace : WordTrace (prefixWord ++ tailWord_205360) baseStart_205360 baseEnd_205360 := by
    simpa [prefixWord, tailWord_205360, baseEnd_205360] using wordTrace_append hprefix tailTrace_205360
  have hstable : (prefixWord ++ tailWord_205360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205360).length < 2 ^ (prefixWord ++ tailWord_205360).sum := by decide
  have hdescent : baseEnd_205360 < baseStart_205360 := by decide
  rcases family_descends (prefixWord ++ tailWord_205360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205366 : List Nat := [5, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_205366 : Nat := 118140960795 + 205366 * 2 ^ 59
def prefixEnd_205366 : Nat := 4983230072969 + 3 ^ 40 * 205366 * 2
def baseEnd_205366 : Nat := 46867319151710550346909

theorem tailTrace_205366 : CollatzResearch.WordTrace tailWord_205366 prefixEnd_205366 46867319151710550346909 := by
  unfold tailWord_205366
  simp only [CollatzResearch.WordTrace]
  refine ⟨468144585875095660346747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4993542249334353710365301 468144585875095660346747)
  ·
    refine ⟨702216878812643490520121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 468144585875095660346747 702216878812643490520121)
    ·
      refine ⟨526662659109482617890091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 702216878812643490520121 526662659109482617890091)
      ·
        refine ⟨789993988664223926835137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526662659109482617890091 789993988664223926835137)
        ·
          refine ⟨592495491498167945126353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 789993988664223926835137 592495491498167945126353)
          ·
            refine ⟨444371618623625958844765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 592495491498167945126353 444371618623625958844765)
            ·
              refine ⟨166639356983859734566787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 444371618623625958844765 166639356983859734566787)
              ·
                refine ⟨249959035475789601850181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166639356983859734566787 249959035475789601850181)
                ·
                  refine ⟨46867319151710550346909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 249959035475789601850181 46867319151710550346909)
                  ·
                    rfl

theorem cell21_205366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_205366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205366 prefixEnd_205366 := by exact prefixLift 205366
  have htrace : WordTrace (prefixWord ++ tailWord_205366) baseStart_205366 baseEnd_205366 := by
    simpa [prefixWord, tailWord_205366, baseEnd_205366] using wordTrace_append hprefix tailTrace_205366
  have hstable : (prefixWord ++ tailWord_205366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205366).length < 2 ^ (prefixWord ++ tailWord_205366).sum := by decide
  have hdescent : baseEnd_205366 < baseStart_205366 := by decide
  rcases family_descends (prefixWord ++ tailWord_205366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205377 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 5]
def baseStart_205377 : Nat := 118140960795 + 205377 * 2 ^ 59
def prefixEnd_205377 : Nat := 4983230072969 + 3 ^ 40 * 205377 * 2
def baseEnd_205377 : Nat := 46869829501576975663553

theorem tailTrace_205377 : CollatzResearch.WordTrace tailWord_205377 prefixEnd_205377 46869829501576975663553 := by
  unfold tailWord_205377
  simp only [CollatzResearch.WordTrace]
  refine ⟨7490714576961679444198385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4993809717974452962798923 7490714576961679444198385)
  ·
    refine ⟨5618035932721259583148789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7490714576961679444198385 5618035932721259583148789)
    ·
      refine ⟨526690868692618085920199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5618035932721259583148789 526690868692618085920199)
      ·
        refine ⟨790036303038927128880299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526690868692618085920199 790036303038927128880299)
        ·
          refine ⟨1185054454558390693320449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 790036303038927128880299 1185054454558390693320449)
          ·
            refine ⟨888790840918793019990337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1185054454558390693320449 888790840918793019990337)
            ·
              refine ⟨666593130689094764992753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888790840918793019990337 666593130689094764992753)
              ·
                refine ⟨499944848016821073744565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666593130689094764992753 499944848016821073744565)
                ·
                  refine ⟨46869829501576975663553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 499944848016821073744565 46869829501576975663553)
                  ·
                    rfl

theorem cell21_205377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_205377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205377 prefixEnd_205377 := by exact prefixLift 205377
  have htrace : WordTrace (prefixWord ++ tailWord_205377) baseStart_205377 baseEnd_205377 := by
    simpa [prefixWord, tailWord_205377, baseEnd_205377] using wordTrace_append hprefix tailTrace_205377
  have hstable : (prefixWord ++ tailWord_205377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205377).length < 2 ^ (prefixWord ++ tailWord_205377).sum := by decide
  have hdescent : baseEnd_205377 < baseStart_205377 := by decide
  rcases family_descends (prefixWord ++ tailWord_205377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205422 : List Nat := [4, 1, 2, 2, 2, 1, 1, 8]
def baseStart_205422 : Nat := 118140960795 + 205422 * 2 ^ 59
def prefixEnd_205422 : Nat := 4983230072969 + 3 ^ 40 * 205422 * 2
def baseEnd_205422 : Nat := 15626699704888965804487

theorem tailTrace_205422 : CollatzResearch.WordTrace tailWord_205422 prefixEnd_205422 15626699704888965804487 := by
  unfold tailWord_205422
  simp only [CollatzResearch.WordTrace]
  refine ⟨936544482724831516198315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4994903907865768086391013 936544482724831516198315)
  ·
    refine ⟨1404816724087247274297473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 936544482724831516198315 1404816724087247274297473)
    ·
      refine ⟨1053612543065435455723105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1404816724087247274297473 1053612543065435455723105)
      ·
        refine ⟨790209407299076591792329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1053612543065435455723105 790209407299076591792329)
        ·
          refine ⟨592657055474307443844247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 790209407299076591792329 592657055474307443844247)
          ·
            refine ⟨888985583211461165766371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592657055474307443844247 888985583211461165766371)
            ·
              refine ⟨1333478374817191748649557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888985583211461165766371 1333478374817191748649557)
              ·
                refine ⟨15626699704888965804487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1333478374817191748649557 15626699704888965804487)
                ·
                  rfl

theorem cell21_205422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_205422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205422 prefixEnd_205422 := by exact prefixLift 205422
  have htrace : WordTrace (prefixWord ++ tailWord_205422) baseStart_205422 baseEnd_205422 := by
    simpa [prefixWord, tailWord_205422, baseEnd_205422] using wordTrace_append hprefix tailTrace_205422
  have hstable : (prefixWord ++ tailWord_205422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205422).length < 2 ^ (prefixWord ++ tailWord_205422).sum := by decide
  have hdescent : baseEnd_205422 < baseStart_205422 := by decide
  rcases family_descends (prefixWord ++ tailWord_205422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205436 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 5]
def baseStart_205436 : Nat := 118140960795 + 205436 * 2 ^ 59
def prefixEnd_205436 : Nat := 4983230072969 + 3 ^ 40 * 205436 * 2
def baseEnd_205436 : Nat := 46883294105405984180099

theorem tailTrace_205436 : CollatzResearch.WordTrace tailWord_205436 prefixEnd_205436 46883294105405984180099 := by
  unfold tailWord_205436
  simp only [CollatzResearch.WordTrace]
  refine ⟨3746433241873966260298081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4995244322498621680397441 3746433241873966260298081)
  ·
    refine ⟨2809824931405474695223561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3746433241873966260298081 2809824931405474695223561)
    ·
      refine ⟨2107368698554106021417671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2809824931405474695223561 2107368698554106021417671)
      ·
        refine ⟨3161053047831159032126507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2107368698554106021417671 3161053047831159032126507)
        ·
          refine ⟨4741579571746738548189761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3161053047831159032126507 4741579571746738548189761)
          ·
            refine ⟨3556184678810053911142321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4741579571746738548189761 3556184678810053911142321)
            ·
              refine ⟨2667138509107540433356741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3556184678810053911142321 2667138509107540433356741)
              ·
                refine ⟨500088470457663831254389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2667138509107540433356741 500088470457663831254389)
                ·
                  refine ⟨46883294105405984180099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 500088470457663831254389 46883294105405984180099)
                  ·
                    rfl

theorem cell21_205436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_205436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205436 prefixEnd_205436 := by exact prefixLift 205436
  have htrace : WordTrace (prefixWord ++ tailWord_205436) baseStart_205436 baseEnd_205436 := by
    simpa [prefixWord, tailWord_205436, baseEnd_205436] using wordTrace_append hprefix tailTrace_205436
  have hstable : (prefixWord ++ tailWord_205436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205436).length < 2 ^ (prefixWord ++ tailWord_205436).sum := by decide
  have hdescent : baseEnd_205436 < baseStart_205436 := by decide
  rcases family_descends (prefixWord ++ tailWord_205436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205498 : List Nat := [3, 1, 1, 1, 2, 3, 5, 5]
def baseStart_205498 : Nat := 118140960795 + 205498 * 2 ^ 59
def prefixEnd_205498 : Nat := 4983230072969 + 3 ^ 40 * 205498 * 2
def baseEnd_205498 : Nat := 15632481116702551382213

theorem tailTrace_205498 : CollatzResearch.WordTrace tailWord_205498 prefixEnd_205498 15632481116702551382213 := by
  unfold tailWord_205498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1873781952380829277338287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4996751873015544739568765 1873781952380829277338287)
  ·
    refine ⟨2810672928571243916007431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1873781952380829277338287 2810672928571243916007431)
    ·
      refine ⟨4216009392856865874011147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2810672928571243916007431 4216009392856865874011147)
      ·
        refine ⟨6324014089285298811016721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4216009392856865874011147 6324014089285298811016721)
        ·
          refine ⟨4743010566963974108262541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6324014089285298811016721 4743010566963974108262541)
          ·
            refine ⟨1778628962611490290598453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4743010566963974108262541 1778628962611490290598453)
            ·
              refine ⟨166746465244827214743605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1778628962611490290598453 166746465244827214743605)
              ·
                refine ⟨15632481116702551382213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166746465244827214743605 15632481116702551382213)
                ·
                  rfl

theorem cell21_205498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_205498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205498 prefixEnd_205498 := by exact prefixLift 205498
  have htrace : WordTrace (prefixWord ++ tailWord_205498) baseStart_205498 baseEnd_205498 := by
    simpa [prefixWord, tailWord_205498, baseEnd_205498] using wordTrace_append hprefix tailTrace_205498
  have hstable : (prefixWord ++ tailWord_205498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205498).length < 2 ^ (prefixWord ++ tailWord_205498).sum := by decide
  have hdescent : baseEnd_205498 < baseStart_205498 := by decide
  rcases family_descends (prefixWord ++ tailWord_205498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205529 : List Nat := [1, 2, 1, 2, 3, 2, 1, 6, 3]
def baseStart_205529 : Nat := 118140960795 + 205529 * 2 ^ 59
def prefixEnd_205529 : Nat := 4983230072969 + 3 ^ 40 * 205529 * 2
def baseEnd_205529 : Nat := 46904517972458489129909

theorem tailTrace_205529 : CollatzResearch.WordTrace tailWord_205529 prefixEnd_205529 46904517972458489129909 := by
  unfold tailWord_205529
  simp only [CollatzResearch.WordTrace]
  refine ⟨7496258472411009403731641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4997505648274006269154427 7496258472411009403731641)
  ·
    refine ⟨5622193854308257052798731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7496258472411009403731641 5622193854308257052798731)
    ·
      refine ⟨8433290781462385579198097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5622193854308257052798731 8433290781462385579198097)
      ·
        refine ⟨6324968086096789184398573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8433290781462385579198097 6324968086096789184398573)
        ·
          refine ⟨2371863032286295944149465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6324968086096789184398573 2371863032286295944149465)
          ·
            refine ⟨1778897274214721958112099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2371863032286295944149465 1778897274214721958112099)
            ·
              refine ⟨2668345911322082937168149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1778897274214721958112099 2668345911322082937168149)
              ·
                refine ⟨125078714593222637679757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2668345911322082937168149 125078714593222637679757)
                ·
                  refine ⟨46904517972458489129909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125078714593222637679757 46904517972458489129909)
                  ·
                    rfl

theorem cell21_205529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 3].length) (baseStart_205529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205529 prefixEnd_205529 := by exact prefixLift 205529
  have htrace : WordTrace (prefixWord ++ tailWord_205529) baseStart_205529 baseEnd_205529 := by
    simpa [prefixWord, tailWord_205529, baseEnd_205529] using wordTrace_append hprefix tailTrace_205529
  have hstable : (prefixWord ++ tailWord_205529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205529).length < 2 ^ (prefixWord ++ tailWord_205529).sum := by decide
  have hdescent : baseEnd_205529 < baseStart_205529 := by decide
  rcases family_descends (prefixWord ++ tailWord_205529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205647 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 11]
def baseStart_205647 : Nat := 118140960795 + 205647 * 2 ^ 59
def prefixEnd_205647 : Nat := 4983230072969 + 3 ^ 40 * 205647 * 2
def baseEnd_205647 : Nat := 46931447180116506163001

theorem tailTrace_205647 : CollatzResearch.WordTrace tailWord_205647 prefixEnd_205647 46931447180116506163001 := by
  unfold tailWord_205647
  simp only [CollatzResearch.WordTrace]
  refine ⟨7500562285983515556527195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5000374857322343704351463 7500562285983515556527195)
  ·
    refine ⟨11250843428975273334790793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7500562285983515556527195 11250843428975273334790793)
    ·
      refine ⟨8438132571731455001093095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11250843428975273334790793 8438132571731455001093095)
      ·
        refine ⟨12657198857597182501639643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8438132571731455001093095 12657198857597182501639643)
        ·
          refine ⟨18985798286395773752459465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12657198857597182501639643 18985798286395773752459465)
          ·
            refine ⟨14239348714796830314344599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18985798286395773752459465 14239348714796830314344599)
            ·
              refine ⟨21359023072195245471516899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14239348714796830314344599 21359023072195245471516899)
              ·
                refine ⟨32038534608292868207275349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21359023072195245471516899 32038534608292868207275349)
                ·
                  refine ⟨46931447180116506163001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 32038534608292868207275349 46931447180116506163001)
                  ·
                    rfl

theorem cell21_205647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 11].length) (baseStart_205647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205647 prefixEnd_205647 := by exact prefixLift 205647
  have htrace : WordTrace (prefixWord ++ tailWord_205647) baseStart_205647 baseEnd_205647 := by
    simpa [prefixWord, tailWord_205647, baseEnd_205647] using wordTrace_append hprefix tailTrace_205647
  have hstable : (prefixWord ++ tailWord_205647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205647).length < 2 ^ (prefixWord ++ tailWord_205647).sum := by decide
  have hdescent : baseEnd_205647 < baseStart_205647 := by decide
  rcases family_descends (prefixWord ++ tailWord_205647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205664 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 5]
def baseStart_205664 : Nat := 118140960795 + 205664 * 2 ^ 59
def prefixEnd_205664 : Nat := 4983230072969 + 3 ^ 40 * 205664 * 2
def baseEnd_205664 : Nat := 46935326811728254379633

theorem tailTrace_205664 : CollatzResearch.WordTrace tailWord_205664 prefixEnd_205664 46935326811728254379633 := by
  unfold tailWord_205664
  simp only [CollatzResearch.WordTrace]
  refine ⟨3750591163460963729948023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5000788217947951639930697 3750591163460963729948023)
  ·
    refine ⟨5625886745191445594922035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3750591163460963729948023 5625886745191445594922035)
    ·
      refine ⟨8438830117787168392383053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5625886745191445594922035 8438830117787168392383053)
      ·
        refine ⟨3164561294170188147143645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8438830117787168392383053 3164561294170188147143645)
        ·
          refine ⟨1186710485313820555178867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3164561294170188147143645 1186710485313820555178867)
          ·
            refine ⟨1780065727970730832768301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186710485313820555178867 1780065727970730832768301)
            ·
              refine ⟨667524647989024062288113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1780065727970730832768301 667524647989024062288113)
              ·
                refine ⟨500643485991768046716085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 667524647989024062288113 500643485991768046716085)
                ·
                  refine ⟨46935326811728254379633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 500643485991768046716085 46935326811728254379633)
                  ·
                    rfl

theorem cell21_205664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_205664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205664 prefixEnd_205664 := by exact prefixLift 205664
  have htrace : WordTrace (prefixWord ++ tailWord_205664) baseStart_205664 baseEnd_205664 := by
    simpa [prefixWord, tailWord_205664, baseEnd_205664] using wordTrace_append hprefix tailTrace_205664
  have hstable : (prefixWord ++ tailWord_205664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205664).length < 2 ^ (prefixWord ++ tailWord_205664).sum := by decide
  have hdescent : baseEnd_205664 < baseStart_205664 := by decide
  rcases family_descends (prefixWord ++ tailWord_205664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205681 : List Nat := [1, 2, 2, 2, 1, 4, 1, 5, 3]
def baseStart_205681 : Nat := 118140960795 + 205681 * 2 ^ 59
def prefixEnd_205681 : Nat := 4983230072969 + 3 ^ 40 * 205681 * 2
def baseEnd_205681 : Nat := 46939206443340002596265

theorem tailTrace_205681 : CollatzResearch.WordTrace tailWord_205681 prefixEnd_205681 46939206443340002596265 := by
  unfold tailWord_205681
  simp only [CollatzResearch.WordTrace]
  refine ⟨7501802367860339363264897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5001201578573559575509931 7501802367860339363264897)
  ·
    refine ⟨5626351775895254522448673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7501802367860339363264897 5626351775895254522448673)
    ·
      refine ⟨4219763831921440891836505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5626351775895254522448673 4219763831921440891836505)
      ·
        refine ⟨3164822873941080668877379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4219763831921440891836505 3164822873941080668877379)
        ·
          refine ⟨4747234310911621003316069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3164822873941080668877379 4747234310911621003316069)
          ·
            refine ⟨890106433295928938121763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4747234310911621003316069 890106433295928938121763)
            ·
              refine ⟨1335159649943893407182645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890106433295928938121763 1335159649943893407182645)
              ·
                refine ⟨125171217182240006923373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1335159649943893407182645 125171217182240006923373)
                ·
                  refine ⟨46939206443340002596265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125171217182240006923373 46939206443340002596265)
                  ·
                    rfl

theorem cell21_205681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 3].length) (baseStart_205681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205681 prefixEnd_205681 := by exact prefixLift 205681
  have htrace : WordTrace (prefixWord ++ tailWord_205681) baseStart_205681 baseEnd_205681 := by
    simpa [prefixWord, tailWord_205681, baseEnd_205681] using wordTrace_append hprefix tailTrace_205681
  have hstable : (prefixWord ++ tailWord_205681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205681).length < 2 ^ (prefixWord ++ tailWord_205681).sum := by decide
  have hdescent : baseEnd_205681 < baseStart_205681 := by decide
  rcases family_descends (prefixWord ++ tailWord_205681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205695 : List Nat := [1, 1, 2, 2, 1, 1, 7, 2, 4]
def baseStart_205695 : Nat := 118140960795 + 205695 * 2 ^ 59
def prefixEnd_205695 : Nat := 4983230072969 + 3 ^ 40 * 205695 * 2
def baseEnd_205695 : Nat := 46942401434079089362903

theorem tailTrace_205695 : CollatzResearch.WordTrace tailWord_205695 prefixEnd_205695 46942401434079089362903 := by
  unfold tailWord_205695
  simp only [CollatzResearch.WordTrace]
  refine ⟨7502312989809619754274539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5001541993206413169516359 7502312989809619754274539)
  ·
    refine ⟨11253469484714429631411809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7502312989809619754274539 11253469484714429631411809)
    ·
      refine ⟨8440102113535822223558857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11253469484714429631411809 8440102113535822223558857)
      ·
        refine ⟨6330076585151866667669143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8440102113535822223558857 6330076585151866667669143)
        ·
          refine ⟨9495114877727800001503715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6330076585151866667669143 9495114877727800001503715)
          ·
            refine ⟨14242672316591700002255573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9495114877727800001503715 14242672316591700002255573)
            ·
              refine ⟨333812632420117968802865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14242672316591700002255573 333812632420117968802865)
              ·
                refine ⟨250359474315088476602149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333812632420117968802865 250359474315088476602149)
                ·
                  refine ⟨46942401434079089362903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 250359474315088476602149 46942401434079089362903)
                  ·
                    rfl

theorem cell21_205695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 4].length) (baseStart_205695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205695 prefixEnd_205695 := by exact prefixLift 205695
  have htrace : WordTrace (prefixWord ++ tailWord_205695) baseStart_205695 baseEnd_205695 := by
    simpa [prefixWord, tailWord_205695, baseEnd_205695] using wordTrace_append hprefix tailTrace_205695
  have hstable : (prefixWord ++ tailWord_205695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205695).length < 2 ^ (prefixWord ++ tailWord_205695).sum := by decide
  have hdescent : baseEnd_205695 < baseStart_205695 := by decide
  rcases family_descends (prefixWord ++ tailWord_205695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205754 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 6]
def baseStart_205754 : Nat := 118140960795 + 205754 * 2 ^ 59
def prefixEnd_205754 : Nat := 4983230072969 + 3 ^ 40 * 205754 * 2
def baseEnd_205754 : Nat := 46955866037908097879449

theorem tailTrace_205754 : CollatzResearch.WordTrace tailWord_205754 prefixEnd_205754 46955866037908097879449 := by
  unfold tailWord_205754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1876116224148968207668079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5002976597730581887114877 1876116224148968207668079)
  ·
    refine ⟨2814174336223452311502119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1876116224148968207668079 2814174336223452311502119)
    ·
      refine ⟨4221261504335178467253179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2814174336223452311502119 4221261504335178467253179)
      ·
        refine ⟨6331892256502767700879769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4221261504335178467253179 6331892256502767700879769)
        ·
          refine ⟨4748919192377075775659827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6331892256502767700879769 4748919192377075775659827)
          ·
            refine ⟨7123378788565613663489741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4748919192377075775659827 7123378788565613663489741)
            ·
              refine ⟨2671267045712105123808653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7123378788565613663489741 2671267045712105123808653)
              ·
                refine ⟨1001725142142039421428245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2671267045712105123808653 1001725142142039421428245)
                ·
                  refine ⟨46955866037908097879449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1001725142142039421428245 46955866037908097879449)
                  ·
                    rfl

theorem cell21_205754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_205754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205754 prefixEnd_205754 := by exact prefixLift 205754
  have htrace : WordTrace (prefixWord ++ tailWord_205754) baseStart_205754 baseEnd_205754 := by
    simpa [prefixWord, tailWord_205754, baseEnd_205754] using wordTrace_append hprefix tailTrace_205754
  have hstable : (prefixWord ++ tailWord_205754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205754).length < 2 ^ (prefixWord ++ tailWord_205754).sum := by decide
  have hdescent : baseEnd_205754 < baseStart_205754 := by decide
  rcases family_descends (prefixWord ++ tailWord_205754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205771 : List Nat := [1, 1, 1, 1, 3, 6, 1, 3, 4]
def baseStart_205771 : Nat := 118140960795 + 205771 * 2 ^ 59
def prefixEnd_205771 : Nat := 4983230072969 + 3 ^ 40 * 205771 * 2
def baseEnd_205771 : Nat := 46959745669519846096081

theorem tailTrace_205771 : CollatzResearch.WordTrace tailWord_205771 prefixEnd_205771 46959745669519846096081 := by
  unfold tailWord_205771
  simp only [CollatzResearch.WordTrace]
  refine ⟨7505084937534284734041167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5003389958356189822694111 7505084937534284734041167)
  ·
    refine ⟨11257627406301427101061751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7505084937534284734041167 11257627406301427101061751)
    ·
      refine ⟨16886441109452140651592627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11257627406301427101061751 16886441109452140651592627)
      ·
        refine ⟨25329661664178210977388941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16886441109452140651592627 25329661664178210977388941)
        ·
          refine ⟨9498623124066829116520853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25329661664178210977388941 9498623124066829116520853)
          ·
            refine ⟨445247958940632614836915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9498623124066829116520853 445247958940632614836915)
            ·
              refine ⟨667871938410948922255373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445247958940632614836915 667871938410948922255373)
              ·
                refine ⟨250451976904105845845765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 667871938410948922255373 250451976904105845845765)
                ·
                  refine ⟨46959745669519846096081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 250451976904105845845765 46959745669519846096081)
                  ·
                    rfl

theorem cell21_205771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 4].length) (baseStart_205771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205771 prefixEnd_205771 := by exact prefixLift 205771
  have htrace : WordTrace (prefixWord ++ tailWord_205771) baseStart_205771 baseEnd_205771 := by
    simpa [prefixWord, tailWord_205771, baseEnd_205771] using wordTrace_append hprefix tailTrace_205771
  have hstable : (prefixWord ++ tailWord_205771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205771).length < 2 ^ (prefixWord ++ tailWord_205771).sum := by decide
  have hdescent : baseEnd_205771 < baseStart_205771 := by decide
  rcases family_descends (prefixWord ++ tailWord_205771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205785 : List Nat := [1, 2, 1, 2, 5, 1, 2, 7]
def baseStart_205785 : Nat := 118140960795 + 205785 * 2 ^ 59
def prefixEnd_205785 : Nat := 4983230072969 + 3 ^ 40 * 205785 * 2
def baseEnd_205785 : Nat := 15654313553419644287573

theorem tailTrace_205785 : CollatzResearch.WordTrace tailWord_205785 prefixEnd_205785 15654313553419644287573 := by
  unfold tailWord_205785
  simp only [CollatzResearch.WordTrace]
  refine ⟨7505595559483565125050809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5003730372989043416700539 7505595559483565125050809)
  ·
    refine ⟨5629196669612673843788107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7505595559483565125050809 5629196669612673843788107)
    ·
      refine ⟨8443795004419010765682161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5629196669612673843788107 8443795004419010765682161)
      ·
        refine ⟨6332846253314258074261621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8443795004419010765682161 6332846253314258074261621)
        ·
          refine ⟨593704336248211694462027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6332846253314258074261621 593704336248211694462027)
          ·
            refine ⟨890556504372317541693041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593704336248211694462027 890556504372317541693041)
            ·
              refine ⟨667917378279238156269781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 890556504372317541693041 667917378279238156269781)
              ·
                refine ⟨15654313553419644287573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 667917378279238156269781 15654313553419644287573)
                ·
                  rfl

theorem cell21_205785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 7].length) (baseStart_205785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205785 prefixEnd_205785 := by exact prefixLift 205785
  have htrace : WordTrace (prefixWord ++ tailWord_205785) baseStart_205785 baseEnd_205785 := by
    simpa [prefixWord, tailWord_205785, baseEnd_205785] using wordTrace_append hprefix tailTrace_205785
  have hstable : (prefixWord ++ tailWord_205785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205785).length < 2 ^ (prefixWord ++ tailWord_205785).sum := by decide
  have hdescent : baseEnd_205785 < baseStart_205785 := by decide
  rcases family_descends (prefixWord ++ tailWord_205785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205985 : List Nat := [1, 2, 3, 3, 1, 1, 3, 4, 3]
def baseStart_205985 : Nat := 118140960795 + 205985 * 2 ^ 59
def prefixEnd_205985 : Nat := 4983230072969 + 3 ^ 40 * 205985 * 2
def baseEnd_205985 : Nat := 47008583385103029528977

theorem tailTrace_205985 : CollatzResearch.WordTrace tailWord_205985 prefixEnd_205985 47008583385103029528977 := by
  unfold tailWord_205985
  simp only [CollatzResearch.WordTrace]
  refine ⟨7512890158758999282331409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5008593439172666188220939 7512890158758999282331409)
  ·
    refine ⟨5634667619069249461748557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7512890158758999282331409 5634667619069249461748557)
    ·
      refine ⟨2113000357150968548155709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5634667619069249461748557 2113000357150968548155709)
      ·
        refine ⟨792375133931613205558391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2113000357150968548155709 792375133931613205558391)
        ·
          refine ⟨1188562700897419808337587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792375133931613205558391 1188562700897419808337587)
          ·
            refine ⟨1782844051346129712506381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1188562700897419808337587 1782844051346129712506381)
            ·
              refine ⟨668566519254798642189893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1782844051346129712506381 668566519254798642189893)
              ·
                refine ⟨125356222360274745410605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 668566519254798642189893 125356222360274745410605)
                ·
                  refine ⟨47008583385103029528977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125356222360274745410605 47008583385103029528977)
                  ·
                    rfl

theorem cell21_205985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 3].length) (baseStart_205985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205985 prefixEnd_205985 := by exact prefixLift 205985
  have htrace : WordTrace (prefixWord ++ tailWord_205985) baseStart_205985 baseEnd_205985 := by
    simpa [prefixWord, tailWord_205985, baseEnd_205985] using wordTrace_append hprefix tailTrace_205985
  have hstable : (prefixWord ++ tailWord_205985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205985).length < 2 ^ (prefixWord ++ tailWord_205985).sum := by decide
  have hdescent : baseEnd_205985 < baseStart_205985 := by decide
  rcases family_descends (prefixWord ++ tailWord_205985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_205996 : List Nat := [2, 2, 1, 1, 1, 1, 1, 12]
def baseStart_205996 : Nat := 118140960795 + 205996 * 2 ^ 59
def prefixEnd_205996 : Nat := 4983230072969 + 3 ^ 40 * 205996 * 2
def baseEnd_205996 : Nat := 15670364578323151615207

theorem tailTrace_205996 : CollatzResearch.WordTrace tailWord_205996 prefixEnd_205996 15670364578323151615207 := by
  unfold tailWord_205996
  simp only [CollatzResearch.WordTrace]
  refine ⟨3756645680859574080490921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5008860907812765440654561 3756645680859574080490921)
  ·
    refine ⟨2817484260644680560368191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3756645680859574080490921 2817484260644680560368191)
    ·
      refine ⟨4226226390967020840552287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2817484260644680560368191 4226226390967020840552287)
      ·
        refine ⟨6339339586450531260828431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4226226390967020840552287 6339339586450531260828431)
        ·
          refine ⟨9509009379675796891242647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6339339586450531260828431 9509009379675796891242647)
          ·
            refine ⟨14263514069513695336863971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9509009379675796891242647 14263514069513695336863971)
            ·
              refine ⟨21395271104270543005295957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14263514069513695336863971 21395271104270543005295957)
              ·
                refine ⟨15670364578323151615207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 21395271104270543005295957 15670364578323151615207)
                ·
                  rfl

theorem cell21_205996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 12].length) (baseStart_205996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_205996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_205996 prefixEnd_205996 := by exact prefixLift 205996
  have htrace : WordTrace (prefixWord ++ tailWord_205996) baseStart_205996 baseEnd_205996 := by
    simpa [prefixWord, tailWord_205996, baseEnd_205996] using wordTrace_append hprefix tailTrace_205996
  have hstable : (prefixWord ++ tailWord_205996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_205996).length < 2 ^ (prefixWord ++ tailWord_205996).sum := by decide
  have hdescent : baseEnd_205996 < baseStart_205996 := by decide
  rcases family_descends (prefixWord ++ tailWord_205996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206078 : List Nat := [4, 2, 2, 1, 1, 2, 3, 3, 3]
def baseStart_206078 : Nat := 118140960795 + 206078 * 2 ^ 59
def prefixEnd_206078 : Nat := 4983230072969 + 3 ^ 40 * 206078 * 2
def baseEnd_206078 : Nat := 47029807252155534478787

theorem tailTrace_206078 : CollatzResearch.WordTrace tailWord_206078 prefixEnd_206078 47029807252155534478787 := by
  unfold tailWord_206078
  simp only [CollatzResearch.WordTrace]
  refine ⟨939535268427759520683361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5010854764948050776977925 939535268427759520683361)
  ·
    refine ⟨704651451320819640512521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 939535268427759520683361 704651451320819640512521)
    ·
      refine ⟨528488588490614730384391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 704651451320819640512521 528488588490614730384391)
      ·
        refine ⟨792732882735922095576587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528488588490614730384391 792732882735922095576587)
        ·
          refine ⟨1189099324103883143364881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792732882735922095576587 1189099324103883143364881)
          ·
            refine ⟨891824493077912357523661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1189099324103883143364881 891824493077912357523661)
            ·
              refine ⟨334434184904217134071373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 891824493077912357523661 334434184904217134071373)
              ·
                refine ⟨125412819339081425276765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334434184904217134071373 125412819339081425276765)
                ·
                  refine ⟨47029807252155534478787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125412819339081425276765 47029807252155534478787)
                  ·
                    rfl

theorem cell21_206078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_206078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206078 prefixEnd_206078 := by exact prefixLift 206078
  have htrace : WordTrace (prefixWord ++ tailWord_206078) baseStart_206078 baseEnd_206078 := by
    simpa [prefixWord, tailWord_206078, baseEnd_206078] using wordTrace_append hprefix tailTrace_206078
  have hstable : (prefixWord ++ tailWord_206078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206078).length < 2 ^ (prefixWord ++ tailWord_206078).sum := by decide
  have hdescent : baseEnd_206078 < baseStart_206078 := by decide
  rcases family_descends (prefixWord ++ tailWord_206078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
