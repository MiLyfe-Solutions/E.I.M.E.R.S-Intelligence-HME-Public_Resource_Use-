import V185TrunkScan22Chunk313

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2800500 : List Nat := [2, 20]
def baseStart_2800500 : Nat := 118140960795 + 2800500 * 2 ^ 59
def prefixEnd_2800500 : Nat := 4983230072969 + 3 ^ 40 * 2800500 * 2
def baseEnd_2800500 : Nat := 146116199046527283907

theorem tailTrace_2800500 : CollatzResearch.WordTrace tailWord_2800500 prefixEnd_2800500 146116199046527283907 := by
  unfold tailWord_2800500
  simp only [CollatzResearch.WordTrace]
  refine ⟨51071313177137131083355477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68095084236182841444473969 51071313177137131083355477)
  ·
    refine ⟨146116199046527283907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 20 51071313177137131083355477 146116199046527283907)
    ·
      rfl

theorem cell22_2800500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 20].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 20].length) (baseStart_2800500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800500 prefixEnd_2800500 := by exact prefixLift 2800500
  have htrace : WordTrace (prefixWord ++ tailWord_2800500) baseStart_2800500 baseEnd_2800500 := by
    simpa [prefixWord, tailWord_2800500, baseEnd_2800500] using wordTrace_append hprefix tailTrace_2800500
  have hstable : (prefixWord ++ tailWord_2800500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800500).length < 2 ^ (prefixWord ++ tailWord_2800500).sum := by decide
  have hdescent : baseEnd_2800500 < baseStart_2800500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800517 : List Nat := [1, 3, 1, 1, 3, 3, 3, 7]
def baseStart_2800517 : Nat := 118140960795 + 2800517 * 2 ^ 59
def prefixEnd_2800517 : Nat := 4983230072969 + 3 ^ 40 * 2800517 * 2
def baseEnd_2800517 : Nat := 106519355710187014670975

theorem tailTrace_2800517 : CollatzResearch.WordTrace tailWord_2800517 prefixEnd_2800517 106519355710187014670975 := by
  unfold tailWord_2800517
  simp only [CollatzResearch.WordTrace]
  refine ⟨102143246395212674070079805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68095497596808449380053203 102143246395212674070079805)
  ·
    refine ⟨38303717398204752776279927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102143246395212674070079805 38303717398204752776279927)
    ·
      refine ⟨57455576097307129164419891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38303717398204752776279927 57455576097307129164419891)
      ·
        refine ⟨86183364145960693746629837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57455576097307129164419891 86183364145960693746629837)
        ·
          refine ⟨32318761554735260154986189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86183364145960693746629837 32318761554735260154986189)
          ·
            refine ⟨12119535583025722558119821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32318761554735260154986189 12119535583025722558119821)
            ·
              refine ⟨4544825843634645959294933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12119535583025722558119821 4544825843634645959294933)
              ·
                refine ⟨106519355710187014670975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4544825843634645959294933 106519355710187014670975)
                ·
                  rfl

theorem cell22_2800517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 7].length) (baseStart_2800517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800517 prefixEnd_2800517 := by exact prefixLift 2800517
  have htrace : WordTrace (prefixWord ++ tailWord_2800517) baseStart_2800517 baseEnd_2800517 := by
    simpa [prefixWord, tailWord_2800517, baseEnd_2800517] using wordTrace_append hprefix tailTrace_2800517
  have hstable : (prefixWord ++ tailWord_2800517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800517).length < 2 ^ (prefixWord ++ tailWord_2800517).sum := by decide
  have hdescent : baseEnd_2800517 < baseStart_2800517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800667 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 4, 7]
def baseStart_2800667 : Nat := 118140960795 + 2800667 * 2 ^ 59
def prefixEnd_2800667 : Nat := 4983230072969 + 3 ^ 40 * 2800667 * 2
def baseEnd_2800667 : Nat := 958725549457132740788315

theorem tailTrace_2800667 : CollatzResearch.WordTrace tailWord_2800667 prefixEnd_2800667 958725549457132740788315 := by
  unfold tailWord_2800667
  simp only [CollatzResearch.WordTrace]
  refine ⟨102148717344669249688040255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68099144896446166458693503 102148717344669249688040255)
  ·
    refine ⟨153223076017003874532060383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102148717344669249688040255 153223076017003874532060383)
    ·
      refine ⟨229834614025505811798090575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153223076017003874532060383 229834614025505811798090575)
      ·
        refine ⟨344751921038258717697135863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229834614025505811798090575 344751921038258717697135863)
        ·
          refine ⟨517127881557388076545703795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344751921038258717697135863 517127881557388076545703795)
          ·
            refine ⟨775691822336082114818555693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517127881557388076545703795 775691822336082114818555693)
            ·
              refine ⟨290884433376030793056958385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 775691822336082114818555693 290884433376030793056958385)
              ·
                refine ⟨218163325032023094792718789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290884433376030793056958385 218163325032023094792718789)
                ·
                  refine ⟨40905623443504330273634773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 218163325032023094792718789 40905623443504330273634773)
                  ·
                    refine ⟨958725549457132740788315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40905623443504330273634773 958725549457132740788315)
                    ·
                      rfl

theorem cell22_2800667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 7].length) (baseStart_2800667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800667 prefixEnd_2800667 := by exact prefixLift 2800667
  have htrace : WordTrace (prefixWord ++ tailWord_2800667) baseStart_2800667 baseEnd_2800667 := by
    simpa [prefixWord, tailWord_2800667, baseEnd_2800667] using wordTrace_append hprefix tailTrace_2800667
  have hstable : (prefixWord ++ tailWord_2800667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800667).length < 2 ^ (prefixWord ++ tailWord_2800667).sum := by decide
  have hdescent : baseEnd_2800667 < baseStart_2800667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800669 : List Nat := [1, 4, 2, 2, 3, 10]
def baseStart_2800669 : Nat := 118140960795 + 2800669 * 2 ^ 59
def prefixEnd_2800669 : Nat := 4983230072969 + 3 ^ 40 * 2800669 * 2
def baseEnd_2800669 : Nat := 11836126346888955583189

theorem tailTrace_2800669 : CollatzResearch.WordTrace tailWord_2800669 prefixEnd_2800669 11836126346888955583189 := by
  unfold tailWord_2800669
  simp only [CollatzResearch.WordTrace]
  refine ⟨102148790290662004029613061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68099193527108002686408707 102148790290662004029613061)
  ·
    refine ⟨19152898179499125755552449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102148790290662004029613061 19152898179499125755552449)
    ·
      refine ⟨14364673634624344316664337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19152898179499125755552449 14364673634624344316664337)
      ·
        refine ⟨10773505225968258237498253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14364673634624344316664337 10773505225968258237498253)
        ·
          refine ⟨4040064459738096839061845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10773505225968258237498253 4040064459738096839061845)
          ·
            refine ⟨11836126346888955583189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4040064459738096839061845 11836126346888955583189)
            ·
              rfl

theorem cell22_2800669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 10].length) (baseStart_2800669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800669 prefixEnd_2800669 := by exact prefixLift 2800669
  have htrace : WordTrace (prefixWord ++ tailWord_2800669) baseStart_2800669 baseEnd_2800669 := by
    simpa [prefixWord, tailWord_2800669, baseEnd_2800669] using wordTrace_append hprefix tailTrace_2800669
  have hstable : (prefixWord ++ tailWord_2800669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800669).length < 2 ^ (prefixWord ++ tailWord_2800669).sum := by decide
  have hdescent : baseEnd_2800669 < baseStart_2800669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800673 : List Nat := [1, 2, 3, 2, 3, 2, 2, 2, 2, 3]
def baseStart_2800673 : Nat := 118140960795 + 2800673 * 2 ^ 59
def prefixEnd_2800673 : Nat := 4983230072969 + 3 ^ 40 * 2800673 * 2
def baseEnd_2800673 : Nat := 958727603379750725138297

theorem tailTrace_2800673 : CollatzResearch.WordTrace tailWord_2800673 prefixEnd_2800673 958727603379750725138297 := by
  unfold tailWord_2800673
  simp only [CollatzResearch.WordTrace]
  refine ⟨102148936182647512712758673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68099290788431675141839115 102148936182647512712758673)
  ·
    refine ⟨76611702136985634534569005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102148936182647512712758673 76611702136985634534569005)
    ·
      refine ⟨28729388301369612950463377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76611702136985634534569005 28729388301369612950463377)
      ·
        refine ⟨21547041226027209712847533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28729388301369612950463377 21547041226027209712847533)
        ·
          refine ⟨8080140459760203642317825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21547041226027209712847533 8080140459760203642317825)
          ·
            refine ⟨6060105344820152731738369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8080140459760203642317825 6060105344820152731738369)
            ·
              refine ⟨4545079008615114548803777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6060105344820152731738369 4545079008615114548803777)
              ·
                refine ⟨3408809256461335911602833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4545079008615114548803777 3408809256461335911602833)
                ·
                  refine ⟨2556606942346001933702125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3408809256461335911602833 2556606942346001933702125)
                  ·
                    refine ⟨958727603379750725138297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2556606942346001933702125 958727603379750725138297)
                    ·
                      rfl

theorem cell22_2800673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_2800673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800673 prefixEnd_2800673 := by exact prefixLift 2800673
  have htrace : WordTrace (prefixWord ++ tailWord_2800673) baseStart_2800673 baseEnd_2800673 := by
    simpa [prefixWord, tailWord_2800673, baseEnd_2800673] using wordTrace_append hprefix tailTrace_2800673
  have hstable : (prefixWord ++ tailWord_2800673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800673).length < 2 ^ (prefixWord ++ tailWord_2800673).sum := by decide
  have hdescent : baseEnd_2800673 < baseStart_2800673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800701 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 5, 3]
def baseStart_2800701 : Nat := 118140960795 + 2800701 * 2 ^ 59
def prefixEnd_2800701 : Nat := 4983230072969 + 3 ^ 40 * 2800701 * 2
def baseEnd_2800701 : Nat := 958737188351967985438211

theorem tailTrace_2800701 : CollatzResearch.WordTrace tailWord_2800701 prefixEnd_2800701 958737188351967985438211 := by
  unfold tailWord_2800701
  simp only [CollatzResearch.WordTrace]
  refine ⟨102149957426546073494777957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68099971617697382329851971 102149957426546073494777957)
  ·
    refine ⟨19153117017477388780270867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102149957426546073494777957 19153117017477388780270867)
    ·
      refine ⟨28729675526216083170406301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19153117017477388780270867 28729675526216083170406301)
      ·
        refine ⟨10773628322331031188902363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28729675526216083170406301 10773628322331031188902363)
        ·
          refine ⟨16160442483496546783353545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10773628322331031188902363 16160442483496546783353545)
          ·
            refine ⟨12120331862622410087515159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16160442483496546783353545 12120331862622410087515159)
            ·
              refine ⟨18180497793933615131272739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12120331862622410087515159 18180497793933615131272739)
              ·
                refine ⟨27270746690900422696909109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18180497793933615131272739 27270746690900422696909109)
                ·
                  refine ⟨2556632502271914627835229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27270746690900422696909109 2556632502271914627835229)
                  ·
                    refine ⟨958737188351967985438211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2556632502271914627835229 958737188351967985438211)
                    ·
                      rfl

theorem cell22_2800701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_2800701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800701 prefixEnd_2800701 := by exact prefixLift 2800701
  have htrace : WordTrace (prefixWord ++ tailWord_2800701) baseStart_2800701 baseEnd_2800701 := by
    simpa [prefixWord, tailWord_2800701, baseEnd_2800701] using wordTrace_append hprefix tailTrace_2800701
  have hstable : (prefixWord ++ tailWord_2800701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800701).length < 2 ^ (prefixWord ++ tailWord_2800701).sum := by decide
  have hdescent : baseEnd_2800701 < baseStart_2800701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800705 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 2, 4]
def baseStart_2800705 : Nat := 118140960795 + 2800705 * 2 ^ 59
def prefixEnd_2800705 : Nat := 4983230072969 + 3 ^ 40 * 2800705 * 2
def baseEnd_2800705 : Nat := 958738557633713308338199

theorem tailTrace_2800705 : CollatzResearch.WordTrace tailWord_2800705 prefixEnd_2800705 958738557633713308338199 := by
  unfold tailWord_2800705
  simp only [CollatzResearch.WordTrace]
  refine ⟨102150103318531582177923569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68100068879021054785282379 102150103318531582177923569)
  ·
    refine ⟨76612577488898686633442677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102150103318531582177923569 76612577488898686633442677)
    ·
      refine ⟨7182429139584251871885251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76612577488898686633442677 7182429139584251871885251)
      ·
        refine ⟨10773643709376377807827877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7182429139584251871885251 10773643709376377807827877)
        ·
          refine ⟨2020058195508070838967727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10773643709376377807827877 2020058195508070838967727)
          ·
            refine ⟨3030087293262106258451591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020058195508070838967727 3030087293262106258451591)
            ·
              refine ⟨4545130939893159387677387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3030087293262106258451591 4545130939893159387677387)
              ·
                refine ⟨6817696409839739081516081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4545130939893159387677387 6817696409839739081516081)
                ·
                  refine ⟨5113272307379804311137061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6817696409839739081516081 5113272307379804311137061)
                  ·
                    refine ⟨958738557633713308338199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5113272307379804311137061 958738557633713308338199)
                    ·
                      rfl

theorem cell22_2800705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_2800705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800705 prefixEnd_2800705 := by exact prefixLift 2800705
  have htrace : WordTrace (prefixWord ++ tailWord_2800705) baseStart_2800705 baseEnd_2800705 := by
    simpa [prefixWord, tailWord_2800705, baseEnd_2800705] using wordTrace_append hprefix tailTrace_2800705
  have hstable : (prefixWord ++ tailWord_2800705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800705).length < 2 ^ (prefixWord ++ tailWord_2800705).sum := by decide
  have hdescent : baseEnd_2800705 < baseStart_2800705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800746 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 2, 5]
def baseStart_2800746 : Nat := 118140960795 + 2800746 * 2 ^ 59
def prefixEnd_2800746 : Nat := 4983230072969 + 3 ^ 40 * 2800746 * 2
def baseEnd_2800746 : Nat := 958752592771602868063073

theorem tailTrace_2800746 : CollatzResearch.WordTrace tailWord_2800746 prefixEnd_2800746 958752592771602868063073 := by
  unfold tailWord_2800746
  simp only [CollatzResearch.WordTrace]
  refine ⟨25537899677845761545041523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68101065807588697453444061 25537899677845761545041523)
  ·
    refine ⟨38306849516768642317562285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25537899677845761545041523 38306849516768642317562285)
    ·
      refine ⟨14365068568788240869085857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38306849516768642317562285 14365068568788240869085857)
      ·
        refine ⟨10773801426591180651814393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14365068568788240869085857 10773801426591180651814393)
        ·
          refine ⟨8080351069943385488860795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10773801426591180651814393 8080351069943385488860795)
          ·
            refine ⟨12120526604915078233291193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8080351069943385488860795 12120526604915078233291193)
            ·
              refine ⟨9090394953686308674968395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12120526604915078233291193 9090394953686308674968395)
              ·
                refine ⟨13635592430529463012452593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9090394953686308674968395 13635592430529463012452593)
                ·
                  refine ⟨10226694322897097259339445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13635592430529463012452593 10226694322897097259339445)
                  ·
                    refine ⟨958752592771602868063073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10226694322897097259339445 958752592771602868063073)
                    ·
                      rfl

theorem cell22_2800746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_2800746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800746 prefixEnd_2800746 := by exact prefixLift 2800746
  have htrace : WordTrace (prefixWord ++ tailWord_2800746) baseStart_2800746 baseEnd_2800746 := by
    simpa [prefixWord, tailWord_2800746, baseEnd_2800746] using wordTrace_append hprefix tailTrace_2800746
  have hstable : (prefixWord ++ tailWord_2800746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800746).length < 2 ^ (prefixWord ++ tailWord_2800746).sum := by decide
  have hdescent : baseEnd_2800746 < baseStart_2800746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800759 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 6]
def baseStart_2800759 : Nat := 118140960795 + 2800759 * 2 ^ 59
def prefixEnd_2800759 : Nat := 4983230072969 + 3 ^ 40 * 2800759 * 2
def baseEnd_2800759 : Nat := 319585680979091722496011

theorem tailTrace_2800759 : CollatzResearch.WordTrace tailWord_2800759 prefixEnd_2800759 319585680979091722496011 := by
  unfold tailWord_2800759
  simp only [CollatzResearch.WordTrace]
  refine ⟨102152072860335949400389331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68101381906890632933592887 102152072860335949400389331)
  ·
    refine ⟨153228109290503924100583997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102152072860335949400389331 153228109290503924100583997)
    ·
      refine ⟨57460540983938971537718999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153228109290503924100583997 57460540983938971537718999)
      ·
        refine ⟨86190811475908457306578499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57460540983938971537718999 86190811475908457306578499)
        ·
          refine ⟨129286217213862685959867749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86190811475908457306578499 129286217213862685959867749)
          ·
            refine ⟨24241165727599253617475203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129286217213862685959867749 24241165727599253617475203)
            ·
              refine ⟨36361748591398880426212805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24241165727599253617475203 36361748591398880426212805)
              ·
                refine ⟨6817827860887290079914901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36361748591398880426212805 6817827860887290079914901)
                ·
                  refine ⟨319585680979091722496011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6817827860887290079914901 319585680979091722496011)
                  ·
                    rfl

theorem cell22_2800759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 6].length) (baseStart_2800759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800759 prefixEnd_2800759 := by exact prefixLift 2800759
  have htrace : WordTrace (prefixWord ++ tailWord_2800759) baseStart_2800759 baseEnd_2800759 := by
    simpa [prefixWord, tailWord_2800759, baseEnd_2800759] using wordTrace_append hprefix tailTrace_2800759
  have hstable : (prefixWord ++ tailWord_2800759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800759).length < 2 ^ (prefixWord ++ tailWord_2800759).sum := by decide
  have hdescent : baseEnd_2800759 < baseStart_2800759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800789 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 3, 6]
def baseStart_2800789 : Nat := 118140960795 + 2800789 * 2 ^ 59
def prefixEnd_2800789 : Nat := 4983230072969 + 3 ^ 40 * 2800789 * 2
def baseEnd_2800789 : Nat := 958767312550365089237941

theorem tailTrace_2800789 : CollatzResearch.WordTrace tailWord_2800789 prefixEnd_2800789 958767312550365089237941 := by
  unfold tailWord_2800789
  simp only [CollatzResearch.WordTrace]
  refine ⟨102153167050227264523981421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68102111366818176349320947 102153167050227264523981421)
  ·
    refine ⟨38307437643835224196493033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102153167050227264523981421 38307437643835224196493033)
    ·
      refine ⟨28730578232876418147369775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38307437643835224196493033 28730578232876418147369775)
      ·
        refine ⟨43095867349314627221054663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28730578232876418147369775 43095867349314627221054663)
        ·
          refine ⟨64643801023971940831581995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43095867349314627221054663 64643801023971940831581995)
          ·
            refine ⟨96965701535957911247372993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64643801023971940831581995 96965701535957911247372993)
            ·
              refine ⟨72724276151968433435529745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96965701535957911247372993 72724276151968433435529745)
              ·
                refine ⟨54543207113976325076647309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72724276151968433435529745 54543207113976325076647309)
                ·
                  refine ⟨20453702667741121903742741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54543207113976325076647309 20453702667741121903742741)
                  ·
                    refine ⟨958767312550365089237941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20453702667741121903742741 958767312550365089237941)
                    ·
                      rfl

theorem cell22_2800789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_2800789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800789 prefixEnd_2800789 := by exact prefixLift 2800789
  have htrace : WordTrace (prefixWord ++ tailWord_2800789) baseStart_2800789 baseEnd_2800789 := by
    simpa [prefixWord, tailWord_2800789, baseEnd_2800789] using wordTrace_append hprefix tailTrace_2800789
  have hstable : (prefixWord ++ tailWord_2800789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800789).length < 2 ^ (prefixWord ++ tailWord_2800789).sum := by decide
  have hdescent : baseEnd_2800789 < baseStart_2800789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800819 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 2, 7]
def baseStart_2800819 : Nat := 118140960795 + 2800819 * 2 ^ 59
def prefixEnd_2800819 : Nat := 4983230072969 + 3 ^ 40 * 2800819 * 2
def baseEnd_2800819 : Nat := 958777582163455010987849

theorem tailTrace_2800819 : CollatzResearch.WordTrace tailWord_2800819 prefixEnd_2800819 958777582163455010987849 := by
  unfold tailWord_2800819
  simp only [CollatzResearch.WordTrace]
  refine ⟨102154261240118579647573511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68102840826745719765049007 102154261240118579647573511)
  ·
    refine ⟨153231391860177869471360267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102154261240118579647573511 153231391860177869471360267)
    ·
      refine ⟨229847087790266804207040401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153231391860177869471360267 229847087790266804207040401)
      ·
        refine ⟨172385315842700103155280301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229847087790266804207040401 172385315842700103155280301)
        ·
          refine ⟨64644493441012538683230113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172385315842700103155280301 64644493441012538683230113)
          ·
            refine ⟨48483370080759404012422585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64644493441012538683230113 48483370080759404012422585)
            ·
              refine ⟨36362527560569553009316939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48483370080759404012422585 36362527560569553009316939)
              ·
                refine ⟨54543791340854329513975409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36362527560569553009316939 54543791340854329513975409)
                ·
                  refine ⟨40907843505640747135481557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54543791340854329513975409 40907843505640747135481557)
                  ·
                    refine ⟨958777582163455010987849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40907843505640747135481557 958777582163455010987849)
                    ·
                      rfl

theorem cell22_2800819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 7].length) (baseStart_2800819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800819 prefixEnd_2800819 := by exact prefixLift 2800819
  have htrace : WordTrace (prefixWord ++ tailWord_2800819) baseStart_2800819 baseEnd_2800819 := by
    simpa [prefixWord, tailWord_2800819, baseEnd_2800819] using wordTrace_append hprefix tailTrace_2800819
  have hstable : (prefixWord ++ tailWord_2800819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800819).length < 2 ^ (prefixWord ++ tailWord_2800819).sum := by decide
  have hdescent : baseEnd_2800819 < baseStart_2800819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800900 : List Nat := [2, 3, 2, 2, 2, 3, 1, 2, 5]
def baseStart_2800900 : Nat := 118140960795 + 2800900 * 2 ^ 59
def prefixEnd_2800900 : Nat := 4983230072969 + 3 ^ 40 * 2800900 * 2
def baseEnd_2800900 : Nat := 319601770039599266570867

theorem tailTrace_2800900 : CollatzResearch.WordTrace tailWord_2800900 prefixEnd_2800900 319601770039599266570867 := by
  unfold tailWord_2800900
  simp only [CollatzResearch.WordTrace]
  refine ⟨51078607776412565240636077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68104810368550086987514769 51078607776412565240636077)
  ·
    refine ⟨19154477916154711965238529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51078607776412565240636077 19154477916154711965238529)
    ·
      refine ⟨14365858437116033973928897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19154477916154711965238529 14365858437116033973928897)
      ·
        refine ⟨10774393827837025480446673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14365858437116033973928897 10774393827837025480446673)
        ·
          refine ⟨8080795370877769110335005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10774393827837025480446673 8080795370877769110335005)
          ·
            refine ⟨3030298264079163416375627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8080795370877769110335005 3030298264079163416375627)
            ·
              refine ⟨4545447396118745124563441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3030298264079163416375627 4545447396118745124563441)
              ·
                refine ⟨3409085547089058843422581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4545447396118745124563441 3409085547089058843422581)
                ·
                  refine ⟨319601770039599266570867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3409085547089058843422581 319601770039599266570867)
                  ·
                    rfl

theorem cell22_2800900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_2800900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800900 prefixEnd_2800900 := by exact prefixLift 2800900
  have htrace : WordTrace (prefixWord ++ tailWord_2800900) baseStart_2800900 baseEnd_2800900 := by
    simpa [prefixWord, tailWord_2800900, baseEnd_2800900] using wordTrace_append hprefix tailTrace_2800900
  have hstable : (prefixWord ++ tailWord_2800900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800900).length < 2 ^ (prefixWord ++ tailWord_2800900).sum := by decide
  have hdescent : baseEnd_2800900 < baseStart_2800900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800945 : List Nat := [1, 2, 2, 3, 3, 1, 3, 3, 4]
def baseStart_2800945 : Nat := 118140960795 + 2800945 * 2 ^ 59
def prefixEnd_2800945 : Nat := 4983230072969 + 3 ^ 40 * 2800945 * 2
def baseEnd_2800945 : Nat := 319606904846144227445821

theorem tailTrace_2800945 : CollatzResearch.WordTrace tailWord_2800945 prefixEnd_2800945 319606904846144227445821 := by
  unfold tailWord_2800945
  simp only [CollatzResearch.WordTrace]
  refine ⟨102158856837662103166660289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68105904558441402111106859 102158856837662103166660289)
  ·
    refine ⟨76619142628246577374995217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102158856837662103166660289 76619142628246577374995217)
    ·
      refine ⟨57464356971184933031246413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76619142628246577374995217 57464356971184933031246413)
      ·
        refine ⟨21549133864194349886717405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57464356971184933031246413 21549133864194349886717405)
        ·
          refine ⟨8080925199072881207519027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21549133864194349886717405 8080925199072881207519027)
          ·
            refine ⟨12121387798609321811278541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8080925199072881207519027 12121387798609321811278541)
            ·
              refine ⟨4545520424478495679229453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12121387798609321811278541 4545520424478495679229453)
              ·
                refine ⟨1704570159179435879711045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4545520424478495679229453 1704570159179435879711045)
                ·
                  refine ⟨319606904846144227445821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1704570159179435879711045 319606904846144227445821)
                  ·
                    rfl

theorem cell22_2800945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 4].length) (baseStart_2800945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800945 prefixEnd_2800945 := by exact prefixLift 2800945
  have htrace : WordTrace (prefixWord ++ tailWord_2800945) baseStart_2800945 baseEnd_2800945 := by
    simpa [prefixWord, tailWord_2800945, baseEnd_2800945] using wordTrace_append hprefix tailTrace_2800945
  have hstable : (prefixWord ++ tailWord_2800945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800945).length < 2 ^ (prefixWord ++ tailWord_2800945).sum := by decide
  have hdescent : baseEnd_2800945 < baseStart_2800945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800956 : List Nat := [2, 2, 2, 2, 1, 3, 10]
def baseStart_2800956 : Nat := 118140960795 + 2800956 * 2 ^ 59
def prefixEnd_2800956 : Nat := 4983230072969 + 3 ^ 40 * 2800956 * 2
def baseEnd_2800956 : Nat := 35512017780119715567127

theorem tailTrace_2800956 : CollatzResearch.WordTrace tailWord_2800956 prefixEnd_2800956 35512017780119715567127 := by
  unfold tailWord_2800956
  simp only [CollatzResearch.WordTrace]
  refine ⟨51079629020311126022655361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68106172027081501363540481 51079629020311126022655361)
  ·
    refine ⟨38309721765233344516991521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51079629020311126022655361 38309721765233344516991521)
    ·
      refine ⟨28732291323925008387743641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38309721765233344516991521 28732291323925008387743641)
      ·
        refine ⟨21549218492943756290807731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28732291323925008387743641 21549218492943756290807731)
        ·
          refine ⟨32323827739415634436211597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21549218492943756290807731 32323827739415634436211597)
          ·
            refine ⟨12121435402280862913579349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32323827739415634436211597 12121435402280862913579349)
            ·
              refine ⟨35512017780119715567127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12121435402280862913579349 35512017780119715567127)
              ·
                rfl

theorem cell22_2800956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 10].length) (baseStart_2800956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800956 prefixEnd_2800956 := by exact prefixLift 2800956
  have htrace : WordTrace (prefixWord ++ tailWord_2800956) baseStart_2800956 baseEnd_2800956 := by
    simpa [prefixWord, tailWord_2800956, baseEnd_2800956] using wordTrace_append hprefix tailTrace_2800956
  have hstable : (prefixWord ++ tailWord_2800956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800956).length < 2 ^ (prefixWord ++ tailWord_2800956).sum := by decide
  have hdescent : baseEnd_2800956 < baseStart_2800956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801001 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 7]
def baseStart_2801001 : Nat := 118140960795 + 2801001 * 2 ^ 59
def prefixEnd_2801001 : Nat := 4983230072969 + 3 ^ 40 * 2801001 * 2
def baseEnd_2801001 : Nat := 319613294827622400979097

theorem tailTrace_2801001 : CollatzResearch.WordTrace tailWord_2801001 prefixEnd_2801001 319613294827622400979097 := by
  unfold tailWord_2801001
  simp only [CollatzResearch.WordTrace]
  refine ⟨102160899325459224730698857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68107266216972816487132571 102160899325459224730698857)
  ·
    refine ⟨76620674494094418548024143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102160899325459224730698857 76620674494094418548024143)
    ·
      refine ⟨114931011741141627822036215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76620674494094418548024143 114931011741141627822036215)
      ·
        refine ⟨172396517611712441733054323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114931011741141627822036215 172396517611712441733054323)
        ·
          refine ⟨258594776417568662599581485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172396517611712441733054323 258594776417568662599581485)
          ·
            refine ⟨96973041156588248474843057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258594776417568662599581485 96973041156588248474843057)
            ·
              refine ⟨72729780867441186356132293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96973041156588248474843057 72729780867441186356132293)
              ·
                refine ⟨13636833912645222441774805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72729780867441186356132293 13636833912645222441774805)
                ·
                  refine ⟨319613294827622400979097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13636833912645222441774805 319613294827622400979097)
                  ·
                    rfl

theorem cell22_2801001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 7].length) (baseStart_2801001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801001 prefixEnd_2801001 := by exact prefixLift 2801001
  have htrace : WordTrace (prefixWord ++ tailWord_2801001) baseStart_2801001 baseEnd_2801001 := by
    simpa [prefixWord, tailWord_2801001, baseEnd_2801001] using wordTrace_append hprefix tailTrace_2801001
  have hstable : (prefixWord ++ tailWord_2801001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801001).length < 2 ^ (prefixWord ++ tailWord_2801001).sum := by decide
  have hdescent : baseEnd_2801001 < baseStart_2801001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801016 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 5, 7]
def baseStart_2801016 : Nat := 118140960795 + 2801016 * 2 ^ 59
def prefixEnd_2801016 : Nat := 4983230072969 + 3 ^ 40 * 2801016 * 2
def baseEnd_2801016 : Nat := 958845019289412163812245

theorem tailTrace_2801016 : CollatzResearch.WordTrace tailWord_2801016 prefixEnd_2801016 958845019289412163812245 := by
  unfold tailWord_2801016
  simp only [CollatzResearch.WordTrace]
  refine ⟨51080723210202441146247451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68107630946936588194996601 51080723210202441146247451)
  ·
    refine ⟨76621084815303661719371177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51080723210202441146247451 76621084815303661719371177)
    ·
      refine ⟨57465813611477746289528383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76621084815303661719371177 57465813611477746289528383)
      ·
        refine ⟨86198720417216619434292575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57465813611477746289528383 86198720417216619434292575)
        ·
          refine ⟨129298080625824929151438863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86198720417216619434292575 129298080625824929151438863)
          ·
            refine ⟨193947120938737393727158295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129298080625824929151438863 193947120938737393727158295)
            ·
              refine ⟨290920681408106090590737443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193947120938737393727158295 290920681408106090590737443)
              ·
                refine ⟨436381022112159135886106165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290920681408106090590737443 436381022112159135886106165)
                ·
                  refine ⟨40910720823014918989322453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 436381022112159135886106165 40910720823014918989322453)
                  ·
                    refine ⟨958845019289412163812245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40910720823014918989322453 958845019289412163812245)
                    ·
                      rfl

theorem cell22_2801016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_2801016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801016 prefixEnd_2801016 := by exact prefixLift 2801016
  have htrace : WordTrace (prefixWord ++ tailWord_2801016) baseStart_2801016 baseEnd_2801016 := by
    simpa [prefixWord, tailWord_2801016, baseEnd_2801016] using wordTrace_append hprefix tailTrace_2801016
  have hstable : (prefixWord ++ tailWord_2801016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801016).length < 2 ^ (prefixWord ++ tailWord_2801016).sum := by decide
  have hdescent : baseEnd_2801016 < baseStart_2801016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801063 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 8]
def baseStart_2801063 : Nat := 118140960795 + 2801063 * 2 ^ 59
def prefixEnd_2801063 : Nat := 4983230072969 + 3 ^ 40 * 2801063 * 2
def baseEnd_2801063 : Nat := 319620369449973235962367

theorem tailTrace_2801063 : CollatzResearch.WordTrace tailWord_2801063 prefixEnd_2801063 319620369449973235962367 := by
  unfold tailWord_2801063
  simp only [CollatzResearch.WordTrace]
  refine ⟨102163160651234609319455843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68108773767489739546303895 102163160651234609319455843)
  ·
    refine ⟨153244740976851913979183765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102163160651234609319455843 153244740976851913979183765)
    ·
      refine ⟨7183347233289933467774239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 153244740976851913979183765 7183347233289933467774239)
      ·
        refine ⟨10775020849934900201661359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7183347233289933467774239 10775020849934900201661359)
        ·
          refine ⟨16162531274902350302492039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10775020849934900201661359 16162531274902350302492039)
          ·
            refine ⟨24243796912353525453738059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16162531274902350302492039 24243796912353525453738059)
            ·
              refine ⟨36365695368530288180607089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24243796912353525453738059 36365695368530288180607089)
              ·
                refine ⟨27274271526397716135455317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36365695368530288180607089 27274271526397716135455317)
                ·
                  refine ⟨319620369449973235962367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27274271526397716135455317 319620369449973235962367)
                  ·
                    rfl

theorem cell22_2801063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 8].length) (baseStart_2801063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801063 prefixEnd_2801063 := by exact prefixLift 2801063
  have htrace : WordTrace (prefixWord ++ tailWord_2801063) baseStart_2801063 baseEnd_2801063 := by
    simpa [prefixWord, tailWord_2801063, baseEnd_2801063] using wordTrace_append hprefix tailTrace_2801063
  have hstable : (prefixWord ++ tailWord_2801063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801063).length < 2 ^ (prefixWord ++ tailWord_2801063).sum := by decide
  have hdescent : baseEnd_2801063 < baseStart_2801063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801080 : List Nat := [2, 1, 2, 1, 2, 2, 4, 4, 4]
def baseStart_2801080 : Nat := 118140960795 + 2801080 * 2 ^ 59
def prefixEnd_2801080 : Nat := 4983230072969 + 3 ^ 40 * 2801080 * 2
def baseEnd_2801080 : Nat := 319622309265779110070683

theorem tailTrace_2801080 : CollatzResearch.WordTrace tailWord_2801080 prefixEnd_2801080 319622309265779110070683 := by
  unfold tailWord_2801080
  simp only [CollatzResearch.WordTrace]
  refine ⟨51081890346086510611412347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68109187128115347481883129 51081890346086510611412347)
  ·
    refine ⟨76622835519129765917118521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51081890346086510611412347 76622835519129765917118521)
    ·
      refine ⟨57467126639347324437838891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76622835519129765917118521 57467126639347324437838891)
      ·
        refine ⟨86200689959020986656758337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57467126639347324437838891 86200689959020986656758337)
        ·
          refine ⟨64650517469265739992568753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86200689959020986656758337 64650517469265739992568753)
          ·
            refine ⟨48487888101949304994426565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64650517469265739992568753 48487888101949304994426565)
            ·
              refine ⟨9091479019115494686454981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48487888101949304994426565 9091479019115494686454981)
              ·
                refine ⟨1704652316084155253710309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9091479019115494686454981 1704652316084155253710309)
                ·
                  refine ⟨319622309265779110070683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1704652316084155253710309 319622309265779110070683)
                  ·
                    rfl

theorem cell22_2801080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 4].length) (baseStart_2801080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801080 prefixEnd_2801080 := by exact prefixLift 2801080
  have htrace : WordTrace (prefixWord ++ tailWord_2801080) baseStart_2801080 baseEnd_2801080 := by
    simpa [prefixWord, tailWord_2801080, baseEnd_2801080] using wordTrace_append hprefix tailTrace_2801080
  have hstable : (prefixWord ++ tailWord_2801080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801080).length < 2 ^ (prefixWord ++ tailWord_2801080).sum := by decide
  have hdescent : baseEnd_2801080 < baseStart_2801080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801125 : List Nat := [1, 3, 1, 5, 1, 3, 8]
def baseStart_2801125 : Nat := 118140960795 + 2801125 * 2 ^ 59
def prefixEnd_2801125 : Nat := 4983230072969 + 3 ^ 40 * 2801125 * 2
def baseEnd_2801125 : Nat := 35514160452480452327293

theorem tailTrace_2801125 : CollatzResearch.WordTrace tailWord_2801125 prefixEnd_2801125 35514160452480452327293 := by
  unfold tailWord_2801125
  simp only [CollatzResearch.WordTrace]
  refine ⟨102165421977009993908212829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68110281318006662605475219 102165421977009993908212829)
  ·
    refine ⟨38312033241378747715579811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102165421977009993908212829 38312033241378747715579811)
    ·
      refine ⟨57468049862068121573369717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38312033241378747715579811 57468049862068121573369717)
      ·
        refine ⟨5387629674568886397503411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57468049862068121573369717 5387629674568886397503411)
        ·
          refine ⟨8081444511853329596255117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5387629674568886397503411 8081444511853329596255117)
          ·
            refine ⟨3030541691944998598595669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8081444511853329596255117 3030541691944998598595669)
            ·
              refine ⟨35514160452480452327293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3030541691944998598595669 35514160452480452327293)
              ·
                rfl

theorem cell22_2801125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 8].length) (baseStart_2801125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801125 prefixEnd_2801125 := by exact prefixLift 2801125
  have htrace : WordTrace (prefixWord ++ tailWord_2801125) baseStart_2801125 baseEnd_2801125 := by
    simpa [prefixWord, tailWord_2801125, baseEnd_2801125] using wordTrace_append hprefix tailTrace_2801125
  have hstable : (prefixWord ++ tailWord_2801125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801125).length < 2 ^ (prefixWord ++ tailWord_2801125).sum := by decide
  have hdescent : baseEnd_2801125 < baseStart_2801125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801182 : List Nat := [4, 3, 3, 1, 2, 1, 2, 2, 4]
def baseStart_2801182 : Nat := 118140960795 + 2801182 * 2 ^ 59
def prefixEnd_2801182 : Nat := 4983230072969 + 3 ^ 40 * 2801182 * 2
def baseEnd_2801182 : Nat := 319633948160614354720579

theorem tailTrace_2801182 : CollatzResearch.WordTrace tailWord_2801182 prefixEnd_2801182 319633948160614354720579 := by
  unfold tailWord_2801182
  simp only [CollatzResearch.WordTrace]
  refine ⟨12770937617225436580379725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68111667291868995095358533 12770937617225436580379725)
  ·
    refine ⟨4789101606459538717642397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12770937617225436580379725 4789101606459538717642397)
    ·
      refine ⟨1795913102422327019115899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4789101606459538717642397 1795913102422327019115899)
      ·
        refine ⟨2693869653633490528673849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1795913102422327019115899 2693869653633490528673849)
        ·
          refine ⟨2020402240225117896505387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2693869653633490528673849 2020402240225117896505387)
          ·
            refine ⟨3030603360337676844758081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020402240225117896505387 3030603360337676844758081)
            ·
              refine ⟨2272952520253257633568561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3030603360337676844758081 2272952520253257633568561)
              ·
                refine ⟨1704714390189943225176421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2272952520253257633568561 1704714390189943225176421)
                ·
                  refine ⟨319633948160614354720579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1704714390189943225176421 319633948160614354720579)
                  ·
                    rfl

theorem cell22_2801182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_2801182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801182 prefixEnd_2801182 := by exact prefixLift 2801182
  have htrace : WordTrace (prefixWord ++ tailWord_2801182) baseStart_2801182 baseEnd_2801182 := by
    simpa [prefixWord, tailWord_2801182, baseEnd_2801182] using wordTrace_append hprefix tailTrace_2801182
  have hstable : (prefixWord ++ tailWord_2801182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801182).length < 2 ^ (prefixWord ++ tailWord_2801182).sum := by decide
  have hdescent : baseEnd_2801182 < baseStart_2801182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801187 : List Nat := [1, 1, 1, 4, 5, 1, 2, 2, 5]
def baseStart_2801187 : Nat := 118140960795 + 2801187 * 2 ^ 59
def prefixEnd_2801187 : Nat := 4983230072969 + 3 ^ 40 * 2801187 * 2
def baseEnd_2801187 : Nat := 319634518694674905928907

theorem tailTrace_2801187 : CollatzResearch.WordTrace tailWord_2801187 prefixEnd_2801187 319634518694674905928907 := by
  unfold tailWord_2801187
  simp only [CollatzResearch.WordTrace]
  refine ⟨102167683302785378496969815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68111788868523585664646543 102167683302785378496969815)
  ·
    refine ⟨153251524954178067745454723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102167683302785378496969815 153251524954178067745454723)
    ·
      refine ⟨229877287431267101618182085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153251524954178067745454723 229877287431267101618182085)
      ·
        refine ⟨43101991393362581553409141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229877287431267101618182085 43101991393362581553409141)
        ·
          refine ⟨4040811693127742020632107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43101991393362581553409141 4040811693127742020632107)
          ·
            refine ⟨6061217539691613030948161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4040811693127742020632107 6061217539691613030948161)
            ·
              refine ⟨4545913154768709773211121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6061217539691613030948161 4545913154768709773211121)
              ·
                refine ⟨3409434866076532329908341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4545913154768709773211121 3409434866076532329908341)
                ·
                  refine ⟨319634518694674905928907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3409434866076532329908341 319634518694674905928907)
                  ·
                    rfl

theorem cell22_2801187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 5].length) (baseStart_2801187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801187 prefixEnd_2801187 := by exact prefixLift 2801187
  have htrace : WordTrace (prefixWord ++ tailWord_2801187) baseStart_2801187 baseEnd_2801187 := by
    simpa [prefixWord, tailWord_2801187, baseEnd_2801187] using wordTrace_append hprefix tailTrace_2801187
  have hstable : (prefixWord ++ tailWord_2801187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801187).length < 2 ^ (prefixWord ++ tailWord_2801187).sum := by decide
  have hdescent : baseEnd_2801187 < baseStart_2801187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801215 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 6]
def baseStart_2801215 : Nat := 118140960795 + 2801215 * 2 ^ 59
def prefixEnd_2801215 : Nat := 4983230072969 + 3 ^ 40 * 2801215 * 2
def baseEnd_2801215 : Nat := 319637713685413992695545

theorem tailTrace_2801215 : CollatzResearch.WordTrace tailWord_2801215 prefixEnd_2801215 319637713685413992695545 := by
  unfold tailWord_2801215
  simp only [CollatzResearch.WordTrace]
  refine ⟨102168704546683939278989099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68112469697789292852659399 102168704546683939278989099)
  ·
    refine ⟨153253056820025908918483649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102168704546683939278989099 153253056820025908918483649)
    ·
      refine ⟨114939792615019431688862737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153253056820025908918483649 114939792615019431688862737)
      ·
        refine ⟨86204844461264573766647053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114939792615019431688862737 86204844461264573766647053)
        ·
          refine ⟨32326816672974215162492645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86204844461264573766647053 32326816672974215162492645)
          ·
            refine ⟨6061278126182665342967371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32326816672974215162492645 6061278126182665342967371)
            ·
              refine ⟨9091917189273998014451057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6061278126182665342967371 9091917189273998014451057)
              ·
                refine ⟨6818937891955498510838293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9091917189273998014451057 6818937891955498510838293)
                ·
                  refine ⟨319637713685413992695545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6818937891955498510838293 319637713685413992695545)
                  ·
                    rfl

theorem cell22_2801215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 6].length) (baseStart_2801215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801215 prefixEnd_2801215 := by exact prefixLift 2801215
  have htrace : WordTrace (prefixWord ++ tailWord_2801215) baseStart_2801215 baseEnd_2801215 := by
    simpa [prefixWord, tailWord_2801215, baseEnd_2801215] using wordTrace_append hprefix tailTrace_2801215
  have hstable : (prefixWord ++ tailWord_2801215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801215).length < 2 ^ (prefixWord ++ tailWord_2801215).sum := by decide
  have hdescent : baseEnd_2801215 < baseStart_2801215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801217 : List Nat := [1, 2, 5, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2801217 : Nat := 118140960795 + 2801217 * 2 ^ 59
def prefixEnd_2801217 : Nat := 4983230072969 + 3 ^ 40 * 2801217 * 2
def baseEnd_2801217 : Nat := 958913825697114639536629

theorem tailTrace_2801217 : CollatzResearch.WordTrace tailWord_2801217 prefixEnd_2801217 958913825697114639536629 := by
  unfold tailWord_2801217
  simp only [CollatzResearch.WordTrace]
  refine ⟨102168777492676693620561905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68112518328451129080374603 102168777492676693620561905)
  ·
    refine ⟨76626583119507520215421429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102168777492676693620561905 76626583119507520215421429)
    ·
      refine ⟨7183742167453830020195759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76626583119507520215421429 7183742167453830020195759)
      ·
        refine ⟨10775613251180745030293639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7183742167453830020195759 10775613251180745030293639)
        ·
          refine ⟨16163419876771117545440459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10775613251180745030293639 16163419876771117545440459)
          ·
            refine ⟨24245129815156676318160689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16163419876771117545440459 24245129815156676318160689)
            ·
              refine ⟨18183847361367507238620517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24245129815156676318160689 18183847361367507238620517)
              ·
                refine ⟨3409471380256407607241347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18183847361367507238620517 3409471380256407607241347)
                ·
                  refine ⟨5114207070384611410862021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3409471380256407607241347 5114207070384611410862021)
                  ·
                    refine ⟨958913825697114639536629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5114207070384611410862021 958913825697114639536629)
                    ·
                      rfl

theorem cell22_2801217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2801217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801217 prefixEnd_2801217 := by exact prefixLift 2801217
  have htrace : WordTrace (prefixWord ++ tailWord_2801217) baseStart_2801217 baseEnd_2801217 := by
    simpa [prefixWord, tailWord_2801217, baseEnd_2801217] using wordTrace_append hprefix tailTrace_2801217
  have hstable : (prefixWord ++ tailWord_2801217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801217).length < 2 ^ (prefixWord ++ tailWord_2801217).sum := by decide
  have hdescent : baseEnd_2801217 < baseStart_2801217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801232 : List Nat := [2, 1, 1, 1, 1, 3, 6, 3, 4]
def baseStart_2801232 : Nat := 118140960795 + 2801232 * 2 ^ 59
def prefixEnd_2801232 : Nat := 4983230072969 + 3 ^ 40 * 2801232 * 2
def baseEnd_2801232 : Nat := 319639653501219866803861

theorem tailTrace_2801232 : CollatzResearch.WordTrace tailWord_2801232 prefixEnd_2801232 319639653501219866803861 := by
  unfold tailWord_2801232
  simp only [CollatzResearch.WordTrace]
  refine ⟨51084662293811175591178975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68112883058414900788238633 51084662293811175591178975)
  ·
    refine ⟨76626993440716763386768463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51084662293811175591178975 76626993440716763386768463)
    ·
      refine ⟨114940490161075145080152695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76626993440716763386768463 114940490161075145080152695)
      ·
        refine ⟨172410735241612717620229043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114940490161075145080152695 172410735241612717620229043)
        ·
          refine ⟨258616102862419076430343565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172410735241612717620229043 258616102862419076430343565)
          ·
            refine ⟨96981038573407153661378837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258616102862419076430343565 96981038573407153661378837)
            ·
              refine ⟨4545986183128460327877133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96981038573407153661378837 4545986183128460327877133)
              ·
                refine ⟨1704744818673172622953925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4545986183128460327877133 1704744818673172622953925)
                ·
                  refine ⟨319639653501219866803861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1704744818673172622953925 319639653501219866803861)
                  ·
                    rfl

theorem cell22_2801232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 4].length) (baseStart_2801232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801232 prefixEnd_2801232 := by exact prefixLift 2801232
  have htrace : WordTrace (prefixWord ++ tailWord_2801232) baseStart_2801232 baseEnd_2801232 := by
    simpa [prefixWord, tailWord_2801232, baseEnd_2801232] using wordTrace_append hprefix tailTrace_2801232
  have hstable : (prefixWord ++ tailWord_2801232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801232).length < 2 ^ (prefixWord ++ tailWord_2801232).sum := by decide
  have hdescent : baseEnd_2801232 < baseStart_2801232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801234 : List Nat := [3, 2, 2, 1, 2, 2, 4, 1, 1, 4]
def baseStart_2801234 : Nat := 118140960795 + 2801234 * 2 ^ 59
def prefixEnd_2801234 : Nat := 4983230072969 + 3 ^ 40 * 2801234 * 2
def baseEnd_2801234 : Nat := 958919645144532261861577

theorem tailTrace_2801234 : CollatzResearch.WordTrace tailWord_2801234 prefixEnd_2801234 958919645144532261861577 := by
  unfold tailWord_2801234
  simp only [CollatzResearch.WordTrace]
  refine ⟨25542349383403776380982689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68112931689076737015953837 25542349383403776380982689)
  ·
    refine ⟨19156762037552832285737017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25542349383403776380982689 19156762037552832285737017)
    ·
      refine ⟨14367571528164624214302763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19156762037552832285737017 14367571528164624214302763)
      ·
        refine ⟨21551357292246936321454145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14367571528164624214302763 21551357292246936321454145)
        ·
          refine ⟨16163517969185202241090609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21551357292246936321454145 16163517969185202241090609)
          ·
            refine ⟨12122638476888901680817957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16163517969185202241090609 12122638476888901680817957)
            ·
              refine ⟨2272994714416669065153367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12122638476888901680817957 2272994714416669065153367)
              ·
                refine ⟨3409492071625003597730051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2272994714416669065153367 3409492071625003597730051)
                ·
                  refine ⟨5114238107437505396595077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3409492071625003597730051 5114238107437505396595077)
                  ·
                    refine ⟨958919645144532261861577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5114238107437505396595077 958919645144532261861577)
                    ·
                      rfl

theorem cell22_2801234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_2801234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801234 prefixEnd_2801234 := by exact prefixLift 2801234
  have htrace : WordTrace (prefixWord ++ tailWord_2801234) baseStart_2801234 baseEnd_2801234 := by
    simpa [prefixWord, tailWord_2801234, baseEnd_2801234] using wordTrace_append hprefix tailTrace_2801234
  have hstable : (prefixWord ++ tailWord_2801234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801234).length < 2 ^ (prefixWord ++ tailWord_2801234).sum := by decide
  have hdescent : baseEnd_2801234 < baseStart_2801234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801238 : List Nat := [5, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_2801238 : Nat := 118140960795 + 2801238 * 2 ^ 59
def prefixEnd_2801238 : Nat := 4983230072969 + 3 ^ 40 * 2801238 * 2
def baseEnd_2801238 : Nat := 319640338142092528253855

theorem tailTrace_2801238 : CollatzResearch.WordTrace tailWord_2801238 prefixEnd_2801238 319640338142092528253855 := by
  unfold tailWord_2801238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6385596464100038387942273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68113028950400409471384245 6385596464100038387942273)
  ·
    refine ⟨4789197348075028790956705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6385596464100038387942273 4789197348075028790956705)
    ·
      refine ⟨3591898011056271593217529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4789197348075028790956705 3591898011056271593217529)
      ·
        refine ⟨2693923508292203694913147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3591898011056271593217529 2693923508292203694913147)
        ·
          refine ⟨4040885262438305542369721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2693923508292203694913147 4040885262438305542369721)
          ·
            refine ⟨3030663946828729156777291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4040885262438305542369721 3030663946828729156777291)
            ·
              refine ⟨4545995920243093735165937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3030663946828729156777291 4545995920243093735165937)
              ·
                refine ⟨3409496940182320301374453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4545995920243093735165937 3409496940182320301374453)
                ·
                  refine ⟨319640338142092528253855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3409496940182320301374453 319640338142092528253855)
                  ·
                    rfl

theorem cell22_2801238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_2801238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801238 prefixEnd_2801238 := by exact prefixLift 2801238
  have htrace : WordTrace (prefixWord ++ tailWord_2801238) baseStart_2801238 baseEnd_2801238 := by
    simpa [prefixWord, tailWord_2801238, baseEnd_2801238] using wordTrace_append hprefix tailTrace_2801238
  have hstable : (prefixWord ++ tailWord_2801238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801238).length < 2 ^ (prefixWord ++ tailWord_2801238).sum := by decide
  have hdescent : baseEnd_2801238 < baseStart_2801238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801277 : List Nat := [1, 4, 1, 1, 4, 1, 4, 6]
def baseStart_2801277 : Nat := 118140960795 + 2801277 * 2 ^ 59
def prefixEnd_2801277 : Nat := 4983230072969 + 3 ^ 40 * 2801277 * 2
def baseEnd_2801277 : Nat := 106548262769254942559605

theorem tailTrace_2801277 : CollatzResearch.WordTrace tailWord_2801277 prefixEnd_2801277 106548262769254942559605 := by
  unfold tailWord_2801277
  simp only [CollatzResearch.WordTrace]
  refine ⟨102170965872459323867746085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68113977248306215911830723 102170965872459323867746085)
  ·
    refine ⟨19157056101086123225202391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102170965872459323867746085 19157056101086123225202391)
    ·
      refine ⟨28735584151629184837803587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19157056101086123225202391 28735584151629184837803587)
      ·
        refine ⟨43103376227443777256705381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28735584151629184837803587 43103376227443777256705381)
        ·
          refine ⟨8081883042645708235632259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43103376227443777256705381 8081883042645708235632259)
          ·
            refine ⟨12122824563968562353448389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8081883042645708235632259 12122824563968562353448389)
            ·
              refine ⟨2273029605744105441271573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12122824563968562353448389 2273029605744105441271573)
              ·
                refine ⟨106548262769254942559605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2273029605744105441271573 106548262769254942559605)
                ·
                  rfl

theorem cell22_2801277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 6].length) (baseStart_2801277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801277 prefixEnd_2801277 := by exact prefixLift 2801277
  have htrace : WordTrace (prefixWord ++ tailWord_2801277) baseStart_2801277 baseEnd_2801277 := by
    simpa [prefixWord, tailWord_2801277, baseEnd_2801277] using wordTrace_append hprefix tailTrace_2801277
  have hstable : (prefixWord ++ tailWord_2801277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801277).length < 2 ^ (prefixWord ++ tailWord_2801277).sum := by decide
  have hdescent : baseEnd_2801277 < baseStart_2801277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801395 : List Nat := [1, 1, 1, 2, 2, 3, 2, 10]
def baseStart_2801395 : Nat := 118140960795 + 2801395 * 2 ^ 59
def prefixEnd_2801395 : Nat := 4983230072969 + 3 ^ 40 * 2801395 * 2
def baseEnd_2801395 : Nat := 106552750970531278731787

theorem tailTrace_2801395 : CollatzResearch.WordTrace tailWord_2801395 prefixEnd_2801395 106552750970531278731787 := by
  unfold tailWord_2801395
  simp only [CollatzResearch.WordTrace]
  refine ⟨102175269686031830020541639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68116846457354553347027759 102175269686031830020541639)
  ·
    refine ⟨153262904529047745030812459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102175269686031830020541639 153262904529047745030812459)
    ·
      refine ⟨229894356793571617546218689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153262904529047745030812459 229894356793571617546218689)
      ·
        refine ⟨172420767595178713159664017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229894356793571617546218689 172420767595178713159664017)
        ·
          refine ⟨129315575696384034869748013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172420767595178713159664017 129315575696384034869748013)
          ·
            refine ⟨48493340886144013076155505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129315575696384034869748013 48493340886144013076155505)
            ·
              refine ⟨36370005664608009807116629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48493340886144013076155505 36370005664608009807116629)
              ·
                refine ⟨106552750970531278731787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36370005664608009807116629 106552750970531278731787)
                ·
                  rfl

theorem cell22_2801395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 10].length) (baseStart_2801395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801395 prefixEnd_2801395 := by exact prefixLift 2801395
  have htrace : WordTrace (prefixWord ++ tailWord_2801395) baseStart_2801395 baseEnd_2801395 := by
    simpa [prefixWord, tailWord_2801395, baseEnd_2801395] using wordTrace_append hprefix tailTrace_2801395
  have hstable : (prefixWord ++ tailWord_2801395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801395).length < 2 ^ (prefixWord ++ tailWord_2801395).sum := by decide
  have hdescent : baseEnd_2801395 < baseStart_2801395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801412 : List Nat := [2, 3, 2, 2, 1, 3, 9]
def baseStart_2801412 : Nat := 118140960795 + 2801412 * 2 ^ 59
def prefixEnd_2801412 : Nat := 4983230072969 + 3 ^ 40 * 2801412 * 2
def baseEnd_2801412 : Nat := 35517799191933301144853

theorem tailTrace_2801412 : CollatzResearch.WordTrace tailWord_2801412 prefixEnd_2801412 35517799191933301144853 := by
  unfold tailWord_2801412
  simp only [CollatzResearch.WordTrace]
  refine ⟨51087944863485120961955245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68117259817980161282606993 51087944863485120961955245)
  ·
    refine ⟨19157979323806920360733217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51087944863485120961955245 19157979323806920360733217)
    ·
      refine ⟨14368484492855190270549913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19157979323806920360733217 14368484492855190270549913)
      ·
        refine ⟨10776363369641392702912435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14368484492855190270549913 10776363369641392702912435)
        ·
          refine ⟨16164545054462089054368653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10776363369641392702912435 16164545054462089054368653)
          ·
            refine ⟨6061704395423283395388245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16164545054462089054368653 6061704395423283395388245)
            ·
              refine ⟨35517799191933301144853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6061704395423283395388245 35517799191933301144853)
              ·
                rfl

theorem cell22_2801412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 9].length) (baseStart_2801412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801412 prefixEnd_2801412 := by exact prefixLift 2801412
  have htrace : WordTrace (prefixWord ++ tailWord_2801412) baseStart_2801412 baseEnd_2801412 := by
    simpa [prefixWord, tailWord_2801412, baseEnd_2801412] using wordTrace_append hprefix tailTrace_2801412
  have hstable : (prefixWord ++ tailWord_2801412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801412).length < 2 ^ (prefixWord ++ tailWord_2801412).sum := by decide
  have hdescent : baseEnd_2801412 < baseStart_2801412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801457 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 7]
def baseStart_2801457 : Nat := 118140960795 + 2801457 * 2 ^ 59
def prefixEnd_2801457 : Nat := 4983230072969 + 3 ^ 40 * 2801457 * 2
def baseEnd_2801457 : Nat := 319665327533944671178631

theorem tailTrace_2801457 : CollatzResearch.WordTrace tailWord_2801457 prefixEnd_2801457 319665327533944671178631 := by
  unfold tailWord_2801457
  simp only [CollatzResearch.WordTrace]
  refine ⟨102177531011807214609298625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68118354007871476406199083 102177531011807214609298625)
  ·
    refine ⟨76633148258855410956973969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102177531011807214609298625 76633148258855410956973969)
    ·
      refine ⟨57474861194141558217730477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76633148258855410956973969 57474861194141558217730477)
      ·
        refine ⟨21553072947803084331648929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57474861194141558217730477 21553072947803084331648929)
        ·
          refine ⟨16164804710852313248736697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21553072947803084331648929 16164804710852313248736697)
          ·
            refine ⟨12123603533139234936552523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16164804710852313248736697 12123603533139234936552523)
            ·
              refine ⟨18185405299708852404828785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12123603533139234936552523 18185405299708852404828785)
              ·
                refine ⟨13639053974781639303621589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18185405299708852404828785 13639053974781639303621589)
                ·
                  refine ⟨319665327533944671178631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13639053974781639303621589 319665327533944671178631)
                  ·
                    rfl

theorem cell22_2801457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 7].length) (baseStart_2801457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801457 prefixEnd_2801457 := by exact prefixLift 2801457
  have htrace : WordTrace (prefixWord ++ tailWord_2801457) baseStart_2801457 baseEnd_2801457 := by
    simpa [prefixWord, tailWord_2801457, baseEnd_2801457] using wordTrace_append hprefix tailTrace_2801457
  have hstable : (prefixWord ++ tailWord_2801457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801457).length < 2 ^ (prefixWord ++ tailWord_2801457).sum := by decide
  have hdescent : baseEnd_2801457 < baseStart_2801457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801504 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 3, 4]
def baseStart_2801504 : Nat := 118140960795 + 2801504 * 2 ^ 59
def prefixEnd_2801504 : Nat := 4983230072969 + 3 ^ 40 * 2801504 * 2
def baseEnd_2801504 : Nat := 959012071662341557610749

theorem tailTrace_2801504 : CollatzResearch.WordTrace tailWord_2801504 prefixEnd_2801504 959012071662341557610749 := by
  unfold tailWord_2801504
  simp only [CollatzResearch.WordTrace]
  refine ⟨51089622621318470818129783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68119496828424627757506377 51089622621318470818129783)
  ·
    refine ⟨76634433931977706227194675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51089622621318470818129783 76634433931977706227194675)
    ·
      refine ⟨114951650897966559340792013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76634433931977706227194675 114951650897966559340792013)
      ·
        refine ⟨43106869086737459752797005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114951650897966559340792013 43106869086737459752797005)
        ·
          refine ⟨16165075907526547407298877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43106869086737459752797005 16165075907526547407298877)
          ·
            refine ⟨6061903465322455277737079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16165075907526547407298877 6061903465322455277737079)
            ·
              refine ⟨9092855197983682916605619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6061903465322455277737079 9092855197983682916605619)
              ·
                refine ⟨13639282796975524374908429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9092855197983682916605619 13639282796975524374908429)
                ·
                  refine ⟨5114731048865821640590661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13639282796975524374908429 5114731048865821640590661)
                  ·
                    refine ⟨959012071662341557610749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5114731048865821640590661 959012071662341557610749)
                    ·
                      rfl

theorem cell22_2801504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_2801504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801504 prefixEnd_2801504 := by exact prefixLift 2801504
  have htrace : WordTrace (prefixWord ++ tailWord_2801504) baseStart_2801504 baseEnd_2801504 := by
    simpa [prefixWord, tailWord_2801504, baseEnd_2801504] using wordTrace_append hprefix tailTrace_2801504
  have hstable : (prefixWord ++ tailWord_2801504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801504).length < 2 ^ (prefixWord ++ tailWord_2801504).sum := by decide
  have hdescent : baseEnd_2801504 < baseStart_2801504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801521 : List Nat := [1, 2, 2, 2, 1, 3, 5, 1, 1, 4]
def baseStart_2801521 : Nat := 118140960795 + 2801521 * 2 ^ 59
def prefixEnd_2801521 : Nat := 4983230072969 + 3 ^ 40 * 2801521 * 2
def baseEnd_2801521 : Nat := 959017891109759179935697

theorem tailTrace_2801521 : CollatzResearch.WordTrace tailWord_2801521 prefixEnd_2801521 959017891109759179935697 := by
  unfold tailWord_2801521
  simp only [CollatzResearch.WordTrace]
  refine ⟨102179865283575353539628417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68119910189050235693085611 102179865283575353539628417)
  ·
    refine ⟨76634898962681515154721313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102179865283575353539628417 76634898962681515154721313)
    ·
      refine ⟨57476174222011136366040985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76634898962681515154721313 57476174222011136366040985)
      ·
        refine ⟨43107130666508352274530739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57476174222011136366040985 43107130666508352274530739)
        ·
          refine ⟨64660695999762528411796109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43107130666508352274530739 64660695999762528411796109)
          ·
            refine ⟨24247760999910948154423541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64660695999762528411796109 24247760999910948154423541)
            ·
              refine ⟨2273227593741651389477207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24247760999910948154423541 2273227593741651389477207)
              ·
                refine ⟨3409841390612477084215811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2273227593741651389477207 3409841390612477084215811)
                ·
                  refine ⟨5114762085918715626323717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3409841390612477084215811 5114762085918715626323717)
                  ·
                    refine ⟨959017891109759179935697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5114762085918715626323717 959017891109759179935697)
                    ·
                      rfl

theorem cell22_2801521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_2801521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801521 prefixEnd_2801521 := by exact prefixLift 2801521
  have htrace : WordTrace (prefixWord ++ tailWord_2801521) baseStart_2801521 baseEnd_2801521 := by
    simpa [prefixWord, tailWord_2801521, baseEnd_2801521] using wordTrace_append hprefix tailTrace_2801521
  have hstable : (prefixWord ++ tailWord_2801521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801521).length < 2 ^ (prefixWord ++ tailWord_2801521).sum := by decide
  have hdescent : baseEnd_2801521 < baseStart_2801521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801532 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 5, 6]
def baseStart_2801532 : Nat := 118140960795 + 2801532 * 2 ^ 59
def prefixEnd_2801532 : Nat := 4983230072969 + 3 ^ 40 * 2801532 * 2
def baseEnd_2801532 : Nat := 959021656634558817910663

theorem tailTrace_2801532 : CollatzResearch.WordTrace tailWord_2801532 prefixEnd_2801532 959021656634558817910663 := by
  unfold tailWord_2801532
  simp only [CollatzResearch.WordTrace]
  refine ⟨51090133243267751209139425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68120177657690334945519233 51090133243267751209139425)
  ·
    refine ⟨38317599932450813406854569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51090133243267751209139425 38317599932450813406854569)
    ·
      refine ⟨28738199949338110055140927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38317599932450813406854569 28738199949338110055140927)
      ·
        refine ⟨43107299924007165082711391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28738199949338110055140927 43107299924007165082711391)
        ·
          refine ⟨64660949886010747624067087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43107299924007165082711391 64660949886010747624067087)
          ·
            refine ⟨96991424829016121436100631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64660949886010747624067087 96991424829016121436100631)
            ·
              refine ⟨145487137243524182154150947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96991424829016121436100631 145487137243524182154150947)
              ·
                refine ⟨218230705865286273231226421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145487137243524182154150947 218230705865286273231226421)
                ·
                  refine ⟨20459128674870588115427477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218230705865286273231226421 20459128674870588115427477)
                  ·
                    refine ⟨959021656634558817910663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20459128674870588115427477 959021656634558817910663)
                    ·
                      rfl

theorem cell22_2801532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_2801532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801532 prefixEnd_2801532 := by exact prefixLift 2801532
  have htrace : WordTrace (prefixWord ++ tailWord_2801532) baseStart_2801532 baseEnd_2801532 := by
    simpa [prefixWord, tailWord_2801532, baseEnd_2801532] using wordTrace_append hprefix tailTrace_2801532
  have hstable : (prefixWord ++ tailWord_2801532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801532).length < 2 ^ (prefixWord ++ tailWord_2801532).sum := by decide
  have hdescent : baseEnd_2801532 < baseStart_2801532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801577 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 1, 8]
def baseStart_2801577 : Nat := 118140960795 + 2801577 * 2 ^ 59
def prefixEnd_2801577 : Nat := 4983230072969 + 3 ^ 40 * 2801577 * 2
def baseEnd_2801577 : Nat := 959037061054193700535525

theorem tailTrace_2801577 : CollatzResearch.WordTrace tailWord_2801577 prefixEnd_2801577 959037061054193700535525 := by
  unfold tailWord_2801577
  simp only [CollatzResearch.WordTrace]
  refine ⟨102181907771372475103666985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68121271847581650069111323 102181907771372475103666985)
  ·
    refine ⟨76636430828529356327750239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102181907771372475103666985 76636430828529356327750239)
    ·
      refine ⟨114954646242794034491625359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76636430828529356327750239 114954646242794034491625359)
      ·
        refine ⟨172431969364191051737438039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114954646242794034491625359 172431969364191051737438039)
        ·
          refine ⟨258647954046286577606157059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172431969364191051737438039 258647954046286577606157059)
          ·
            refine ⟨387971931069429866409235589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258647954046286577606157059 387971931069429866409235589)
            ·
              refine ⟨72744737075518099951731673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 387971931069429866409235589 72744737075518099951731673)
              ·
                refine ⟨54558552806638574963798755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72744737075518099951731673 54558552806638574963798755)
                ·
                  refine ⟨81837829209957862445698133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54558552806638574963798755 81837829209957862445698133)
                  ·
                    refine ⟨959037061054193700535525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81837829209957862445698133 959037061054193700535525)
                    ·
                      rfl

theorem cell22_2801577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_2801577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801577 prefixEnd_2801577 := by exact prefixLift 2801577
  have htrace : WordTrace (prefixWord ++ tailWord_2801577) baseStart_2801577 baseEnd_2801577 := by
    simpa [prefixWord, tailWord_2801577, baseEnd_2801577] using wordTrace_append hprefix tailTrace_2801577
  have hstable : (prefixWord ++ tailWord_2801577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801577).length < 2 ^ (prefixWord ++ tailWord_2801577).sum := by decide
  have hdescent : baseEnd_2801577 < baseStart_2801577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801701 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 2, 4]
def baseStart_2801701 : Nat := 118140960795 + 2801701 * 2 ^ 59
def prefixEnd_2801701 : Nat := 4983230072969 + 3 ^ 40 * 2801701 * 2
def baseEnd_2801701 : Nat := 959079508788298710435145

theorem tailTrace_2801701 : CollatzResearch.WordTrace tailWord_2801701 prefixEnd_2801701 959079508788298710435145 := by
  unfold tailWord_2801701
  simp only [CollatzResearch.WordTrace]
  refine ⟨102186430422923244281180957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68124286948615496187453971 102186430422923244281180957)
  ·
    refine ⟨38319911408596216605442859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102186430422923244281180957 38319911408596216605442859)
    ·
      refine ⟨57479867112894324908164289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38319911408596216605442859 57479867112894324908164289)
      ·
        refine ⟨43109900334670743681123217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57479867112894324908164289 43109900334670743681123217)
        ·
          refine ⟨32332425251003057760842413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43109900334670743681123217 32332425251003057760842413)
          ·
            refine ⟨12124659469126146660315905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32332425251003057760842413 12124659469126146660315905)
            ·
              refine ⟨9093494601844609995236929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12124659469126146660315905 9093494601844609995236929)
              ·
                refine ⟨6820120951383457496427697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9093494601844609995236929 6820120951383457496427697)
                ·
                  refine ⟨5115090713537593122320773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6820120951383457496427697 5115090713537593122320773)
                  ·
                    refine ⟨959079508788298710435145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5115090713537593122320773 959079508788298710435145)
                    ·
                      rfl

theorem cell22_2801701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_2801701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801701 prefixEnd_2801701 := by exact prefixLift 2801701
  have htrace : WordTrace (prefixWord ++ tailWord_2801701) baseStart_2801701 baseEnd_2801701 := by
    simpa [prefixWord, tailWord_2801701, baseEnd_2801701] using wordTrace_append hprefix tailTrace_2801701
  have hstable : (prefixWord ++ tailWord_2801701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801701).length < 2 ^ (prefixWord ++ tailWord_2801701).sum := by decide
  have hdescent : baseEnd_2801701 < baseStart_2801701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801765 : List Nat := [1, 3, 1, 3, 2, 2, 2, 4, 1, 3]
def baseStart_2801765 : Nat := 118140960795 + 2801765 * 2 ^ 59
def prefixEnd_2801765 : Nat := 4983230072969 + 3 ^ 40 * 2801765 * 2
def baseEnd_2801765 : Nat := 959101417296223876834949

theorem tailTrace_2801765 : CollatzResearch.WordTrace tailWord_2801765 prefixEnd_2801765 959101417296223876834949 := by
  unfold tailWord_2801765
  simp only [CollatzResearch.WordTrace]
  refine ⟨102188764694691383211510749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68125843129794255474340499 102188764694691383211510749)
  ·
    refine ⟨38320786760509268704316531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102188764694691383211510749 38320786760509268704316531)
    ·
      refine ⟨57481180140763903056474797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38320786760509268704316531 57481180140763903056474797)
      ·
        refine ⟨21555442552786463646178049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57481180140763903056474797 21555442552786463646178049)
        ·
          refine ⟨16166581914589847734633537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21555442552786463646178049 16166581914589847734633537)
          ·
            refine ⟨12124936435942385800975153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16166581914589847734633537 12124936435942385800975153)
            ·
              refine ⟨9093702326956789350731365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12124936435942385800975153 9093702326956789350731365)
              ·
                refine ⟨1705069186304398003262131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9093702326956789350731365 1705069186304398003262131)
                ·
                  refine ⟨2557603779456597004893197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705069186304398003262131 2557603779456597004893197)
                  ·
                    refine ⟨959101417296223876834949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2557603779456597004893197 959101417296223876834949)
                    ·
                      rfl

theorem cell22_2801765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_2801765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801765 prefixEnd_2801765 := by exact prefixLift 2801765
  have htrace : WordTrace (prefixWord ++ tailWord_2801765) baseStart_2801765 baseEnd_2801765 := by
    simpa [prefixWord, tailWord_2801765, baseEnd_2801765] using wordTrace_append hprefix tailTrace_2801765
  have hstable : (prefixWord ++ tailWord_2801765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801765).length < 2 ^ (prefixWord ++ tailWord_2801765).sum := by decide
  have hdescent : baseEnd_2801765 < baseStart_2801765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801776 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 2, 5]
def baseStart_2801776 : Nat := 118140960795 + 2801776 * 2 ^ 59
def prefixEnd_2801776 : Nat := 4983230072969 + 3 ^ 40 * 2801776 * 2
def baseEnd_2801776 : Nat := 959105182821023514809915

theorem tailTrace_2801776 : CollatzResearch.WordTrace tailWord_2801776 prefixEnd_2801776 959105182821023514809915 := by
  unfold tailWord_2801776
  simp only [CollatzResearch.WordTrace]
  refine ⟨51094582948825766045080591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68126110598434354726774121 51094582948825766045080591)
  ·
    refine ⟨76641874423238649067620887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51094582948825766045080591 76641874423238649067620887)
    ·
      refine ⟨114962811634857973601431331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76641874423238649067620887 114962811634857973601431331)
      ·
        refine ⟨172444217452286960402146997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114962811634857973601431331 172444217452286960402146997)
        ·
          refine ⟨16166645386151902537701281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172444217452286960402146997 16166645386151902537701281)
          ·
            refine ⟨12124984039613926903275961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16166645386151902537701281 12124984039613926903275961)
            ·
              refine ⟨9093738029710445177456971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12124984039613926903275961 9093738029710445177456971)
              ·
                refine ⟨13640607044565667766185457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9093738029710445177456971 13640607044565667766185457)
                ·
                  refine ⟨10230455283424250824639093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13640607044565667766185457 10230455283424250824639093)
                  ·
                    refine ⟨959105182821023514809915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10230455283424250824639093 959105182821023514809915)
                    ·
                      rfl

theorem cell22_2801776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_2801776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801776 prefixEnd_2801776 := by exact prefixLift 2801776
  have htrace : WordTrace (prefixWord ++ tailWord_2801776) baseStart_2801776 baseEnd_2801776 := by
    simpa [prefixWord, tailWord_2801776, baseEnd_2801776] using wordTrace_append hprefix tailTrace_2801776
  have hstable : (prefixWord ++ tailWord_2801776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801776).length < 2 ^ (prefixWord ++ tailWord_2801776).sum := by decide
  have hdescent : baseEnd_2801776 < baseStart_2801776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801823 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 6]
def baseStart_2801823 : Nat := 118140960795 + 2801823 * 2 ^ 59
def prefixEnd_2801823 : Nat := 4983230072969 + 3 ^ 40 * 2801823 * 2
def baseEnd_2801823 : Nat := 319707090627177019628257

theorem tailTrace_2801823 : CollatzResearch.WordTrace tailWord_2801823 prefixEnd_2801823 319707090627177019628257 := by
  unfold tailWord_2801823
  simp only [CollatzResearch.WordTrace]
  refine ⟨102190880128481259117122123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68127253418987506078081415 102190880128481259117122123)
  ·
    refine ⟨153286320192721888675683185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102190880128481259117122123 153286320192721888675683185)
    ·
      refine ⟨114964740144541416506762389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153286320192721888675683185 114964740144541416506762389)
      ·
        refine ⟨5388972194275378898754487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 114964740144541416506762389 5388972194275378898754487)
        ·
          refine ⟨8083458291413068348131731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5388972194275378898754487 8083458291413068348131731)
          ·
            refine ⟨12125187437119602522197597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8083458291413068348131731 12125187437119602522197597)
            ·
              refine ⟨4546945288919850945824099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12125187437119602522197597 4546945288919850945824099)
              ·
                refine ⟨6820417933379776418736149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546945288919850945824099 6820417933379776418736149)
                ·
                  refine ⟨319707090627177019628257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6820417933379776418736149 319707090627177019628257)
                  ·
                    rfl

theorem cell22_2801823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 6].length) (baseStart_2801823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801823 prefixEnd_2801823 := by exact prefixLift 2801823
  have htrace : WordTrace (prefixWord ++ tailWord_2801823) baseStart_2801823 baseEnd_2801823 := by
    simpa [prefixWord, tailWord_2801823, baseEnd_2801823] using wordTrace_append hprefix tailTrace_2801823
  have hstable : (prefixWord ++ tailWord_2801823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801823).length < 2 ^ (prefixWord ++ tailWord_2801823).sum := by decide
  have hdescent : baseEnd_2801823 < baseStart_2801823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801868 : List Nat := [2, 2, 1, 6, 1, 10]
def baseStart_2801868 : Nat := 118140960795 + 2801868 * 2 ^ 59
def prefixEnd_2801868 : Nat := 4983230072969 + 3 ^ 40 * 2801868 * 2
def baseEnd_2801868 : Nat := 11841193534582295574193

theorem tailTrace_2801868 : CollatzResearch.WordTrace tailWord_2801868 prefixEnd_2801868 11841193534582295574193 := by
  unfold tailWord_2801868
  simp only [CollatzResearch.WordTrace]
  refine ⟨51096260706659115901255129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68128347608878821201673505 51096260706659115901255129)
  ·
    refine ⟨38322195529994336925941347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51096260706659115901255129 38322195529994336925941347)
    ·
      refine ⟨57483293294991505388912021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38322195529994336925941347 57483293294991505388912021)
      ·
        refine ⟨2694529373202726815105251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57483293294991505388912021 2694529373202726815105251)
        ·
          refine ⟨4041794059804090222657877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694529373202726815105251 4041794059804090222657877)
          ·
            refine ⟨11841193534582295574193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4041794059804090222657877 11841193534582295574193)
            ·
              rfl

theorem cell22_2801868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 10].length) (baseStart_2801868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801868 prefixEnd_2801868 := by exact prefixLift 2801868
  have htrace : WordTrace (prefixWord ++ tailWord_2801868) baseStart_2801868 baseEnd_2801868 := by
    simpa [prefixWord, tailWord_2801868, baseEnd_2801868] using wordTrace_append hprefix tailTrace_2801868
  have hstable : (prefixWord ++ tailWord_2801868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801868).length < 2 ^ (prefixWord ++ tailWord_2801868).sum := by decide
  have hdescent : baseEnd_2801868 < baseStart_2801868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801881 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 2, 6]
def baseStart_2801881 : Nat := 118140960795 + 2801881 * 2 ^ 59
def prefixEnd_2801881 : Nat := 4983230072969 + 3 ^ 40 * 2801881 * 2
def baseEnd_2801881 : Nat := 959141126466838240934593

theorem tailTrace_2801881 : CollatzResearch.WordTrace tailWord_2801881 prefixEnd_2801881 959141126466838240934593 := by
  unfold tailWord_2801881
  simp only [CollatzResearch.WordTrace]
  refine ⟨102192995562271135022733497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68128663708180756681822331 102192995562271135022733497)
  ·
    refine ⟨76644746671703351267050123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102192995562271135022733497 76644746671703351267050123)
    ·
      refine ⟨114967120007555026900575185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76644746671703351267050123 114967120007555026900575185)
      ·
        refine ⟨86225340005666270175431389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114967120007555026900575185 86225340005666270175431389)
        ·
          refine ⟨32334502502124851315786771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86225340005666270175431389 32334502502124851315786771)
          ·
            refine ⟨48501753753187276973680157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32334502502124851315786771 48501753753187276973680157)
            ·
              refine ⟨18188157657445228865130059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48501753753187276973680157 18188157657445228865130059)
              ·
                refine ⟨27282236486167843297695089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18188157657445228865130059 27282236486167843297695089)
                ·
                  refine ⟨20461677364625882473271317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27282236486167843297695089 20461677364625882473271317)
                  ·
                    refine ⟨959141126466838240934593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20461677364625882473271317 959141126466838240934593)
                    ·
                      rfl

theorem cell22_2801881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_2801881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801881 prefixEnd_2801881 := by exact prefixLift 2801881
  have htrace : WordTrace (prefixWord ++ tailWord_2801881) baseStart_2801881 baseEnd_2801881 := by
    simpa [prefixWord, tailWord_2801881, baseEnd_2801881] using wordTrace_append hprefix tailTrace_2801881
  have hstable : (prefixWord ++ tailWord_2801881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801881).length < 2 ^ (prefixWord ++ tailWord_2801881).sum := by decide
  have hdescent : baseEnd_2801881 < baseStart_2801881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801885 : List Nat := [1, 4, 3, 2, 1, 3, 1, 7]
def baseStart_2801885 : Nat := 118140960795 + 2801885 * 2 ^ 59
def prefixEnd_2801885 : Nat := 4983230072969 + 3 ^ 40 * 2801885 * 2
def baseEnd_2801885 : Nat := 106571388416509284870509

theorem tailTrace_2801885 : CollatzResearch.WordTrace tailWord_2801885 prefixEnd_2801885 106571388416509284870509 := by
  unfold tailWord_2801885
  simp only [CollatzResearch.WordTrace]
  refine ⟨102193141454256643705879109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68128760969504429137252739 102193141454256643705879109)
  ·
    refine ⟨19161214022673120694852333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102193141454256643705879109 19161214022673120694852333)
    ·
      refine ⟨7185455258502420260569625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19161214022673120694852333 7185455258502420260569625)
      ·
        refine ⟨5389091443876815195427219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7185455258502420260569625 5389091443876815195427219)
        ·
          refine ⟨8083637165815222793140829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5389091443876815195427219 8083637165815222793140829)
          ·
            refine ⟨3031363937180708547427811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8083637165815222793140829 3031363937180708547427811)
            ·
              refine ⟨4547045905771062821141717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3031363937180708547427811 4547045905771062821141717)
              ·
                refine ⟨106571388416509284870509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4547045905771062821141717 106571388416509284870509)
                ·
                  rfl

theorem cell22_2801885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 7].length) (baseStart_2801885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801885 prefixEnd_2801885 := by exact prefixLift 2801885
  have htrace : WordTrace (prefixWord ++ tailWord_2801885) baseStart_2801885 baseEnd_2801885 := by
    simpa [prefixWord, tailWord_2801885, baseEnd_2801885] using wordTrace_append hprefix tailTrace_2801885
  have hstable : (prefixWord ++ tailWord_2801885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801885).length < 2 ^ (prefixWord ++ tailWord_2801885).sum := by decide
  have hdescent : baseEnd_2801885 < baseStart_2801885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801911 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 6, 5]
def baseStart_2801911 : Nat := 118140960795 + 2801911 * 2 ^ 59
def prefixEnd_2801911 : Nat := 4983230072969 + 3 ^ 40 * 2801911 * 2
def baseEnd_2801911 : Nat := 959151396079928162684501

theorem tailTrace_2801911 : CollatzResearch.WordTrace tailWord_2801911 prefixEnd_2801911 959151396079928162684501 := by
  unfold tailWord_2801911
  simp only [CollatzResearch.WordTrace]
  refine ⟨102194089752162450146325587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68129393168108300097550391 102194089752162450146325587)
  ·
    refine ⟨153291134628243675219488381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102194089752162450146325587 153291134628243675219488381)
    ·
      refine ⟨57484175485591378207308143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153291134628243675219488381 57484175485591378207308143)
      ·
        refine ⟨86226263228387067310962215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57484175485591378207308143 86226263228387067310962215)
        ·
          refine ⟨129339394842580600966443323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86226263228387067310962215 129339394842580600966443323)
          ·
            refine ⟨194009092263870901449664985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129339394842580600966443323 194009092263870901449664985)
            ·
              refine ⟨145506819197903176087248739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194009092263870901449664985 145506819197903176087248739)
              ·
                refine ⟨218260228796854764130873109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145506819197903176087248739 218260228796854764130873109)
                ·
                  refine ⟨10230948224852567068634677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 218260228796854764130873109 10230948224852567068634677)
                  ·
                    refine ⟨959151396079928162684501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10230948224852567068634677 959151396079928162684501)
                    ·
                      rfl

theorem cell22_2801911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_2801911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801911 prefixEnd_2801911 := by exact prefixLift 2801911
  have htrace : WordTrace (prefixWord ++ tailWord_2801911) baseStart_2801911 baseEnd_2801911 := by
    simpa [prefixWord, tailWord_2801911, baseEnd_2801911] using wordTrace_append hprefix tailTrace_2801911
  have hstable : (prefixWord ++ tailWord_2801911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801911).length < 2 ^ (prefixWord ++ tailWord_2801911).sum := by decide
  have hdescent : baseEnd_2801911 < baseStart_2801911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801928 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 2, 5]
def baseStart_2801928 : Nat := 118140960795 + 2801928 * 2 ^ 59
def prefixEnd_2801928 : Nat := 4983230072969 + 3 ^ 40 * 2801928 * 2
def baseEnd_2801928 : Nat := 959157215527345785009449

theorem tailTrace_2801928 : CollatzResearch.WordTrace tailWord_2801928 prefixEnd_2801928 959157215527345785009449 := by
  unfold tailWord_2801928
  simp only [CollatzResearch.WordTrace]
  refine ⟨51097354896550431024847219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68129806528733908033129625 51097354896550431024847219)
  ·
    refine ⟨76646032344825646537270829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51097354896550431024847219 76646032344825646537270829)
    ·
      refine ⟨28742262129309617451476561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76646032344825646537270829 28742262129309617451476561)
      ·
        refine ⟨21556696596982213088607421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28742262129309617451476561 21556696596982213088607421)
        ·
          refine ⟨8083761223868329908227783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21556696596982213088607421 8083761223868329908227783)
          ·
            refine ⟨12125641835802494862341675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8083761223868329908227783 12125641835802494862341675)
            ·
              refine ⟨18188462753703742293512513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12125641835802494862341675 18188462753703742293512513)
              ·
                refine ⟨13641347065277806720134385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18188462753703742293512513 13641347065277806720134385)
                ·
                  refine ⟨10231010298958355040100789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13641347065277806720134385 10231010298958355040100789)
                  ·
                    refine ⟨959157215527345785009449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10231010298958355040100789 959157215527345785009449)
                    ·
                      rfl

theorem cell22_2801928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_2801928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801928 prefixEnd_2801928 := by exact prefixLift 2801928
  have htrace : WordTrace (prefixWord ++ tailWord_2801928) baseStart_2801928 baseEnd_2801928 := by
    simpa [prefixWord, tailWord_2801928, baseEnd_2801928] using wordTrace_append hprefix tailTrace_2801928
  have hstable : (prefixWord ++ tailWord_2801928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801928).length < 2 ^ (prefixWord ++ tailWord_2801928).sum := by decide
  have hdescent : baseEnd_2801928 < baseStart_2801928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2801973 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 3, 5]
def baseStart_2801973 : Nat := 118140960795 + 2801973 * 2 ^ 59
def prefixEnd_2801973 : Nat := 4983230072969 + 3 ^ 40 * 2801973 * 2
def baseEnd_2801973 : Nat := 959172619946980667634311

theorem tailTrace_2801973 : CollatzResearch.WordTrace tailWord_2801973 prefixEnd_2801973 959172619946980667634311 := by
  unfold tailWord_2801973
  simp only [CollatzResearch.WordTrace]
  refine ⟨102196351077937834735082573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68130900718625223156721715 102196351077937834735082573)
  ·
    refine ⟨38323631654226688025655965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102196351077937834735082573 38323631654226688025655965)
    ·
      refine ⟨14371361870335008009620987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38323631654226688025655965 14371361870335008009620987)
      ·
        refine ⟨21557042805502512014431481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14371361870335008009620987 21557042805502512014431481)
        ·
          refine ⟨16167782104126884010823611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21557042805502512014431481 16167782104126884010823611)
          ·
            refine ⟨24251673156190326016235417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16167782104126884010823611 24251673156190326016235417)
            ·
              refine ⟨18188754867142744512176563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24251673156190326016235417 18188754867142744512176563)
              ·
                refine ⟨27283132300714116768264845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18188754867142744512176563 27283132300714116768264845)
                ·
                  refine ⟨10231174612767793788099317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27283132300714116768264845 10231174612767793788099317)
                  ·
                    refine ⟨959172619946980667634311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10231174612767793788099317 959172619946980667634311)
                    ·
                      rfl

theorem cell22_2801973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_2801973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2801973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2801973 prefixEnd_2801973 := by exact prefixLift 2801973
  have htrace : WordTrace (prefixWord ++ tailWord_2801973) baseStart_2801973 baseEnd_2801973 := by
    simpa [prefixWord, tailWord_2801973, baseEnd_2801973] using wordTrace_append hprefix tailTrace_2801973
  have hstable : (prefixWord ++ tailWord_2801973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2801973).length < 2 ^ (prefixWord ++ tailWord_2801973).sum := by decide
  have hdescent : baseEnd_2801973 < baseStart_2801973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2801973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802110 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 6]
def baseStart_2802110 : Nat := 118140960795 + 2802110 * 2 ^ 59
def prefixEnd_2802110 : Nat := 4983230072969 + 3 ^ 40 * 2802110 * 2
def baseEnd_2802110 : Nat := 319739839282252658986297

theorem tailTrace_2802110 : CollatzResearch.WordTrace tailWord_2802110 prefixEnd_2802110 319739839282252658986297 := by
  unfold tailWord_2802110
  simp only [CollatzResearch.WordTrace]
  refine ⟨12775168484805188391602473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68134231918961004755213189 12775168484805188391602473)
  ·
    refine ⟨9581376363603891293701855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12775168484805188391602473 9581376363603891293701855)
    ·
      refine ⟨14372064545405836940552783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9581376363603891293701855 14372064545405836940552783)
      ·
        refine ⟨21558096818108755410829175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14372064545405836940552783 21558096818108755410829175)
        ·
          refine ⟨32337145227163133116243763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21558096818108755410829175 32337145227163133116243763)
          ·
            refine ⟨48505717840744699674365645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32337145227163133116243763 48505717840744699674365645)
            ·
              refine ⟨18189644190279262377887117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48505717840744699674365645 18189644190279262377887117)
              ·
                refine ⟨6821116571354723391707669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18189644190279262377887117 6821116571354723391707669)
                ·
                  refine ⟨319739839282252658986297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6821116571354723391707669 319739839282252658986297)
                  ·
                    rfl

theorem cell22_2802110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_2802110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802110 prefixEnd_2802110 := by exact prefixLift 2802110
  have htrace : WordTrace (prefixWord ++ tailWord_2802110) baseStart_2802110 baseEnd_2802110 := by
    simpa [prefixWord, tailWord_2802110, baseEnd_2802110] using wordTrace_append hprefix tailTrace_2802110
  have hstable : (prefixWord ++ tailWord_2802110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802110).length < 2 ^ (prefixWord ++ tailWord_2802110).sum := by decide
  have hdescent : baseEnd_2802110 < baseStart_2802110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802157 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_2802157 : Nat := 118140960795 + 2802157 * 2 ^ 59
def prefixEnd_2802157 : Nat := 4983230072969 + 3 ^ 40 * 2802157 * 2
def baseEnd_2802157 : Nat := 959235606907265521033747

theorem tailTrace_2802157 : CollatzResearch.WordTrace tailWord_2802157 prefixEnd_2802157 959235606907265521033747 := by
  unfold tailWord_2802157
  simp only [CollatzResearch.WordTrace]
  refine ⟨102203062109271234159780725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68135374739514156106520483 102203062109271234159780725)
  ·
    refine ⟨9581537072744178202479443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102203062109271234159780725 9581537072744178202479443)
    ·
      refine ⟨14372305609116267303719165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9581537072744178202479443 14372305609116267303719165)
      ·
        refine ⟨5389614603418600238894687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14372305609116267303719165 5389614603418600238894687)
        ·
          refine ⟨8084421905127900358342031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5389614603418600238894687 8084421905127900358342031)
          ·
            refine ⟨12126632857691850537513047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8084421905127900358342031 12126632857691850537513047)
            ·
              refine ⟨18189949286537775806269571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12126632857691850537513047 18189949286537775806269571)
              ·
                refine ⟨27284923929806663709404357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18189949286537775806269571 27284923929806663709404357)
                ·
                  refine ⟨5115923236838749445513317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27284923929806663709404357 5115923236838749445513317)
                  ·
                    refine ⟨959235606907265521033747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5115923236838749445513317 959235606907265521033747)
                    ·
                      rfl

theorem cell22_2802157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_2802157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802157 prefixEnd_2802157 := by exact prefixLift 2802157
  have htrace : WordTrace (prefixWord ++ tailWord_2802157) baseStart_2802157 baseEnd_2802157 := by
    simpa [prefixWord, tailWord_2802157, baseEnd_2802157] using wordTrace_append hprefix tailTrace_2802157
  have hstable : (prefixWord ++ tailWord_2802157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802157).length < 2 ^ (prefixWord ++ tailWord_2802157).sum := by decide
  have hdescent : baseEnd_2802157 < baseStart_2802157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802189 : List Nat := [1, 7, 1, 1, 1, 1, 2, 8]
def baseStart_2802189 : Nat := 118140960795 + 2802189 * 2 ^ 59
def prefixEnd_2802189 : Nat := 4983230072969 + 3 ^ 40 * 2802189 * 2
def baseEnd_2802189 : Nat := 106582951240136456025961

theorem tailTrace_2802189 : CollatzResearch.WordTrace tailWord_2802189 prefixEnd_2802189 106582951240136456025961 := by
  unfold tailWord_2802189
  simp only [CollatzResearch.WordTrace]
  refine ⟨102204229245155303624945621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68136152830103535749963747 102204229245155303624945621)
  ·
    refine ⟨2395411622933327428709663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 102204229245155303624945621 2395411622933327428709663)
    ·
      refine ⟨3593117434399991143064495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2395411622933327428709663 3593117434399991143064495)
      ·
        refine ⟨5389676151599986714596743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3593117434399991143064495 5389676151599986714596743)
        ·
          refine ⟨8084514227399980071895115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5389676151599986714596743 8084514227399980071895115)
          ·
            refine ⟨12126771341099970107842673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8084514227399980071895115 12126771341099970107842673)
            ·
              refine ⟨9095078505824977580882005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12126771341099970107842673 9095078505824977580882005)
              ·
                refine ⟨106582951240136456025961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9095078505824977580882005 106582951240136456025961)
                ·
                  rfl

theorem cell22_2802189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 8].length) (baseStart_2802189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802189 prefixEnd_2802189 := by exact prefixLift 2802189
  have htrace : WordTrace (prefixWord ++ tailWord_2802189) baseStart_2802189 baseEnd_2802189 := by
    simpa [prefixWord, tailWord_2802189, baseEnd_2802189] using wordTrace_append hprefix tailTrace_2802189
  have hstable : (prefixWord ++ tailWord_2802189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802189).length < 2 ^ (prefixWord ++ tailWord_2802189).sum := by decide
  have hdescent : baseEnd_2802189 < baseStart_2802189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802245 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 8]
def baseStart_2802245 : Nat := 118140960795 + 2802245 * 2 ^ 59
def prefixEnd_2802245 : Nat := 4983230072969 + 3 ^ 40 * 2802245 * 2
def baseEnd_2802245 : Nat := 319755243701887541611159

theorem tailTrace_2802245 : CollatzResearch.WordTrace tailWord_2802245 prefixEnd_2802245 319755243701887541611159 := by
  unfold tailWord_2802245
  simp only [CollatzResearch.WordTrace]
  refine ⟨102206271732952425188984189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68137514488634950125989459 102206271732952425188984189)
  ·
    refine ⟨38327351899857159445869071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102206271732952425188984189 38327351899857159445869071)
    ·
      refine ⟨57491027849785739168803607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38327351899857159445869071 57491027849785739168803607)
      ·
        refine ⟨86236541774678608753205411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57491027849785739168803607 86236541774678608753205411)
        ·
          refine ⟨129354812662017913129808117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86236541774678608753205411 129354812662017913129808117)
          ·
            refine ⟨12127013687064179355919511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129354812662017913129808117 12127013687064179355919511)
            ·
              refine ⟨18190520530596269033879267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12127013687064179355919511 18190520530596269033879267)
              ·
                refine ⟨27285780795894403550818901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18190520530596269033879267 27285780795894403550818901)
                ·
                  refine ⟨319755243701887541611159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27285780795894403550818901 319755243701887541611159)
                  ·
                    rfl

theorem cell22_2802245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_2802245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802245 prefixEnd_2802245 := by exact prefixLift 2802245
  have htrace : WordTrace (prefixWord ++ tailWord_2802245) baseStart_2802245 baseEnd_2802245 := by
    simpa [prefixWord, tailWord_2802245, baseEnd_2802245] using wordTrace_append hprefix tailTrace_2802245
  have hstable : (prefixWord ++ tailWord_2802245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802245).length < 2 ^ (prefixWord ++ tailWord_2802245).sum := by decide
  have hdescent : baseEnd_2802245 < baseStart_2802245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802247 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 3, 4]
def baseStart_2802247 : Nat := 118140960795 + 2802247 * 2 ^ 59
def prefixEnd_2802247 : Nat := 4983230072969 + 3 ^ 40 * 2802247 * 2
def baseEnd_2802247 : Nat := 959266415746535286283471

theorem tailTrace_2802247 : CollatzResearch.WordTrace tailWord_2802247 prefixEnd_2802247 959266415746535286283471 := by
  unfold tailWord_2802247
  simp only [CollatzResearch.WordTrace]
  refine ⟨102206344678945179530556995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68137563119296786353704663 102206344678945179530556995)
  ·
    refine ⟨153309517018417769295835493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102206344678945179530556995 153309517018417769295835493)
    ·
      refine ⟨28745534440953331742969155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153309517018417769295835493 28745534440953331742969155)
      ·
        refine ⟨43118301661429997614453733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28745534440953331742969155 43118301661429997614453733)
        ·
          refine ⟨8084681561518124552710075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43118301661429997614453733 8084681561518124552710075)
          ·
            refine ⟨12127022342277186829065113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8084681561518124552710075 12127022342277186829065113)
            ·
              refine ⟨9095266756707890121798835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12127022342277186829065113 9095266756707890121798835)
              ·
                refine ⟨13642900135061835182698253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9095266756707890121798835 13642900135061835182698253)
                ·
                  refine ⟨5116087550648188193511845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13642900135061835182698253 5116087550648188193511845)
                  ·
                    refine ⟨959266415746535286283471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5116087550648188193511845 959266415746535286283471)
                    ·
                      rfl

theorem cell22_2802247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_2802247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802247 prefixEnd_2802247 := by exact prefixLift 2802247
  have htrace : WordTrace (prefixWord ++ tailWord_2802247) baseStart_2802247 baseEnd_2802247 := by
    simpa [prefixWord, tailWord_2802247, baseEnd_2802247] using wordTrace_append hprefix tailTrace_2802247
  have hstable : (prefixWord ++ tailWord_2802247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802247).length < 2 ^ (prefixWord ++ tailWord_2802247).sum := by decide
  have hdescent : baseEnd_2802247 < baseStart_2802247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802264 : List Nat := [2, 1, 2, 2, 1, 2, 6, 1, 1, 4]
def baseStart_2802264 : Nat := 118140960795 + 2802264 * 2 ^ 59
def prefixEnd_2802264 : Nat := 4983230072969 + 3 ^ 40 * 2802264 * 2
def baseEnd_2802264 : Nat := 959272235193952908608419

theorem tailTrace_2802264 : CollatzResearch.WordTrace tailWord_2802264 prefixEnd_2802264 959272235193952908608419 := by
  unfold tailWord_2802264
  simp only [CollatzResearch.WordTrace]
  refine ⟨51103482359941795716962923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68137976479922394289283897 51103482359941795716962923)
  ·
    refine ⟨76655223539912693575444385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51103482359941795716962923 76655223539912693575444385)
    ·
      refine ⟨57491417654934520181583289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76655223539912693575444385 57491417654934520181583289)
      ·
        refine ⟨43118563241200890136187467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57491417654934520181583289 43118563241200890136187467)
        ·
          refine ⟨64677844861801335204281201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43118563241200890136187467 64677844861801335204281201)
          ·
            refine ⟨48508383646351001403210901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64677844861801335204281201 48508383646351001403210901)
            ·
              refine ⟨2273830483422703190775511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48508383646351001403210901 2273830483422703190775511)
              ·
                refine ⟨3410745725134054786163267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2273830483422703190775511 3410745725134054786163267)
                ·
                  refine ⟨5116118587701082179244901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3410745725134054786163267 5116118587701082179244901)
                  ·
                    refine ⟨959272235193952908608419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5116118587701082179244901 959272235193952908608419)
                    ·
                      rfl

theorem cell22_2802264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_2802264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802264 prefixEnd_2802264 := by exact prefixLift 2802264
  have htrace : WordTrace (prefixWord ++ tailWord_2802264) baseStart_2802264 baseEnd_2802264 := by
    simpa [prefixWord, tailWord_2802264, baseEnd_2802264] using wordTrace_append hprefix tailTrace_2802264
  have hstable : (prefixWord ++ tailWord_2802264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802264).length < 2 ^ (prefixWord ++ tailWord_2802264).sum := by decide
  have hdescent : baseEnd_2802264 < baseStart_2802264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802307 : List Nat := [1, 1, 1, 3, 3, 1, 6, 6]
def baseStart_2802307 : Nat := 118140960795 + 2802307 * 2 ^ 59
def prefixEnd_2802307 : Nat := 4983230072969 + 3 ^ 40 * 2802307 * 2
def baseEnd_2802307 : Nat := 106587439441412792198143

theorem tailTrace_2802307 : CollatzResearch.WordTrace tailWord_2802307 prefixEnd_2802307 106587439441412792198143 := by
  unfold tailWord_2802307
  simp only [CollatzResearch.WordTrace]
  refine ⟨102208533058727809777741175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68139022039151873185160783 102208533058727809777741175)
  ·
    refine ⟨153312799588091714666611763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102208533058727809777741175 153312799588091714666611763)
    ·
      refine ⟨229969199382137571999917645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153312799588091714666611763 229969199382137571999917645)
      ·
        refine ⟨86238449768301589499969117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229969199382137571999917645 86238449768301589499969117)
        ·
          refine ⟨32339418663113096062488419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86238449768301589499969117 32339418663113096062488419)
          ·
            refine ⟨48509127994669644093732629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32339418663113096062488419 48509127994669644093732629)
            ·
              refine ⟨2273865374750139566893717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48509127994669644093732629 2273865374750139566893717)
              ·
                refine ⟨106587439441412792198143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2273865374750139566893717 106587439441412792198143)
                ·
                  rfl

theorem cell22_2802307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 6].length) (baseStart_2802307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802307 prefixEnd_2802307 := by exact prefixLift 2802307
  have htrace : WordTrace (prefixWord ++ tailWord_2802307) baseStart_2802307 baseEnd_2802307 := by
    simpa [prefixWord, tailWord_2802307, baseEnd_2802307] using wordTrace_append hprefix tailTrace_2802307
  have hstable : (prefixWord ++ tailWord_2802307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802307).length < 2 ^ (prefixWord ++ tailWord_2802307).sum := by decide
  have hdescent : baseEnd_2802307 < baseStart_2802307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802320 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 3, 8]
def baseStart_2802320 : Nat := 118140960795 + 2802320 * 2 ^ 59
def prefixEnd_2802320 : Nat := 4983230072969 + 3 ^ 40 * 2802320 * 2
def baseEnd_2802320 : Nat := 959291405138387429208247

theorem tailTrace_2802320 : CollatzResearch.WordTrace tailWord_2802320 prefixEnd_2802320 959291405138387429208247 := by
  unfold tailWord_2802320
  simp only [CollatzResearch.WordTrace]
  refine ⟨51104503603840356498982207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68139338138453808665309609 51104503603840356498982207)
  ·
    refine ⟨76656755405760534748473311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51104503603840356498982207 76656755405760534748473311)
    ·
      refine ⟨114985133108640802122709967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76656755405760534748473311 114985133108640802122709967)
      ·
        refine ⟨172477699662961203184064951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114985133108640802122709967 172477699662961203184064951)
        ·
          refine ⟨258716549494441804776097427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172477699662961203184064951 258716549494441804776097427)
          ·
            refine ⟨388074824241662707164146141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258716549494441804776097427 388074824241662707164146141)
            ·
              refine ⟨145528059090623515186554803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 388074824241662707164146141 145528059090623515186554803)
              ·
                refine ⟨218292088635935272779832205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145528059090623515186554803 218292088635935272779832205)
                ·
                  refine ⟨81859533238475727292437077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218292088635935272779832205 81859533238475727292437077)
                  ·
                    refine ⟨959291405138387429208247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81859533238475727292437077 959291405138387429208247)
                    ·
                      rfl

theorem cell22_2802320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_2802320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802320 prefixEnd_2802320 := by exact prefixLift 2802320
  have htrace : WordTrace (prefixWord ++ tailWord_2802320) baseStart_2802320 baseEnd_2802320 := by
    simpa [prefixWord, tailWord_2802320, baseEnd_2802320] using wordTrace_append hprefix tailTrace_2802320
  have hstable : (prefixWord ++ tailWord_2802320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802320).length < 2 ^ (prefixWord ++ tailWord_2802320).sum := by decide
  have hdescent : baseEnd_2802320 < baseStart_2802320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802324 : List Nat := [2, 4, 2, 2, 1, 3, 8]
def baseStart_2802324 : Nat := 118140960795 + 2802324 * 2 ^ 59
def prefixEnd_2802324 : Nat := 4983230072969 + 3 ^ 40 * 2802324 * 2
def baseEnd_2802324 : Nat := 35529362015560472300305

theorem tailTrace_2802324 : CollatzResearch.WordTrace tailWord_2802324 prefixEnd_2802324 35529362015560472300305 := by
  unfold tailWord_2802324
  simp only [CollatzResearch.WordTrace]
  refine ⟨51104576549833110840555013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68139435399777481120740017 51104576549833110840555013)
  ·
    refine ⟨9582108103093708282604065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51104576549833110840555013 9582108103093708282604065)
    ·
      refine ⟨7186581077320281211953049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9582108103093708282604065 7186581077320281211953049)
      ·
        refine ⟨5389935807990210908964787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7186581077320281211953049 5389935807990210908964787)
        ·
          refine ⟨8084903711985316363447181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5389935807990210908964787 8084903711985316363447181)
          ·
            refine ⟨3031838891994493636292693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8084903711985316363447181 3031838891994493636292693)
            ·
              refine ⟨35529362015560472300305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3031838891994493636292693 35529362015560472300305)
              ·
                rfl

theorem cell22_2802324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 8].length) (baseStart_2802324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802324 prefixEnd_2802324 := by exact prefixLift 2802324
  have htrace : WordTrace (prefixWord ++ tailWord_2802324) baseStart_2802324 baseEnd_2802324 := by
    simpa [prefixWord, tailWord_2802324, baseEnd_2802324] using wordTrace_append hprefix tailTrace_2802324
  have hstable : (prefixWord ++ tailWord_2802324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802324).length < 2 ^ (prefixWord ++ tailWord_2802324).sum := by decide
  have hdescent : baseEnd_2802324 < baseStart_2802324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802386 : List Nat := [3, 2, 2, 2, 3, 1, 2, 2, 5]
def baseStart_2802386 : Nat := 118140960795 + 2802386 * 2 ^ 59
def prefixEnd_2802386 : Nat := 4983230072969 + 3 ^ 40 * 2802386 * 2
def baseEnd_2802386 : Nat := 319771332762395085686015

theorem tailTrace_2802386 : CollatzResearch.WordTrace tailWord_2802386 prefixEnd_2802386 319771332762395085686015 := by
  unfold tailWord_2802386
  simp only [CollatzResearch.WordTrace]
  refine ⟨25552853606360401567466753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68140942950294404179911341 25552853606360401567466753)
  ·
    refine ⟨19164640204770301175600065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25552853606360401567466753 19164640204770301175600065)
    ·
      refine ⟨14373480153577725881700049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19164640204770301175600065 14373480153577725881700049)
      ·
        refine ⟨10780110115183294411275037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14373480153577725881700049 10780110115183294411275037)
        ·
          refine ⟨4042541293193735404228139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10780110115183294411275037 4042541293193735404228139)
          ·
            refine ⟨6063811939790603106342209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4042541293193735404228139 6063811939790603106342209)
            ·
              refine ⟨4547858954842952329756657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6063811939790603106342209 4547858954842952329756657)
              ·
                refine ⟨3410894216132214247317493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4547858954842952329756657 3410894216132214247317493)
                ·
                  refine ⟨319771332762395085686015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3410894216132214247317493 319771332762395085686015)
                  ·
                    rfl

theorem cell22_2802386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_2802386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802386 prefixEnd_2802386 := by exact prefixLift 2802386
  have htrace : WordTrace (prefixWord ++ tailWord_2802386) baseStart_2802386 baseEnd_2802386 := by
    simpa [prefixWord, tailWord_2802386, baseEnd_2802386] using wordTrace_append hprefix tailTrace_2802386
  have hstable : (prefixWord ++ tailWord_2802386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802386).length < 2 ^ (prefixWord ++ tailWord_2802386).sum := by decide
  have hdescent : baseEnd_2802386 < baseStart_2802386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802414 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 6]
def baseStart_2802414 : Nat := 118140960795 + 2802414 * 2 ^ 59
def prefixEnd_2802414 : Nat := 4983230072969 + 3 ^ 40 * 2802414 * 2
def baseEnd_2802414 : Nat := 319774527753134172452653

theorem tailTrace_2802414 : CollatzResearch.WordTrace tailWord_2802414 prefixEnd_2802414 319774527753134172452653 := by
  unfold tailWord_2802414
  simp only [CollatzResearch.WordTrace]
  refine ⟨12776554458667520881485787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68141623779560111367924197 12776554458667520881485787)
  ·
    refine ⟨19164831688001281322228681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12776554458667520881485787 19164831688001281322228681)
    ·
      refine ⟨14373623766000960991671511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19164831688001281322228681 14373623766000960991671511)
      ·
        refine ⟨21560435649001441487507267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14373623766000960991671511 21560435649001441487507267)
        ·
          refine ⟨32340653473502162231260901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21560435649001441487507267 32340653473502162231260901)
          ·
            refine ⟨6063872526281655418361419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32340653473502162231260901 6063872526281655418361419)
            ·
              refine ⟨9095808789422483127542129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6063872526281655418361419 9095808789422483127542129)
              ·
                refine ⟨6821856592066862345656597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9095808789422483127542129 6821856592066862345656597)
                ·
                  refine ⟨319774527753134172452653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6821856592066862345656597 319774527753134172452653)
                  ·
                    rfl

theorem cell22_2802414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_2802414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802414 prefixEnd_2802414 := by exact prefixLift 2802414
  have htrace : WordTrace (prefixWord ++ tailWord_2802414) baseStart_2802414 baseEnd_2802414 := by
    simpa [prefixWord, tailWord_2802414, baseEnd_2802414] using wordTrace_append hprefix tailTrace_2802414
  have hstable : (prefixWord ++ tailWord_2802414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802414).length < 2 ^ (prefixWord ++ tailWord_2802414).sum := by decide
  have hdescent : baseEnd_2802414 < baseStart_2802414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802429 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 4, 3]
def baseStart_2802429 : Nat := 118140960795 + 2802429 * 2 ^ 59
def prefixEnd_2802429 : Nat := 4983230072969 + 3 ^ 40 * 2802429 * 2
def baseEnd_2802429 : Nat := 959328718065947478232913

theorem tailTrace_2802429 : CollatzResearch.WordTrace tailWord_2802429 prefixEnd_2802429 959328718065947478232913 := by
  unfold tailWord_2802429
  simp only [CollatzResearch.WordTrace]
  refine ⟨102212982764285824613682341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68141988509523883075788227 102212982764285824613682341)
  ·
    refine ⟨19164934268303592115065439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102212982764285824613682341 19164934268303592115065439)
    ·
      refine ⟨28747401402455388172598159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19164934268303592115065439 28747401402455388172598159)
      ·
        refine ⟨43121102103683082258897239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28747401402455388172598159 43121102103683082258897239)
        ·
          refine ⟨64681653155524623388345859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43121102103683082258897239 64681653155524623388345859)
          ·
            refine ⟨97022479733286935082518789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64681653155524623388345859 97022479733286935082518789)
            ·
              refine ⟨18191714949991300327972273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97022479733286935082518789 18191714949991300327972273)
              ·
                refine ⟨13643786212493475245979205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18191714949991300327972273 13643786212493475245979205)
                ·
                  refine ⟨2558209914842526608621101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13643786212493475245979205 2558209914842526608621101)
                  ·
                    refine ⟨959328718065947478232913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2558209914842526608621101 959328718065947478232913)
                    ·
                      rfl

theorem cell22_2802429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_2802429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802429 prefixEnd_2802429 := by exact prefixLift 2802429
  have htrace : WordTrace (prefixWord ++ tailWord_2802429) baseStart_2802429 baseEnd_2802429 := by
    simpa [prefixWord, tailWord_2802429, baseEnd_2802429] using wordTrace_append hprefix tailTrace_2802429
  have hstable : (prefixWord ++ tailWord_2802429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802429).length < 2 ^ (prefixWord ++ tailWord_2802429).sum := by decide
  have hdescent : baseEnd_2802429 < baseStart_2802429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802442 : List Nat := [3, 1, 2, 2, 1, 2, 11]
def baseStart_2802442 : Nat := 118140960795 + 2802442 * 2 ^ 59
def prefixEnd_2802442 : Nat := 4983230072969 + 3 ^ 40 * 2802442 * 2
def baseEnd_2802442 : Nat := 35530858082652584357699

theorem tailTrace_2802442 : CollatzResearch.WordTrace tailWord_2802442 prefixEnd_2802442 35530858082652584357699 := by
  unfold tailWord_2802442
  simp only [CollatzResearch.WordTrace]
  refine ⟨25553364228309681958476395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68142304608825818555937053 25553364228309681958476395)
  ·
    refine ⟨38330046342464522937714593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25553364228309681958476395 38330046342464522937714593)
    ·
      refine ⟨28747534756848392203285945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38330046342464522937714593 28747534756848392203285945)
      ·
        refine ⟨21560651067636294152464459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28747534756848392203285945 21560651067636294152464459)
        ·
          refine ⟨32340976601454441228696689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21560651067636294152464459 32340976601454441228696689)
          ·
            refine ⟨24255732451090830921522517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32340976601454441228696689 24255732451090830921522517)
            ·
              refine ⟨35530858082652584357699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24255732451090830921522517 35530858082652584357699)
              ·
                rfl

theorem cell22_2802442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 11].length) (baseStart_2802442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802442 prefixEnd_2802442 := by exact prefixLift 2802442
  have htrace : WordTrace (prefixWord ++ tailWord_2802442) baseStart_2802442 baseEnd_2802442 := by
    simpa [prefixWord, tailWord_2802442, baseEnd_2802442] using wordTrace_append hprefix tailTrace_2802442
  have hstable : (prefixWord ++ tailWord_2802442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802442).length < 2 ^ (prefixWord ++ tailWord_2802442).sum := by decide
  have hdescent : baseEnd_2802442 < baseStart_2802442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802463 : List Nat := [1, 1, 2, 4, 2, 3, 3, 1, 2, 3]
def baseStart_2802463 : Nat := 118140960795 + 2802463 * 2 ^ 59
def prefixEnd_2802463 : Nat := 4983230072969 + 3 ^ 40 * 2802463 * 2
def baseEnd_2802463 : Nat := 959340356960782722882809

theorem tailTrace_2802463 : CollatzResearch.WordTrace tailWord_2802463 prefixEnd_2802463 959340356960782722882809 := by
  unfold tailWord_2802463
  simp only [CollatzResearch.WordTrace]
  refine ⟨102214222846162648420420043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68142815230775098946946695 102214222846162648420420043)
  ·
    refine ⟨153321334269243972630630065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102214222846162648420420043 153321334269243972630630065)
    ·
      refine ⟨114991000701932979472972549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153321334269243972630630065 114991000701932979472972549)
      ·
        refine ⟨21560812631612433651182353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114991000701932979472972549 21560812631612433651182353)
        ·
          refine ⟨16170609473709325238386765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21560812631612433651182353 16170609473709325238386765)
          ·
            refine ⟨6063978552640996964395037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16170609473709325238386765 6063978552640996964395037)
            ·
              refine ⟨2273991957240373861648139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6063978552640996964395037 2273991957240373861648139)
              ·
                refine ⟨3410987935860560792472209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2273991957240373861648139 3410987935860560792472209)
                ·
                  refine ⟨2558240951895420594354157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3410987935860560792472209 2558240951895420594354157)
                  ·
                    refine ⟨959340356960782722882809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2558240951895420594354157 959340356960782722882809)
                    ·
                      rfl

theorem cell22_2802463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 2, 3].length) (baseStart_2802463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802463 prefixEnd_2802463 := by exact prefixLift 2802463
  have htrace : WordTrace (prefixWord ++ tailWord_2802463) baseStart_2802463 baseEnd_2802463 := by
    simpa [prefixWord, tailWord_2802463, baseEnd_2802463] using wordTrace_append hprefix tailTrace_2802463
  have hstable : (prefixWord ++ tailWord_2802463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802463).length < 2 ^ (prefixWord ++ tailWord_2802463).sum := by decide
  have hdescent : baseEnd_2802463 < baseStart_2802463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802487 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 9]
def baseStart_2802487 : Nat := 118140960795 + 2802487 * 2 ^ 59
def prefixEnd_2802487 : Nat := 4983230072969 + 3 ^ 40 * 2802487 * 2
def baseEnd_2802487 : Nat := 319782857550418220094245

theorem tailTrace_2802487 : CollatzResearch.WordTrace tailWord_2802487 prefixEnd_2802487 319782857550418220094245 := by
  unfold tailWord_2802487
  simp only [CollatzResearch.WordTrace]
  refine ⟨102215098198075700519293715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68143398798717133679529143 102215098198075700519293715)
  ·
    refine ⟨153322647297113550778940573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102215098198075700519293715 153322647297113550778940573)
    ·
      refine ⟨57495992736417581542102715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153322647297113550778940573 57495992736417581542102715)
      ·
        refine ⟨86243989104626372313154073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57495992736417581542102715 86243989104626372313154073)
        ·
          refine ⟨64682991828469779234865555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86243989104626372313154073 64682991828469779234865555)
          ·
            refine ⟨97024487742704668852298333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64682991828469779234865555 97024487742704668852298333)
            ·
              refine ⟨36384182903514250819611875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97024487742704668852298333 36384182903514250819611875)
              ·
                refine ⟨54576274355271376229417813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36384182903514250819611875 54576274355271376229417813)
                ·
                  refine ⟨319782857550418220094245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54576274355271376229417813 319782857550418220094245)
                  ·
                    rfl

theorem cell22_2802487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 9].length) (baseStart_2802487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802487 prefixEnd_2802487 := by exact prefixLift 2802487
  have htrace : WordTrace (prefixWord ++ tailWord_2802487) baseStart_2802487 baseEnd_2802487 := by
    simpa [prefixWord, tailWord_2802487, baseEnd_2802487] using wordTrace_append hprefix tailTrace_2802487
  have hstable : (prefixWord ++ tailWord_2802487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802487).length < 2 ^ (prefixWord ++ tailWord_2802487).sum := by decide
  have hdescent : baseEnd_2802487 < baseStart_2802487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802504 : List Nat := [2, 1, 3, 1, 1, 3, 2, 4, 5]
def baseStart_2802504 : Nat := 118140960795 + 2802504 * 2 ^ 59
def prefixEnd_2802504 : Nat := 4983230072969 + 3 ^ 40 * 2802504 * 2
def baseEnd_2802504 : Nat := 319784797366224094202561

theorem tailTrace_2802504 : CollatzResearch.WordTrace tailWord_2802504 prefixEnd_2802504 319784797366224094202561 := by
  unfold tailWord_2802504
  simp only [CollatzResearch.WordTrace]
  refine ⟨51107859119507056211331283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68143812159342741615108377 51107859119507056211331283)
  ·
    refine ⟨76661788679260584316996925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51107859119507056211331283 76661788679260584316996925)
    ·
      refine ⟨28748170754722719118873847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76661788679260584316996925 28748170754722719118873847)
      ·
        refine ⟨43122256132084078678310771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28748170754722719118873847 43122256132084078678310771)
        ·
          refine ⟨64683384198126118017466157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43122256132084078678310771 64683384198126118017466157)
          ·
            refine ⟨24256269074297294256549809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64683384198126118017466157 24256269074297294256549809)
            ·
              refine ⟨18192201805722970692412357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24256269074297294256549809 18192201805722970692412357)
              ·
                refine ⟨3411037838573057004827317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18192201805722970692412357 3411037838573057004827317)
                ·
                  refine ⟨319784797366224094202561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3411037838573057004827317 319784797366224094202561)
                  ·
                    rfl

theorem cell22_2802504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 5].length) (baseStart_2802504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802504 prefixEnd_2802504 := by exact prefixLift 2802504
  have htrace : WordTrace (prefixWord ++ tailWord_2802504) baseStart_2802504 baseEnd_2802504 := by
    simpa [prefixWord, tailWord_2802504, baseEnd_2802504] using wordTrace_append hprefix tailTrace_2802504
  have hstable : (prefixWord ++ tailWord_2802504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802504).length < 2 ^ (prefixWord ++ tailWord_2802504).sum := by decide
  have hdescent : baseEnd_2802504 < baseStart_2802504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802508 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 3, 3]
def baseStart_2802508 : Nat := 118140960795 + 2802508 * 2 ^ 59
def prefixEnd_2802508 : Nat := 4983230072969 + 3 ^ 40 * 2802508 * 2
def baseEnd_2802508 : Nat := 959355761380417605507671

theorem tailTrace_2802508 : CollatzResearch.WordTrace tailWord_2802508 prefixEnd_2802508 959355761380417605507671 := by
  unfold tailWord_2802508
  simp only [CollatzResearch.WordTrace]
  refine ⟨51107932065499810552904089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68143909420666414070538785 51107932065499810552904089)
  ·
    refine ⟨38330949049124857914678067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51107932065499810552904089 38330949049124857914678067)
    ·
      refine ⟨57496423573687286872017101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38330949049124857914678067 57496423573687286872017101)
      ·
        refine ⟨21561158840132732577006413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57496423573687286872017101 21561158840132732577006413)
        ·
          refine ⟨8085434565049774716377405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21561158840132732577006413 8085434565049774716377405)
          ·
            refine ⟨3032037961893665518641527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8085434565049774716377405 3032037961893665518641527)
            ·
              refine ⟨4548056942840498277962291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3032037961893665518641527 4548056942840498277962291)
              ·
                refine ⟨6822085414260747416943437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548056942840498277962291 6822085414260747416943437)
                ·
                  refine ⟨2558282030347780281353789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6822085414260747416943437 2558282030347780281353789)
                  ·
                    refine ⟨959355761380417605507671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2558282030347780281353789 959355761380417605507671)
                    ·
                      rfl

theorem cell22_2802508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_2802508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802508 prefixEnd_2802508 := by exact prefixLift 2802508
  have htrace : WordTrace (prefixWord ++ tailWord_2802508) baseStart_2802508 baseEnd_2802508 := by
    simpa [prefixWord, tailWord_2802508, baseEnd_2802508] using wordTrace_append hprefix tailTrace_2802508
  have hstable : (prefixWord ++ tailWord_2802508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802508).length < 2 ^ (prefixWord ++ tailWord_2802508).sum := by decide
  have hdescent : baseEnd_2802508 < baseStart_2802508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802521 : List Nat := [1, 2, 1, 2, 2, 4, 4, 1, 5]
def baseStart_2802521 : Nat := 118140960795 + 2802521 * 2 ^ 59
def prefixEnd_2802521 : Nat := 4983230072969 + 3 ^ 40 * 2802521 * 2
def baseEnd_2802521 : Nat := 319786737182029968310877

theorem tailTrace_2802521 : CollatzResearch.WordTrace tailWord_2802521 prefixEnd_2802521 319786737182029968310877 := by
  unfold tailWord_2802521
  simp only [CollatzResearch.WordTrace]
  refine ⟨102216338279952524326031417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68144225519968349550687611 102216338279952524326031417)
  ·
    refine ⟨76662253709964393244523563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102216338279952524326031417 76662253709964393244523563)
    ·
      refine ⟨114993380564946589866785345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76662253709964393244523563 114993380564946589866785345)
      ·
        refine ⟨86245035423709942400089009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114993380564946589866785345 86245035423709942400089009)
        ·
          refine ⟨64683776567782456800066757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86245035423709942400089009 64683776567782456800066757)
          ·
            refine ⟨12128208106459210650012517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64683776567782456800066757 12128208106459210650012517)
            ·
              refine ⟨2274039019961101996877347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12128208106459210650012517 2274039019961101996877347)
              ·
                refine ⟨3411058529941652995316021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2274039019961101996877347 3411058529941652995316021)
                ·
                  refine ⟨319786737182029968310877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3411058529941652995316021 319786737182029968310877)
                  ·
                    rfl

theorem cell22_2802521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 5].length) (baseStart_2802521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802521 prefixEnd_2802521 := by exact prefixLift 2802521
  have htrace : WordTrace (prefixWord ++ tailWord_2802521) baseStart_2802521 baseEnd_2802521 := by
    simpa [prefixWord, tailWord_2802521, baseEnd_2802521] using wordTrace_append hprefix tailTrace_2802521
  have hstable : (prefixWord ++ tailWord_2802521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802521).length < 2 ^ (prefixWord ++ tailWord_2802521).sum := by decide
  have hdescent : baseEnd_2802521 < baseStart_2802521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802564 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_2802564 : Nat := 118140960795 + 2802564 * 2 ^ 59
def prefixEnd_2802564 : Nat := 4983230072969 + 3 ^ 40 * 2802564 * 2
def baseEnd_2802564 : Nat := 959374931324852126107499

theorem tailTrace_2802564 : CollatzResearch.WordTrace tailWord_2802564 prefixEnd_2802564 959374931324852126107499 := by
  unfold tailWord_2802564
  simp only [CollatzResearch.WordTrace]
  refine ⟨51108953309398371334923373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68145271079197828446564497 51108953309398371334923373)
  ·
    refine ⟨19165857491024389250596265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51108953309398371334923373 19165857491024389250596265)
    ·
      refine ⟨14374393118268291937947199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19165857491024389250596265 14374393118268291937947199)
      ·
        refine ⟨21561589677402437906920799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14374393118268291937947199 21561589677402437906920799)
        ·
          refine ⟨32342384516103656860381199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21561589677402437906920799 32342384516103656860381199)
          ·
            refine ⟨48513576774155485290571799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32342384516103656860381199 48513576774155485290571799)
            ·
              refine ⟨72770365161233227935857699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48513576774155485290571799 72770365161233227935857699)
              ·
                refine ⟨109155547741849841903786549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72770365161233227935857699 109155547741849841903786549)
                ·
                  refine ⟨10233332600798422678479989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109155547741849841903786549 10233332600798422678479989)
                  ·
                    refine ⟨959374931324852126107499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10233332600798422678479989 959374931324852126107499)
                    ·
                      rfl

theorem cell22_2802564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_2802564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802564 prefixEnd_2802564 := by exact prefixLift 2802564
  have htrace : WordTrace (prefixWord ++ tailWord_2802564) baseStart_2802564 baseEnd_2802564 := by
    simpa [prefixWord, tailWord_2802564, baseEnd_2802564] using wordTrace_append hprefix tailTrace_2802564
  have hstable : (prefixWord ++ tailWord_2802564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802564).length < 2 ^ (prefixWord ++ tailWord_2802564).sum := by decide
  have hdescent : baseEnd_2802564 < baseStart_2802564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802581 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 1, 5]
def baseStart_2802581 : Nat := 118140960795 + 2802581 * 2 ^ 59
def prefixEnd_2802581 : Nat := 4983230072969 + 3 ^ 40 * 2802581 * 2
def baseEnd_2802581 : Nat := 959380750772269748432447

theorem tailTrace_2802581 : CollatzResearch.WordTrace tailWord_2802581 prefixEnd_2802581 959380750772269748432447 := by
  unfold tailWord_2802581
  simp only [CollatzResearch.WordTrace]
  refine ⟨102218526659735154573215597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68145684439823436382143731 102218526659735154573215597)
  ·
    refine ⟨38331947497400682964955849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102218526659735154573215597 38331947497400682964955849)
    ·
      refine ⟨28748960623050512223716887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38331947497400682964955849 28748960623050512223716887)
      ·
        refine ⟨43123440934575768335575331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28748960623050512223716887 43123440934575768335575331)
        ·
          refine ⟨64685161401863652503362997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43123440934575768335575331 64685161401863652503362997)
          ·
            refine ⟨6064233881424717422190281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64685161401863652503362997 6064233881424717422190281)
            ·
              refine ⟨4548175411068538066642711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6064233881424717422190281 4548175411068538066642711)
              ·
                refine ⟨6822263116602807099964067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548175411068538066642711 6822263116602807099964067)
                ·
                  refine ⟨10233394674904210649946101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6822263116602807099964067 10233394674904210649946101)
                  ·
                    refine ⟨959380750772269748432447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10233394674904210649946101 959380750772269748432447)
                    ·
                      rfl

theorem cell22_2802581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_2802581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802581 prefixEnd_2802581 := by exact prefixLift 2802581
  have htrace : WordTrace (prefixWord ++ tailWord_2802581) baseStart_2802581 baseEnd_2802581 := by
    simpa [prefixWord, tailWord_2802581, baseEnd_2802581] using wordTrace_append hprefix tailTrace_2802581
  have hstable : (prefixWord ++ tailWord_2802581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802581).length < 2 ^ (prefixWord ++ tailWord_2802581).sum := by decide
  have hdescent : baseEnd_2802581 < baseStart_2802581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802645 : List Nat := [1, 3, 2, 3, 4, 1, 2, 6]
def baseStart_2802645 : Nat := 118140960795 + 2802645 * 2 ^ 59
def prefixEnd_2802645 : Nat := 4983230072969 + 3 ^ 40 * 2802645 * 2
def baseEnd_2802645 : Nat := 106600295475577212759139

theorem tailTrace_2802645 : CollatzResearch.WordTrace tailWord_2802645 prefixEnd_2802645 106600295475577212759139 := by
  unfold tailWord_2802645
  simp only [CollatzResearch.WordTrace]
  refine ⟨102220860931503293503545389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68147240621002195669030259 102220860931503293503545389)
  ·
    refine ⟨38332822849313735063829521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102220860931503293503545389 38332822849313735063829521)
    ·
      refine ⟨28749617136985301297872141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38332822849313735063829521 28749617136985301297872141)
      ·
        refine ⟨10781106426369487986702053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28749617136985301297872141 10781106426369487986702053)
        ·
          refine ⟨2021457454944278997506635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10781106426369487986702053 2021457454944278997506635)
          ·
            refine ⟨3032186182416418496259953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2021457454944278997506635 3032186182416418496259953)
            ·
              refine ⟨2274139636812313872194965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3032186182416418496259953 2274139636812313872194965)
              ·
                refine ⟨106600295475577212759139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2274139636812313872194965 106600295475577212759139)
                ·
                  rfl

theorem cell22_2802645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 6].length) (baseStart_2802645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802645 prefixEnd_2802645 := by exact prefixLift 2802645
  have htrace : WordTrace (prefixWord ++ tailWord_2802645) baseStart_2802645 baseEnd_2802645 := by
    simpa [prefixWord, tailWord_2802645, baseEnd_2802645] using wordTrace_append hprefix tailTrace_2802645
  have hstable : (prefixWord ++ tailWord_2802645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802645).length < 2 ^ (prefixWord ++ tailWord_2802645).sum := by decide
  have hdescent : baseEnd_2802645 < baseStart_2802645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802731 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 2, 4]
def baseStart_2802731 : Nat := 118140960795 + 2802731 * 2 ^ 59
def prefixEnd_2802731 : Nat := 4983230072969 + 3 ^ 40 * 2802731 * 2
def baseEnd_2802731 : Nat := 959432098837719357181987

theorem tailTrace_2802731 : CollatzResearch.WordTrace tailWord_2802731 prefixEnd_2802731 959432098837719357181987 := by
  unfold tailWord_2802731
  simp only [CollatzResearch.WordTrace]
  refine ⟨102223997609191730191176047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68149331739461153460784031 102223997609191730191176047)
  ·
    refine ⟨153335996413787595286764071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102223997609191730191176047 153335996413787595286764071)
    ·
      refine ⟨230003994620681392930146107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153335996413787595286764071 230003994620681392930146107)
      ·
        refine ⟨345005991931022089395219161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230003994620681392930146107 345005991931022089395219161)
        ·
          refine ⟨258754493948266567046414371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345005991931022089395219161 258754493948266567046414371)
          ·
            refine ⟨388131740922399850569621557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258754493948266567046414371 388131740922399850569621557)
            ·
              refine ⟨36387350711474985990902021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 388131740922399850569621557 36387350711474985990902021)
              ·
                refine ⟨6822628258401559873294129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36387350711474985990902021 6822628258401559873294129)
                ·
                  refine ⟨5116971193801169904970597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6822628258401559873294129 5116971193801169904970597)
                  ·
                    refine ⟨959432098837719357181987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5116971193801169904970597 959432098837719357181987)
                    ·
                      rfl

theorem cell22_2802731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 4].length) (baseStart_2802731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802731 prefixEnd_2802731 := by exact prefixLift 2802731
  have htrace : WordTrace (prefixWord ++ tailWord_2802731) baseStart_2802731 baseEnd_2802731 := by
    simpa [prefixWord, tailWord_2802731, baseEnd_2802731] using wordTrace_append hprefix tailTrace_2802731
  have hstable : (prefixWord ++ tailWord_2802731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802731).length < 2 ^ (prefixWord ++ tailWord_2802731).sum := by decide
  have hdescent : baseEnd_2802731 < baseStart_2802731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802746 : List Nat := [3, 1, 1, 1, 3, 1, 5, 7]
def baseStart_2802746 : Nat := 118140960795 + 2802746 * 2 ^ 59
def prefixEnd_2802746 : Nat := 4983230072969 + 3 ^ 40 * 2802746 * 2
def baseEnd_2802746 : Nat := 106604137071584924228549

theorem tailTrace_2802746 : CollatzResearch.WordTrace tailWord_2802746 prefixEnd_2802746 106604137071584924228549 := by
  unfold tailWord_2802746
  simp only [CollatzResearch.WordTrace]
  refine ⟨25556136176034346938243023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68149696469424925168648061 25556136176034346938243023)
  ·
    refine ⟨38334204264051520407364535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25556136176034346938243023 38334204264051520407364535)
    ·
      refine ⟨57501306396077280611046803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38334204264051520407364535 57501306396077280611046803)
      ·
        refine ⟨86251959594115920916570205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57501306396077280611046803 86251959594115920916570205)
        ·
          refine ⟨32344484847793470343713827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86251959594115920916570205 32344484847793470343713827)
          ·
            refine ⟨48516727271690205515570741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32344484847793470343713827 48516727271690205515570741)
            ·
              refine ⟨4548443181720956767084757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48516727271690205515570741 4548443181720956767084757)
              ·
                refine ⟨106604137071584924228549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4548443181720956767084757 106604137071584924228549)
                ·
                  rfl

theorem cell22_2802746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 7].length) (baseStart_2802746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802746 prefixEnd_2802746 := by exact prefixLift 2802746
  have htrace : WordTrace (prefixWord ++ tailWord_2802746) baseStart_2802746 baseEnd_2802746 := by
    simpa [prefixWord, tailWord_2802746, baseEnd_2802746] using wordTrace_append hprefix tailTrace_2802746
  have hstable : (prefixWord ++ tailWord_2802746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802746).length < 2 ^ (prefixWord ++ tailWord_2802746).sum := by decide
  have hdescent : baseEnd_2802746 < baseStart_2802746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802750 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_2802750 : Nat := 118140960795 + 2802750 * 2 ^ 59
def prefixEnd_2802750 : Nat := 4983230072969 + 3 ^ 40 * 2802750 * 2
def baseEnd_2802750 : Nat := 959438602926009640956929

theorem tailTrace_2802750 : CollatzResearch.WordTrace tailWord_2802750 prefixEnd_2802750 959438602926009640956929 := by
  unfold tailWord_2802750
  simp only [CollatzResearch.WordTrace]
  refine ⟨12778086324515362054514713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68149793730748597624078469 12778086324515362054514713)
  ·
    refine ⟨9583564743386521540886035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12778086324515362054514713 9583564743386521540886035)
    ·
      refine ⟨14375347115079782311329053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9583564743386521540886035 14375347115079782311329053)
      ·
        refine ⟨5390755168154918366748395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14375347115079782311329053 5390755168154918366748395)
        ·
          refine ⟨8086132752232377550122593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5390755168154918366748395 8086132752232377550122593)
          ·
            refine ⟨6064599564174283162591945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8086132752232377550122593 6064599564174283162591945)
            ·
              refine ⟨4548449673130712371943959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6064599564174283162591945 4548449673130712371943959)
              ·
                refine ⟨6822674509696068557915939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548449673130712371943959 6822674509696068557915939)
                ·
                  refine ⟨10234011764544102836873909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6822674509696068557915939 10234011764544102836873909)
                  ·
                    refine ⟨959438602926009640956929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10234011764544102836873909 959438602926009640956929)
                    ·
                      rfl

theorem cell22_2802750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_2802750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802750 prefixEnd_2802750 := by exact prefixLift 2802750
  have htrace : WordTrace (prefixWord ++ tailWord_2802750) baseStart_2802750 baseEnd_2802750 := by
    simpa [prefixWord, tailWord_2802750, baseEnd_2802750] using wordTrace_append hprefix tailTrace_2802750
  have hstable : (prefixWord ++ tailWord_2802750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802750).length < 2 ^ (prefixWord ++ tailWord_2802750).sum := by decide
  have hdescent : baseEnd_2802750 < baseStart_2802750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802765 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_2802765 : Nat := 118140960795 + 2802765 * 2 ^ 59
def prefixEnd_2802765 : Nat := 4983230072969 + 3 ^ 40 * 2802765 * 2
def baseEnd_2802765 : Nat := 959443737732554601831883

theorem tailTrace_2802765 : CollatzResearch.WordTrace tailWord_2802765 prefixEnd_2802765 959443737732554601831883 := by
  unfold tailWord_2802765
  simp only [CollatzResearch.WordTrace]
  refine ⟨102225237691068553997913749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68150158460712369331942499 102225237691068553997913749)
  ·
    refine ⟨4791808016768838468652207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102225237691068553997913749 4791808016768838468652207)
    ·
      refine ⟨7187712025153257702978311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4791808016768838468652207 7187712025153257702978311)
      ·
        refine ⟨10781568037729886554467467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7187712025153257702978311 10781568037729886554467467)
        ·
          refine ⟨16172352056594829831701201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10781568037729886554467467 16172352056594829831701201)
          ·
            refine ⟨12129264042446122373775901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16172352056594829831701201 12129264042446122373775901)
            ·
              refine ⟨4548474015917295890165963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12129264042446122373775901 4548474015917295890165963)
              ·
                refine ⟨6822711023875943835248945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548474015917295890165963 6822711023875943835248945)
                ·
                  refine ⟨5117033267906957876436709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6822711023875943835248945 5117033267906957876436709)
                  ·
                    refine ⟨959443737732554601831883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5117033267906957876436709 959443737732554601831883)
                    ·
                      rfl

theorem cell22_2802765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_2802765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802765 prefixEnd_2802765 := by exact prefixLift 2802765
  have htrace : WordTrace (prefixWord ++ tailWord_2802765) baseStart_2802765 baseEnd_2802765 := by
    simpa [prefixWord, tailWord_2802765, baseEnd_2802765] using wordTrace_append hprefix tailTrace_2802765
  have hstable : (prefixWord ++ tailWord_2802765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802765).length < 2 ^ (prefixWord ++ tailWord_2802765).sum := by decide
  have hdescent : baseEnd_2802765 < baseStart_2802765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802846 : List Nat := [4, 3, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_2802846 : Nat := 118140960795 + 2802846 * 2 ^ 59
def prefixEnd_2802846 : Nat := 4983230072969 + 3 ^ 40 * 2802846 * 2
def baseEnd_2802846 : Nat := 959471465687897390556635

theorem tailTrace_2802846 : CollatzResearch.WordTrace tailWord_2802846 prefixEnd_2802846 959471465687897390556635 := by
  unfold tailWord_2802846
  simp only [CollatzResearch.WordTrace]
  refine ⟨12778524000471888103951549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68152128002516736554408261 12778524000471888103951549)
  ·
    refine ⟨4791946500176958038981831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12778524000471888103951549 4791946500176958038981831)
    ·
      refine ⟨7187919750265437058472747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4791946500176958038981831 7187919750265437058472747)
      ·
        refine ⟨10781879625398155587709121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7187919750265437058472747 10781879625398155587709121)
        ·
          refine ⟨8086409719048616690781841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10781879625398155587709121 8086409719048616690781841)
          ·
            refine ⟨6064807289286462518086381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8086409719048616690781841 6064807289286462518086381)
            ·
              refine ⟨2274302733482423444282393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6064807289286462518086381 2274302733482423444282393)
              ·
                refine ⟨1705727050111817583211795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2274302733482423444282393 1705727050111817583211795)
                ·
                  refine ⟨2558590575167726374817693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705727050111817583211795 2558590575167726374817693)
                  ·
                    refine ⟨959471465687897390556635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2558590575167726374817693 959471465687897390556635)
                    ·
                      rfl

theorem cell22_2802846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_2802846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802846 prefixEnd_2802846 := by exact prefixLift 2802846
  have htrace : WordTrace (prefixWord ++ tailWord_2802846) baseStart_2802846 baseEnd_2802846 := by
    simpa [prefixWord, tailWord_2802846, baseEnd_2802846] using wordTrace_append hprefix tailTrace_2802846
  have hstable : (prefixWord ++ tailWord_2802846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802846).length < 2 ^ (prefixWord ++ tailWord_2802846).sum := by decide
  have hdescent : baseEnd_2802846 < baseStart_2802846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802853 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 6]
def baseStart_2802853 : Nat := 118140960795 + 2802853 * 2 ^ 59
def prefixEnd_2802853 : Nat := 4983230072969 + 3 ^ 40 * 2802853 * 2
def baseEnd_2802853 : Nat := 319824620643650568543871

theorem tailTrace_2802853 : CollatzResearch.WordTrace tailWord_2802853 prefixEnd_2802853 319824620643650568543871 := by
  unfold tailWord_2802853
  simp only [CollatzResearch.WordTrace]
  refine ⟨102228447314749745027117213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68152298209833163351411475 102228447314749745027117213)
  ·
    refine ⟨38335667743031154385168955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102228447314749745027117213 38335667743031154385168955)
    ·
      refine ⟨57503501614546731577753433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38335667743031154385168955 57503501614546731577753433)
      ·
        refine ⟨43127626210910048683315075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57503501614546731577753433 43127626210910048683315075)
        ·
          refine ⟨64691439316365073024972613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43127626210910048683315075 64691439316365073024972613)
          ·
            refine ⟨12129644871818451192182365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64691439316365073024972613 12129644871818451192182365)
            ·
              refine ⟨4548616826931919197068387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12129644871818451192182365 4548616826931919197068387)
              ·
                refine ⟨6822925240397878795602581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548616826931919197068387 6822925240397878795602581)
                ·
                  refine ⟨319824620643650568543871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6822925240397878795602581 319824620643650568543871)
                  ·
                    rfl

theorem cell22_2802853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_2802853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802853 prefixEnd_2802853 := by exact prefixLift 2802853
  have htrace : WordTrace (prefixWord ++ tailWord_2802853) baseStart_2802853 baseEnd_2802853 := by
    simpa [prefixWord, tailWord_2802853, baseEnd_2802853] using wordTrace_append hprefix tailTrace_2802853
  have hstable : (prefixWord ++ tailWord_2802853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802853).length < 2 ^ (prefixWord ++ tailWord_2802853).sum := by decide
  have hdescent : baseEnd_2802853 < baseStart_2802853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802904 : List Nat := [2, 1, 2, 2, 5, 2, 2, 2, 4]
def baseStart_2802904 : Nat := 118140960795 + 2802904 * 2 ^ 59
def prefixEnd_2802904 : Nat := 4983230072969 + 3 ^ 40 * 2802904 * 2
def baseEnd_2802904 : Nat := 319830440091068190868819

theorem tailTrace_2802904 : CollatzResearch.WordTrace tailWord_2802904 prefixEnd_2802904 319830440091068190868819 := by
  unfold tailWord_2802904
  simp only [CollatzResearch.WordTrace]
  refine ⟨51115153718782490368611883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68153538291709987158149177 51115153718782490368611883)
  ·
    refine ⟨76672730578173735552917825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51115153718782490368611883 76672730578173735552917825)
    ·
      refine ⟨57504547933630301664688369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76672730578173735552917825 57504547933630301664688369)
      ·
        refine ⟨43128410950222726248516277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57504547933630301664688369 43128410950222726248516277)
        ·
          refine ⟨4043288526583380585798401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43128410950222726248516277 4043288526583380585798401)
          ·
            refine ⟨3032466394937535439348801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4043288526583380585798401 3032466394937535439348801)
            ·
              refine ⟨2274349796203151579511601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3032466394937535439348801 2274349796203151579511601)
              ·
                refine ⟨1705762347152363684633701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2274349796203151579511601 1705762347152363684633701)
                ·
                  refine ⟨319830440091068190868819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1705762347152363684633701 319830440091068190868819)
                  ·
                    rfl

theorem cell22_2802904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 4].length) (baseStart_2802904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802904 prefixEnd_2802904 := by exact prefixLift 2802904
  have htrace : WordTrace (prefixWord ++ tailWord_2802904) baseStart_2802904 baseEnd_2802904 := by
    simpa [prefixWord, tailWord_2802904, baseEnd_2802904] using wordTrace_append hprefix tailTrace_2802904
  have hstable : (prefixWord ++ tailWord_2802904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802904).length < 2 ^ (prefixWord ++ tailWord_2802904).sum := by decide
  have hdescent : baseEnd_2802904 < baseStart_2802904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2802947 : List Nat := [1, 1, 1, 3, 2, 4, 1, 5, 1, 3]
def baseStart_2802947 : Nat := 118140960795 + 2802947 * 2 ^ 59
def prefixEnd_2802947 : Nat := 4983230072969 + 3 ^ 40 * 2802947 * 2
def baseEnd_2802947 : Nat := 959506040051966793781325

theorem tailTrace_2802947 : CollatzResearch.WordTrace tailWord_2802947 prefixEnd_2802947 959506040051966793781325 := by
  unfold tailWord_2802947
  simp only [CollatzResearch.WordTrace]
  refine ⟨102231875776409199081039095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68154583850939466054026063 102231875776409199081039095)
  ·
    refine ⟨153347813664613798621558643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102231875776409199081039095 153347813664613798621558643)
    ·
      refine ⟨230021720496920697932337965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153347813664613798621558643 230021720496920697932337965)
      ·
        refine ⟨86258145186345261724626737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230021720496920697932337965 86258145186345261724626737)
        ·
          refine ⟨64693608889758946293470053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86258145186345261724626737 64693608889758946293470053)
          ·
            refine ⟨12130051666829802430025635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64693608889758946293470053 12130051666829802430025635)
            ·
              refine ⟨18195077500244703645038453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12130051666829802430025635 18195077500244703645038453)
              ·
                refine ⟨1705788515647940966722355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18195077500244703645038453 1705788515647940966722355)
                ·
                  refine ⟨2558682773471911450083533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705788515647940966722355 2558682773471911450083533)
                  ·
                    refine ⟨959506040051966793781325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2558682773471911450083533 959506040051966793781325)
                    ·
                      rfl

theorem cell22_2802947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 1, 3].length) (baseStart_2802947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2802947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2802947 prefixEnd_2802947 := by exact prefixLift 2802947
  have htrace : WordTrace (prefixWord ++ tailWord_2802947) baseStart_2802947 baseEnd_2802947 := by
    simpa [prefixWord, tailWord_2802947, baseEnd_2802947] using wordTrace_append hprefix tailTrace_2802947
  have hstable : (prefixWord ++ tailWord_2802947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2802947).length < 2 ^ (prefixWord ++ tailWord_2802947).sum := by decide
  have hdescent : baseEnd_2802947 < baseStart_2802947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2802947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803033 : List Nat := [1, 2, 1, 2, 2, 2, 3, 9]
def baseStart_2803033 : Nat := 118140960795 + 2803033 * 2 ^ 59
def prefixEnd_2803033 : Nat := 4983230072969 + 3 ^ 40 * 2803033 * 2
def baseEnd_2803033 : Nat := 106615053289943470681229

theorem tailTrace_2803033 : CollatzResearch.WordTrace tailWord_2803033 prefixEnd_2803033 106615053289943470681229 := by
  unfold tailWord_2803033
  simp only [CollatzResearch.WordTrace]
  refine ⟨102235012454097635768669753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68156674969398423845779835 102235012454097635768669753)
  ·
    refine ⟨76676259340573226826502315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102235012454097635768669753 76676259340573226826502315)
    ·
      refine ⟨115014389010859840239753473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76676259340573226826502315 115014389010859840239753473)
      ·
        refine ⟨86260791758144880179815105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115014389010859840239753473 86260791758144880179815105)
        ·
          refine ⟨64695593818608660134861329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86260791758144880179815105 64695593818608660134861329)
          ·
            refine ⟨48521695363956495101145997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64695593818608660134861329 48521695363956495101145997)
            ·
              refine ⟨18195635761483685662929749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48521695363956495101145997 18195635761483685662929749)
              ·
                refine ⟨106615053289943470681229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18195635761483685662929749 106615053289943470681229)
                ·
                  rfl

theorem cell22_2803033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 9].length) (baseStart_2803033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803033 prefixEnd_2803033 := by exact prefixLift 2803033
  have htrace : WordTrace (prefixWord ++ tailWord_2803033) baseStart_2803033 baseEnd_2803033 := by
    simpa [prefixWord, tailWord_2803033, baseEnd_2803033] using wordTrace_append hprefix tailTrace_2803033
  have hstable : (prefixWord ++ tailWord_2803033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803033).length < 2 ^ (prefixWord ++ tailWord_2803033).sum := by decide
  have hdescent : baseEnd_2803033 < baseStart_2803033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803052 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 2, 4]
def baseStart_2803052 : Nat := 118140960795 + 2803052 * 2 ^ 59
def prefixEnd_2803052 : Nat := 4983230072969 + 3 ^ 40 * 2803052 * 2
def baseEnd_2803052 : Nat := 959541983697781519906003

theorem tailTrace_2803052 : CollatzResearch.WordTrace tailWord_2803052 prefixEnd_2803052 959541983697781519906003 := by
  unfold tailWord_2803052
  simp only [CollatzResearch.WordTrace]
  refine ⟨51117852720514401006805705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68157136960685868009074273 51117852720514401006805705)
  ·
    refine ⟨38338389540385800755104279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51117852720514401006805705 38338389540385800755104279)
    ·
      refine ⟨57507584310578701132656419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38338389540385800755104279 57507584310578701132656419)
      ·
        refine ⟨86261376465868051698984629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57507584310578701132656419 86261376465868051698984629)
        ·
          refine ⟨8087004043675129846779809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86261376465868051698984629 8087004043675129846779809)
          ·
            refine ⟨6065253032756347385084857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8087004043675129846779809 6065253032756347385084857)
            ·
              refine ⟨4548939774567260538813643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6065253032756347385084857 4548939774567260538813643)
              ·
                refine ⟨6823409661850890808220465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548939774567260538813643 6823409661850890808220465)
                ·
                  refine ⟨5117557246388168106165349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6823409661850890808220465 5117557246388168106165349)
                  ·
                    refine ⟨959541983697781519906003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5117557246388168106165349 959541983697781519906003)
                    ·
                      rfl

theorem cell22_2803052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_2803052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803052 prefixEnd_2803052 := by exact prefixLift 2803052
  have htrace : WordTrace (prefixWord ++ tailWord_2803052) baseStart_2803052 baseEnd_2803052 := by
    simpa [prefixWord, tailWord_2803052, baseEnd_2803052] using wordTrace_append hprefix tailTrace_2803052
  have hstable : (prefixWord ++ tailWord_2803052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803052).length < 2 ^ (prefixWord ++ tailWord_2803052).sum := by decide
  have hdescent : baseEnd_2803052 < baseStart_2803052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803054 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 1, 5]
def baseStart_2803054 : Nat := 118140960795 + 2803054 * 2 ^ 59
def prefixEnd_2803054 : Nat := 4983230072969 + 3 ^ 40 * 2803054 * 2
def baseEnd_2803054 : Nat := 959542668338654181355997

theorem tailTrace_2803054 : CollatzResearch.WordTrace tailWord_2803054 prefixEnd_2803054 959542668338654181355997 := by
  unfold tailWord_2803054
  simp only [CollatzResearch.WordTrace]
  refine ⟨12779472298377694544398027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68157185591347704236789477 12779472298377694544398027)
  ·
    refine ⟨19169208447566541816597041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12779472298377694544398027 19169208447566541816597041)
    ·
      refine ⟨14376906335674906362447781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19169208447566541816597041 14376906335674906362447781)
      ·
        refine ⟨2695669937939044942958959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14376906335674906362447781 2695669937939044942958959)
        ·
          refine ⟨4043504906908567414438439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2695669937939044942958959 4043504906908567414438439)
          ·
            refine ⟨6065257360362851121657659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4043504906908567414438439 6065257360362851121657659)
            ·
              refine ⟨9097886040544276682486489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6065257360362851121657659 9097886040544276682486489)
              ·
                refine ⟨6823414530408207511864867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9097886040544276682486489 6823414530408207511864867)
                ·
                  refine ⟨10235121795612311267797301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6823414530408207511864867 10235121795612311267797301)
                  ·
                    refine ⟨959542668338654181355997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10235121795612311267797301 959542668338654181355997)
                    ·
                      rfl

theorem cell22_2803054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_2803054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803054 prefixEnd_2803054 := by exact prefixLift 2803054
  have htrace : WordTrace (prefixWord ++ tailWord_2803054) baseStart_2803054 baseEnd_2803054 := by
    simpa [prefixWord, tailWord_2803054, baseEnd_2803054] using wordTrace_append hprefix tailTrace_2803054
  have hstable : (prefixWord ++ tailWord_2803054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803054).length < 2 ^ (prefixWord ++ tailWord_2803054).sum := by decide
  have hdescent : baseEnd_2803054 < baseStart_2803054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803073 : List Nat := [1, 2, 4, 3, 3, 1, 2, 2, 4]
def baseStart_2803073 : Nat := 118140960795 + 2803073 * 2 ^ 59
def prefixEnd_2803073 : Nat := 4983230072969 + 3 ^ 40 * 2803073 * 2
def baseEnd_2803073 : Nat := 319849724142314821710313

theorem tailTrace_2803073 : CollatzResearch.WordTrace tailWord_2803073 prefixEnd_2803073 319849724142314821710313 := by
  unfold tailWord_2803073
  simp only [CollatzResearch.WordTrace]
  refine ⟨102236471373952722600125873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68157647582635148400083915 102236471373952722600125873)
  ·
    refine ⟨76677353530464541950094405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102236471373952722600125873 76677353530464541950094405)
    ·
      refine ⟨14377003786962101615642701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76677353530464541950094405 14377003786962101615642701)
      ·
        refine ⟨5391376420110788105866013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14377003786962101615642701 5391376420110788105866013)
        ·
          refine ⟨2021766157541545539699755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5391376420110788105866013 2021766157541545539699755)
          ·
            refine ⟨3032649236312318309549633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2021766157541545539699755 3032649236312318309549633)
            ·
              refine ⟨2274486927234238732162225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3032649236312318309549633 2274486927234238732162225)
              ·
                refine ⟨1705865195425679049121669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2274486927234238732162225 1705865195425679049121669)
                ·
                  refine ⟨319849724142314821710313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1705865195425679049121669 319849724142314821710313)
                  ·
                    rfl

theorem cell22_2803073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 4].length) (baseStart_2803073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803073 prefixEnd_2803073 := by exact prefixLift 2803073
  have htrace : WordTrace (prefixWord ++ tailWord_2803073) baseStart_2803073 baseEnd_2803073 := by
    simpa [prefixWord, tailWord_2803073, baseEnd_2803073] using wordTrace_append hprefix tailTrace_2803073
  have hstable : (prefixWord ++ tailWord_2803073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803073).length < 2 ^ (prefixWord ++ tailWord_2803073).sum := by decide
  have hdescent : baseEnd_2803073 < baseStart_2803073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803080 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 2, 6]
def baseStart_2803080 : Nat := 118140960795 + 2803080 * 2 ^ 59
def prefixEnd_2803080 : Nat := 4983230072969 + 3 ^ 40 * 2803080 * 2
def baseEnd_2803080 : Nat := 959551568669998780205917

theorem tailTrace_2803080 : CollatzResearch.WordTrace tailWord_2803080 prefixEnd_2803080 959551568669998780205917 := by
  unfold tailWord_2803080
  simp only [CollatzResearch.WordTrace]
  refine ⟨51118363342463681397815347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68157817789951575197087129 51118363342463681397815347)
  ·
    refine ⟨76677545013695522096723021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51118363342463681397815347 76677545013695522096723021)
    ·
      refine ⟨28754079380135820786271133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76677545013695522096723021 28754079380135820786271133)
      ·
        refine ⟨10782779767550932794851675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28754079380135820786271133 10782779767550932794851675)
        ·
          refine ⟨16174169651326399192277513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10782779767550932794851675 16174169651326399192277513)
          ·
            refine ⟨12130627238494799394208135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16174169651326399192277513 12130627238494799394208135)
            ·
              refine ⟨18195940857742199091312203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12130627238494799394208135 18195940857742199091312203)
              ·
                refine ⟨27293911286613298636968305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18195940857742199091312203 27293911286613298636968305)
                ·
                  refine ⟨20470433464959973977726229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27293911286613298636968305 20470433464959973977726229)
                  ·
                    refine ⟨959551568669998780205917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20470433464959973977726229 959551568669998780205917)
                    ·
                      rfl

theorem cell22_2803080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_2803080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803080 prefixEnd_2803080 := by exact prefixLift 2803080
  have htrace : WordTrace (prefixWord ++ tailWord_2803080) baseStart_2803080 baseEnd_2803080 := by
    simpa [prefixWord, tailWord_2803080, baseEnd_2803080] using wordTrace_append hprefix tailTrace_2803080
  have hstable : (prefixWord ++ tailWord_2803080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803080).length < 2 ^ (prefixWord ++ tailWord_2803080).sum := by decide
  have hdescent : baseEnd_2803080 < baseStart_2803080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803129 : List Nat := [1, 2, 1, 4, 4, 2, 1, 2, 5]
def baseStart_2803129 : Nat := 118140960795 + 2803129 * 2 ^ 59
def prefixEnd_2803129 : Nat := 4983230072969 + 3 ^ 40 * 2803129 * 2
def baseEnd_2803129 : Nat := 319856114123792995243589

theorem tailTrace_2803129 : CollatzResearch.WordTrace tailWord_2803129 prefixEnd_2803129 319856114123792995243589 := by
  unfold tailWord_2803129
  simp only [CollatzResearch.WordTrace]
  refine ⟨102238513861749844164164441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68159009241166562776109627 102238513861749844164164441)
  ·
    refine ⟨76678885396312383123123331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102238513861749844164164441 76678885396312383123123331)
    ·
      refine ⟨115018328094468574684684997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76678885396312383123123331 115018328094468574684684997)
      ·
        refine ⟨21565936517712857753378437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115018328094468574684684997 21565936517712857753378437)
        ·
          refine ⟨4043613097071160828758457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21565936517712857753378437 4043613097071160828758457)
          ·
            refine ⟨3032709822803370621568843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4043613097071160828758457 3032709822803370621568843)
            ·
              refine ⟨4549064734205055932353265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3032709822803370621568843 4549064734205055932353265)
              ·
                refine ⟨3411798550653791949264949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4549064734205055932353265 3411798550653791949264949)
                ·
                  refine ⟨319856114123792995243589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3411798550653791949264949 319856114123792995243589)
                  ·
                    rfl

theorem cell22_2803129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 5].length) (baseStart_2803129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803129 prefixEnd_2803129 := by exact prefixLift 2803129
  have htrace : WordTrace (prefixWord ++ tailWord_2803129) baseStart_2803129 baseEnd_2803129 := by
    simpa [prefixWord, tailWord_2803129, baseEnd_2803129] using wordTrace_append hprefix tailTrace_2803129
  have hstable : (prefixWord ++ tailWord_2803129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803129).length < 2 ^ (prefixWord ++ tailWord_2803129).sum := by decide
  have hdescent : baseEnd_2803129 < baseStart_2803129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803185 : List Nat := [1, 2, 2, 2, 3, 2, 10]
def baseStart_2803185 : Nat := 118140960795 + 2803185 * 2 ^ 59
def prefixEnd_2803185 : Nat := 4983230072969 + 3 ^ 40 * 2803185 * 2
def baseEnd_2803185 : Nat := 35540278233919018752985

theorem tailTrace_2803185 : CollatzResearch.WordTrace tailWord_2803185 prefixEnd_2803185 35540278233919018752985 := by
  unfold tailWord_2803185
  simp only [CollatzResearch.WordTrace]
  refine ⟨102240556349546965728203009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68160370899697977152135339 102240556349546965728203009)
  ·
    refine ⟨76680417262160224296152257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102240556349546965728203009 76680417262160224296152257)
    ·
      refine ⟨57510312946620168222114193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76680417262160224296152257 57510312946620168222114193)
      ·
        refine ⟨43132734709965126166585645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57510312946620168222114193 43132734709965126166585645)
        ·
          refine ⟨16174775516236922312469617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43132734709965126166585645 16174775516236922312469617)
          ·
            refine ⟨12131081637177691734352213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16174775516236922312469617 12131081637177691734352213)
            ·
              refine ⟨35540278233919018752985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12131081637177691734352213 35540278233919018752985)
              ·
                rfl

theorem cell22_2803185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 10].length) (baseStart_2803185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803185 prefixEnd_2803185 := by exact prefixLift 2803185
  have htrace : WordTrace (prefixWord ++ tailWord_2803185) baseStart_2803185 baseEnd_2803185 := by
    simpa [prefixWord, tailWord_2803185, baseEnd_2803185] using wordTrace_append hprefix tailTrace_2803185
  have hstable : (prefixWord ++ tailWord_2803185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803185).length < 2 ^ (prefixWord ++ tailWord_2803185).sum := by decide
  have hdescent : baseEnd_2803185 < baseStart_2803185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803217 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 5, 3]
def baseStart_2803217 : Nat := 118140960795 + 2803217 * 2 ^ 59
def prefixEnd_2803217 : Nat := 4983230072969 + 3 ^ 40 * 2803217 * 2
def baseEnd_2803217 : Nat := 959598466569776089530497

theorem tailTrace_2803217 : CollatzResearch.WordTrace tailWord_2803217 prefixEnd_2803217 959598466569776089530497 := by
  unfold tailWord_2803217
  simp only [CollatzResearch.WordTrace]
  refine ⟨102241723485431035193367905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68161148990287356795578603 102241723485431035193367905)
  ·
    refine ⟨76681292614073276395025929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102241723485431035193367905 76681292614073276395025929)
    ·
      refine ⟨57510969460554957296269447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76681292614073276395025929 57510969460554957296269447)
      ·
        refine ⟨86266454190832435944404171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57510969460554957296269447 86266454190832435944404171)
        ·
          refine ⟨129399681286248653916606257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86266454190832435944404171 129399681286248653916606257)
          ·
            refine ⟨97049760964686490437454693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129399681286248653916606257 97049760964686490437454693)
            ·
              refine ⟨18196830180878716957022755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97049760964686490437454693 18196830180878716957022755)
              ·
                refine ⟨27295245271318075435534133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18196830180878716957022755 27295245271318075435534133)
                ·
                  refine ⟨2558929244186069572081325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27295245271318075435534133 2558929244186069572081325)
                  ·
                    refine ⟨959598466569776089530497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2558929244186069572081325 959598466569776089530497)
                    ·
                      rfl

theorem cell22_2803217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_2803217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803217 prefixEnd_2803217 := by exact prefixLift 2803217
  have htrace : WordTrace (prefixWord ++ tailWord_2803217) baseStart_2803217 baseEnd_2803217 := by
    simpa [prefixWord, tailWord_2803217, baseEnd_2803217] using wordTrace_append hprefix tailTrace_2803217
  have hstable : (prefixWord ++ tailWord_2803217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803217).length < 2 ^ (prefixWord ++ tailWord_2803217).sum := by decide
  have hdescent : baseEnd_2803217 < baseStart_2803217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803251 : List Nat := [1, 1, 1, 2, 4, 4, 1, 4, 1, 3]
def baseStart_2803251 : Nat := 118140960795 + 2803251 * 2 ^ 59
def prefixEnd_2803251 : Nat := 4983230072969 + 3 ^ 40 * 2803251 * 2
def baseEnd_2803251 : Nat := 959610105464611334180393

theorem tailTrace_2803251 : CollatzResearch.WordTrace tailWord_2803251 prefixEnd_2803251 959610105464611334180393 := by
  unfold tailWord_2803251
  simp only [CollatzResearch.WordTrace]
  refine ⟨102242963567307859000105607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68161975711538572666737071 102242963567307859000105607)
  ·
    refine ⟨153364445350961788500158411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102242963567307859000105607 153364445350961788500158411)
    ·
      refine ⟨230046668026442682750237617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153364445350961788500158411 230046668026442682750237617)
      ·
        refine ⟨172535001019832012062678213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230046668026442682750237617 172535001019832012062678213)
        ·
          refine ⟨32350312691218502261752165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172535001019832012062678213 32350312691218502261752165)
          ·
            refine ⟨6065683629603469174078531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32350312691218502261752165 6065683629603469174078531)
            ·
              refine ⟨9098525444405203761117797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6065683629603469174078531 9098525444405203761117797)
              ·
                refine ⟨1705973520825975705209587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9098525444405203761117797 1705973520825975705209587)
                ·
                  refine ⟨2558960281238963557814381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705973520825975705209587 2558960281238963557814381)
                  ·
                    refine ⟨959610105464611334180393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2558960281238963557814381 959610105464611334180393)
                    ·
                      rfl

theorem cell22_2803251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 1, 3].length) (baseStart_2803251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803251 prefixEnd_2803251 := by exact prefixLift 2803251
  have htrace : WordTrace (prefixWord ++ tailWord_2803251) baseStart_2803251 baseEnd_2803251 := by
    simpa [prefixWord, tailWord_2803251, baseEnd_2803251] using wordTrace_append hprefix tailTrace_2803251
  have hstable : (prefixWord ++ tailWord_2803251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803251).length < 2 ^ (prefixWord ++ tailWord_2803251).sum := by decide
  have hdescent : baseEnd_2803251 < baseStart_2803251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803322 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 6, 4]
def baseStart_2803322 : Nat := 118140960795 + 2803322 * 2 ^ 59
def prefixEnd_2803322 : Nat := 4983230072969 + 3 ^ 40 * 2803322 * 2
def baseEnd_2803322 : Nat := 959634410215590815655175

theorem tailTrace_2803322 : CollatzResearch.WordTrace tailWord_2803322 prefixEnd_2803322 959634410215590815655175 := by
  unfold tailWord_2803322
  simp only [CollatzResearch.WordTrace]
  refine ⟨25561388287512659531485055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68163702100033758750626813 25561388287512659531485055)
  ·
    refine ⟨38342082431268989297227583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25561388287512659531485055 38342082431268989297227583)
    ·
      refine ⟨57513123646903483945841375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38342082431268989297227583 57513123646903483945841375)
      ·
        refine ⟨86269685470355225918762063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57513123646903483945841375 86269685470355225918762063)
        ·
          refine ⟨129404528205532838878143095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86269685470355225918762063 129404528205532838878143095)
          ·
            refine ⟨194106792308299258317214643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129404528205532838878143095 194106792308299258317214643)
            ·
              refine ⟨291160188462448887475821965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194106792308299258317214643 291160188462448887475821965)
              ·
                refine ⟨109185070673418332803433237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291160188462448887475821965 109185070673418332803433237)
                ·
                  refine ⟨5118050187816484350160933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109185070673418332803433237 5118050187816484350160933)
                  ·
                    refine ⟨959634410215590815655175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5118050187816484350160933 959634410215590815655175)
                    ·
                      rfl

theorem cell22_2803322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_2803322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803322 prefixEnd_2803322 := by exact prefixLift 2803322
  have htrace : WordTrace (prefixWord ++ tailWord_2803322) baseStart_2803322 baseEnd_2803322 := by
    simpa [prefixWord, tailWord_2803322, baseEnd_2803322] using wordTrace_append hprefix tailTrace_2803322
  have hstable : (prefixWord ++ tailWord_2803322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803322).length < 2 ^ (prefixWord ++ tailWord_2803322).sum := by decide
  have hdescent : baseEnd_2803322 < baseStart_2803322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803356 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 2, 4]
def baseStart_2803356 : Nat := 118140960795 + 2803356 * 2 ^ 59
def prefixEnd_2803356 : Nat := 4983230072969 + 3 ^ 40 * 2803356 * 2
def baseEnd_2803356 : Nat := 959646049110426060305071

theorem tailTrace_2803356 : CollatzResearch.WordTrace tailWord_2803356 prefixEnd_2803356 959646049110426060305071 := by
  unfold tailWord_2803356
  simp only [CollatzResearch.WordTrace]
  refine ⟨51123396615963730966338961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68164528821284974621785281 51123396615963730966338961)
  ·
    refine ⟨38342547461972798224754221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51123396615963730966338961 38342547461972798224754221)
    ·
      refine ⟨14378455298239799334282833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38342547461972798224754221 14378455298239799334282833)
      ·
        refine ⟨10783841473679849500712125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14378455298239799334282833 10783841473679849500712125)
        ·
          refine ⟨4043940552629943562767047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10783841473679849500712125 4043940552629943562767047)
          ·
            refine ⟨6065910828944915344150571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4043940552629943562767047 6065910828944915344150571)
            ·
              refine ⟨9098866243417373016225857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6065910828944915344150571 9098866243417373016225857)
              ·
                refine ⟨6824149682563029762169393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9098866243417373016225857 6824149682563029762169393)
                ·
                  refine ⟨5118112261922272321627045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6824149682563029762169393 5118112261922272321627045)
                  ·
                    refine ⟨959646049110426060305071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5118112261922272321627045 959646049110426060305071)
                    ·
                      rfl

theorem cell22_2803356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_2803356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803356 prefixEnd_2803356 := by exact prefixLift 2803356
  have htrace : WordTrace (prefixWord ++ tailWord_2803356) baseStart_2803356 baseEnd_2803356 := by
    simpa [prefixWord, tailWord_2803356, baseEnd_2803356] using wordTrace_append hprefix tailTrace_2803356
  have hstable : (prefixWord ++ tailWord_2803356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803356).length < 2 ^ (prefixWord ++ tailWord_2803356).sum := by decide
  have hdescent : baseEnd_2803356 < baseStart_2803356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803397 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 1, 7]
def baseStart_2803397 : Nat := 118140960795 + 2803397 * 2 ^ 59
def prefixEnd_2803397 : Nat := 4983230072969 + 3 ^ 40 * 2803397 * 2
def baseEnd_2803397 : Nat := 959660084248315620029945

theorem tailTrace_2803397 : CollatzResearch.WordTrace tailWord_2803397 prefixEnd_2803397 959660084248315620029945 := by
  unfold tailWord_2803397
  simp only [CollatzResearch.WordTrace]
  refine ⟨102248288624778925934920445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68165525749852617289946963 102248288624778925934920445)
  ·
    refine ⟨38343108234292097225595167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102248288624778925934920445 38343108234292097225595167)
    ·
      refine ⟨57514662351438145838392751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38343108234292097225595167 57514662351438145838392751)
      ·
        refine ⟨86271993527157218757589127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57514662351438145838392751 86271993527157218757589127)
        ·
          refine ⟨129407990290735828136383691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86271993527157218757589127 129407990290735828136383691)
          ·
            refine ⟨194111985436103742204575537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129407990290735828136383691 194111985436103742204575537)
            ·
              refine ⟨145583989077077806653431653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194111985436103742204575537 145583989077077806653431653)
              ·
                refine ⟨27296997951952088747518435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145583989077077806653431653 27296997951952088747518435)
                ·
                  refine ⟨40945496927928133121277653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27296997951952088747518435 40945496927928133121277653)
                  ·
                    refine ⟨959660084248315620029945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40945496927928133121277653 959660084248315620029945)
                    ·
                      rfl

theorem cell22_2803397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_2803397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803397 prefixEnd_2803397 := by exact prefixLift 2803397
  have htrace : WordTrace (prefixWord ++ tailWord_2803397) baseStart_2803397 baseEnd_2803397 := by
    simpa [prefixWord, tailWord_2803397, baseEnd_2803397] using wordTrace_append hprefix tailTrace_2803397
  have hstable : (prefixWord ++ tailWord_2803397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803397).length < 2 ^ (prefixWord ++ tailWord_2803397).sum := by decide
  have hdescent : baseEnd_2803397 < baseStart_2803397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803429 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 5, 4]
def baseStart_2803429 : Nat := 118140960795 + 2803429 * 2 ^ 59
def prefixEnd_2803429 : Nat := 4983230072969 + 3 ^ 40 * 2803429 * 2
def baseEnd_2803429 : Nat := 959671038502278203229847

theorem tailTrace_2803429 : CollatzResearch.WordTrace tailWord_2803429 prefixEnd_2803429 959671038502278203229847 := by
  unfold tailWord_2803429
  simp only [CollatzResearch.WordTrace]
  refine ⟨102249455760662995400085341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68166303840441996933390227 102249455760662995400085341)
  ·
    refine ⟨38343545910248623275032003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102249455760662995400085341 38343545910248623275032003)
    ·
      refine ⟨57515318865372934912548005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38343545910248623275032003 57515318865372934912548005)
      ·
        refine ⟨10784122287257425296102751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57515318865372934912548005 10784122287257425296102751)
        ·
          refine ⟨16176183430886137944154127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10784122287257425296102751 16176183430886137944154127)
          ·
            refine ⟨24264275146329206916231191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16176183430886137944154127 24264275146329206916231191)
            ·
              refine ⟨36396412719493810374346787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24264275146329206916231191 36396412719493810374346787)
              ·
                refine ⟨54594619079240715561520181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36396412719493810374346787 54594619079240715561520181)
                ·
                  refine ⟨5118245538678817083892517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54594619079240715561520181 5118245538678817083892517)
                  ·
                    refine ⟨959671038502278203229847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5118245538678817083892517 959671038502278203229847)
                    ·
                      rfl

theorem cell22_2803429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_2803429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803429 prefixEnd_2803429 := by exact prefixLift 2803429
  have htrace : WordTrace (prefixWord ++ tailWord_2803429) baseStart_2803429 baseEnd_2803429 := by
    simpa [prefixWord, tailWord_2803429, baseEnd_2803429] using wordTrace_append hprefix tailTrace_2803429
  have hstable : (prefixWord ++ tailWord_2803429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803429).length < 2 ^ (prefixWord ++ tailWord_2803429).sum := by decide
  have hdescent : baseEnd_2803429 < baseStart_2803429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803446 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_2803446 : Nat := 118140960795 + 2803446 * 2 ^ 59
def prefixEnd_2803446 : Nat := 4983230072969 + 3 ^ 40 * 2803446 * 2
def baseEnd_2803446 : Nat := 959676857949695825554795

theorem tailTrace_2803446 : CollatzResearch.WordTrace tailWord_2803446 prefixEnd_2803446 959676857949695825554795 := by
  unfold tailWord_2803446
  simp only [CollatzResearch.WordTrace]
  refine ⟨6390629737600087956465887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68166717201067604868969461 6390629737600087956465887)
  ·
    refine ⟨9585944606400131934698831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6390629737600087956465887 9585944606400131934698831)
    ·
      refine ⟨14378916909600197902048247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9585944606400131934698831 14378916909600197902048247)
      ·
        refine ⟨21568375364400296853072371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14378916909600197902048247 21568375364400296853072371)
        ·
          refine ⟨32352563046600445279608557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21568375364400296853072371 32352563046600445279608557)
          ·
            refine ⟨12132211142475166979853209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32352563046600445279608557 12132211142475166979853209)
            ·
              refine ⟨9099158356856375234889907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12132211142475166979853209 9099158356856375234889907)
              ·
                refine ⟨13648737535284562852334861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9099158356856375234889907 13648737535284562852334861)
                ·
                  refine ⟨5118276575731711069625573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13648737535284562852334861 5118276575731711069625573)
                  ·
                    refine ⟨959676857949695825554795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5118276575731711069625573 959676857949695825554795)
                    ·
                      rfl

theorem cell22_2803446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_2803446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803446 prefixEnd_2803446 := by exact prefixLift 2803446
  have htrace : WordTrace (prefixWord ++ tailWord_2803446) baseStart_2803446 baseEnd_2803446 := by
    simpa [prefixWord, tailWord_2803446, baseEnd_2803446] using wordTrace_append hprefix tailTrace_2803446
  have hstable : (prefixWord ++ tailWord_2803446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803446).length < 2 ^ (prefixWord ++ tailWord_2803446).sum := by decide
  have hdescent : baseEnd_2803446 < baseStart_2803446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803459 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 1, 5]
def baseStart_2803459 : Nat := 118140960795 + 2803459 * 2 ^ 59
def prefixEnd_2803459 : Nat := 4983230072969 + 3 ^ 40 * 2803459 * 2
def baseEnd_2803459 : Nat := 959681308115368124979755

theorem tailTrace_2803459 : CollatzResearch.WordTrace tailWord_2803459 prefixEnd_2803459 959681308115368124979755 := by
  unfold tailWord_2803459
  simp only [CollatzResearch.WordTrace]
  refine ⟨102250549950554310523677431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68167033300369540349118287 102250549950554310523677431)
  ·
    refine ⟨153375824925831465785516147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102250549950554310523677431 153375824925831465785516147)
    ·
      refine ⟨230063737388747198678274221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153375824925831465785516147 230063737388747198678274221)
      ·
        refine ⟨86273901520780199504352833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230063737388747198678274221 86273901520780199504352833)
        ·
          refine ⟨64705426140585149628264625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86273901520780199504352833 64705426140585149628264625)
          ·
            refine ⟨48529069605438862221198469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64705426140585149628264625 48529069605438862221198469)
            ·
              refine ⟨9099200551019786666474713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48529069605438862221198469 9099200551019786666474713)
              ·
                refine ⟨6824400413264839999856035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9099200551019786666474713 6824400413264839999856035)
                ·
                  refine ⟨10236600619897259999784053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6824400413264839999856035 10236600619897259999784053)
                  ·
                    refine ⟨959681308115368124979755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10236600619897259999784053 959681308115368124979755)
                    ·
                      rfl

theorem cell22_2803459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 5].length) (baseStart_2803459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803459 prefixEnd_2803459 := by exact prefixLift 2803459
  have htrace : WordTrace (prefixWord ++ tailWord_2803459) baseStart_2803459 baseEnd_2803459 := by
    simpa [prefixWord, tailWord_2803459, baseEnd_2803459] using wordTrace_append hprefix tailTrace_2803459
  have hstable : (prefixWord ++ tailWord_2803459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803459).length < 2 ^ (prefixWord ++ tailWord_2803459).sum := by decide
  have hdescent : baseEnd_2803459 < baseStart_2803459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803463 : List Nat := [1, 1, 4, 4, 2, 1, 1, 3, 1, 4]
def baseStart_2803463 : Nat := 118140960795 + 2803463 * 2 ^ 59
def prefixEnd_2803463 : Nat := 4983230072969 + 3 ^ 40 * 2803463 * 2
def baseEnd_2803463 : Nat := 959682677397113447879743

theorem tailTrace_2803463 : CollatzResearch.WordTrace tailWord_2803463 prefixEnd_2803463 959682677397113447879743 := by
  unfold tailWord_2803463
  simp only [CollatzResearch.WordTrace]
  refine ⟨102250695842539819206823043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68167130561693212804548695 102250695842539819206823043)
  ·
    refine ⟨153376043763809728810234565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102250695842539819206823043 153376043763809728810234565)
    ·
      refine ⟨28758008205714324151918981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153376043763809728810234565 28758008205714324151918981)
      ·
        refine ⟨5392126538571435778484809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28758008205714324151918981 5392126538571435778484809)
        ·
          refine ⟨4044094903928576833863607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5392126538571435778484809 4044094903928576833863607)
          ·
            refine ⟨6066142355892865250795411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044094903928576833863607 6066142355892865250795411)
            ·
              refine ⟨9099213533839297876193117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6066142355892865250795411 9099213533839297876193117)
              ·
                refine ⟨3412205075189736703572419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9099213533839297876193117 3412205075189736703572419)
                ·
                  refine ⟨5118307612784605055358629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3412205075189736703572419 5118307612784605055358629)
                  ·
                    refine ⟨959682677397113447879743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5118307612784605055358629 959682677397113447879743)
                    ·
                      rfl

theorem cell22_2803463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_2803463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803463 prefixEnd_2803463 := by exact prefixLift 2803463
  have htrace : WordTrace (prefixWord ++ tailWord_2803463) baseStart_2803463 baseEnd_2803463 := by
    simpa [prefixWord, tailWord_2803463, baseEnd_2803463] using wordTrace_append hprefix tailTrace_2803463
  have hstable : (prefixWord ++ tailWord_2803463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803463).length < 2 ^ (prefixWord ++ tailWord_2803463).sum := by decide
  have hdescent : baseEnd_2803463 < baseStart_2803463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803506 : List Nat := [3, 2, 1, 1, 3, 2, 4, 6]
def baseStart_2803506 : Nat := 118140960795 + 2803506 * 2 ^ 59
def prefixEnd_2803506 : Nat := 4983230072969 + 3 ^ 40 * 2803506 * 2
def baseEnd_2803506 : Nat := 106633044130652852117179

theorem tailTrace_2803506 : CollatzResearch.WordTrace tailWord_2803506 prefixEnd_2803506 106633044130652852117179 := by
  unfold tailWord_2803506
  simp only [CollatzResearch.WordTrace]
  refine ⟨25563066045346009387659593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68168176120922691700425581 25563066045346009387659593)
  ·
    refine ⟨19172299534009507040744695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25563066045346009387659593 19172299534009507040744695)
    ·
      refine ⟨28758449301014260561117043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19172299534009507040744695 28758449301014260561117043)
      ·
        refine ⟨43137673951521390841675565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28758449301014260561117043 43137673951521390841675565)
        ·
          refine ⟨16176627731820521565628337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43137673951521390841675565 16176627731820521565628337)
          ·
            refine ⟨12132470798865391174221253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16176627731820521565628337 12132470798865391174221253)
            ·
              refine ⟨2274838274787260845166485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12132470798865391174221253 2274838274787260845166485)
              ·
                refine ⟨106633044130652852117179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2274838274787260845166485 106633044130652852117179)
                ·
                  rfl

theorem cell22_2803506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 6].length) (baseStart_2803506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803506 prefixEnd_2803506 := by exact prefixLift 2803506
  have htrace : WordTrace (prefixWord ++ tailWord_2803506) baseStart_2803506 baseEnd_2803506 := by
    simpa [prefixWord, tailWord_2803506, baseEnd_2803506] using wordTrace_append hprefix tailTrace_2803506
  have hstable : (prefixWord ++ tailWord_2803506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803506).length < 2 ^ (prefixWord ++ tailWord_2803506).sum := by decide
  have hdescent : baseEnd_2803506 < baseStart_2803506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803538 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 3, 3]
def baseStart_2803538 : Nat := 118140960795 + 2803538 * 2 ^ 59
def prefixEnd_2803538 : Nat := 4983230072969 + 3 ^ 40 * 2803538 * 2
def baseEnd_2803538 : Nat := 959708351429838252254513

theorem tailTrace_2803538 : CollatzResearch.WordTrace tailWord_2803538 prefixEnd_2803538 959708351429838252254513 := by
  unfold tailWord_2803538
  simp only [CollatzResearch.WordTrace]
  refine ⟨25563357829317026753950817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68168954211512071343868845 25563357829317026753950817)
  ·
    refine ⟨19172518371987770065463113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25563357829317026753950817 19172518371987770065463113)
    ·
      refine ⟨14379388778990827549097335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19172518371987770065463113 14379388778990827549097335)
      ·
        refine ⟨21569083168486241323646003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14379388778990827549097335 21569083168486241323646003)
        ·
          refine ⟨32353624752729361985469005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21569083168486241323646003 32353624752729361985469005)
          ·
            refine ⟨12132609282273510744550877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32353624752729361985469005 12132609282273510744550877)
            ·
              refine ⟨4549728480852566529206579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12132609282273510744550877 4549728480852566529206579)
              ·
                refine ⟨6824592721278849793809869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4549728480852566529206579 6824592721278849793809869)
                ·
                  refine ⟨2559222270479568672678701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6824592721278849793809869 2559222270479568672678701)
                  ·
                    refine ⟨959708351429838252254513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2559222270479568672678701 959708351429838252254513)
                    ·
                      rfl

theorem cell22_2803538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_2803538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803538 prefixEnd_2803538 := by exact prefixLift 2803538
  have htrace : WordTrace (prefixWord ++ tailWord_2803538) baseStart_2803538 baseEnd_2803538 := by
    simpa [prefixWord, tailWord_2803538, baseEnd_2803538] using wordTrace_append hprefix tailTrace_2803538
  have hstable : (prefixWord ++ tailWord_2803538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803538).length < 2 ^ (prefixWord ++ tailWord_2803538).sum := by decide
  have hdescent : baseEnd_2803538 < baseStart_2803538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803551 : List Nat := [1, 1, 2, 3, 1, 5, 1, 3, 5]
def baseStart_2803551 : Nat := 118140960795 + 2803551 * 2 ^ 59
def prefixEnd_2803551 : Nat := 4983230072969 + 3 ^ 40 * 2803551 * 2
def baseEnd_2803551 : Nat := 319904267198503517226491

theorem tailTrace_2803551 : CollatzResearch.WordTrace tailWord_2803551 prefixEnd_2803551 319904267198503517226491 := by
  unfold tailWord_2803551
  simp only [CollatzResearch.WordTrace]
  refine ⟨102253905466221010236026507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68169270310814006824017671 102253905466221010236026507)
  ·
    refine ⟨153380858199331515354039761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102253905466221010236026507 153380858199331515354039761)
    ·
      refine ⟨115035643649498636515529821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153380858199331515354039761 115035643649498636515529821)
      ·
        refine ⟨43138366368561988693323683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115035643649498636515529821 43138366368561988693323683)
        ·
          refine ⟨64707549552842983039985525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43138366368561988693323683 64707549552842983039985525)
          ·
            refine ⟨6066332770579029659998643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64707549552842983039985525 6066332770579029659998643)
            ·
              refine ⟨9099499155868544489997965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6066332770579029659998643 9099499155868544489997965)
              ·
                refine ⟨3412312183450704183749237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9099499155868544489997965 3412312183450704183749237)
                ·
                  refine ⟨319904267198503517226491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3412312183450704183749237 319904267198503517226491)
                  ·
                    rfl

theorem cell22_2803551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 5].length) (baseStart_2803551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803551 prefixEnd_2803551 := by exact prefixLift 2803551
  have htrace : WordTrace (prefixWord ++ tailWord_2803551) baseStart_2803551 baseEnd_2803551 := by
    simpa [prefixWord, tailWord_2803551, baseEnd_2803551] using wordTrace_append hprefix tailTrace_2803551
  have hstable : (prefixWord ++ tailWord_2803551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803551).length < 2 ^ (prefixWord ++ tailWord_2803551).sum := by decide
  have hdescent : baseEnd_2803551 < baseStart_2803551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803585 : List Nat := [1, 2, 4, 4, 1, 1, 2, 2, 5]
def baseStart_2803585 : Nat := 118140960795 + 2803585 * 2 ^ 59
def prefixEnd_2803585 : Nat := 4983230072969 + 3 ^ 40 * 2803585 * 2
def baseEnd_2803585 : Nat := 319908146830115265443123

theorem tailTrace_2803585 : CollatzResearch.WordTrace tailWord_2803585 prefixEnd_2803585 319908146830115265443123 := by
  unfold tailWord_2803585
  simp only [CollatzResearch.WordTrace]
  refine ⟨102255145548097834042764209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68170097032065222695176139 102255145548097834042764209)
  ·
    refine ⟨76691359161073375532073157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102255145548097834042764209 76691359161073375532073157)
    ·
      refine ⟨14379629842701257912263717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76691359161073375532073157 14379629842701257912263717)
      ·
        refine ⟨2696180595506485858549447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14379629842701257912263717 2696180595506485858549447)
        ·
          refine ⟨4044270893259728787824171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2696180595506485858549447 4044270893259728787824171)
          ·
            refine ⟨6066406339889593181736257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044270893259728787824171 6066406339889593181736257)
            ·
              refine ⟨4549804754917194886302193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6066406339889593181736257 4549804754917194886302193)
              ·
                refine ⟨3412353566187896164726645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4549804754917194886302193 3412353566187896164726645)
                ·
                  refine ⟨319908146830115265443123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3412353566187896164726645 319908146830115265443123)
                  ·
                    rfl

theorem cell22_2803585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 5].length) (baseStart_2803585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803585 prefixEnd_2803585 := by exact prefixLift 2803585
  have htrace : WordTrace (prefixWord ++ tailWord_2803585) baseStart_2803585 baseEnd_2803585 := by
    simpa [prefixWord, tailWord_2803585, baseEnd_2803585] using wordTrace_append hprefix tailTrace_2803585
  have hstable : (prefixWord ++ tailWord_2803585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803585).length < 2 ^ (prefixWord ++ tailWord_2803585).sum := by decide
  have hdescent : baseEnd_2803585 < baseStart_2803585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803645 : List Nat := [1, 4, 1, 2, 3, 1, 3, 2, 2, 3]
def baseStart_2803645 : Nat := 118140960795 + 2803645 * 2 ^ 59
def prefixEnd_2803645 : Nat := 4983230072969 + 3 ^ 40 * 2803645 * 2
def baseEnd_2803645 : Nat := 959744979716525639829185

theorem tailTrace_2803645 : CollatzResearch.WordTrace tailWord_2803645 prefixEnd_2803645 959744979716525639829185 := by
  unfold tailWord_2803645
  simp only [CollatzResearch.WordTrace]
  refine ⟨102257333927880464289948389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68171555951920309526632259 102257333927880464289948389)
  ·
    refine ⟨19173250111477587054365323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102257333927880464289948389 19173250111477587054365323)
    ·
      refine ⟨28759875167216380581547985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19173250111477587054365323 28759875167216380581547985)
      ·
        refine ⟨21569906375412285436160989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28759875167216380581547985 21569906375412285436160989)
        ·
          refine ⟨8088714890779607038560371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21569906375412285436160989 8088714890779607038560371)
          ·
            refine ⟨12133072336169410557840557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8088714890779607038560371 12133072336169410557840557)
            ·
              refine ⟨4549902126063528959190209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12133072336169410557840557 4549902126063528959190209)
              ·
                refine ⟨3412426594547646719392657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4549902126063528959190209 3412426594547646719392657)
                ·
                  refine ⟨2559319945910735039544493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3412426594547646719392657 2559319945910735039544493)
                  ·
                    refine ⟨959744979716525639829185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2559319945910735039544493 959744979716525639829185)
                    ·
                      rfl

theorem cell22_2803645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_2803645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803645 prefixEnd_2803645 := by exact prefixLift 2803645
  have htrace : WordTrace (prefixWord ++ tailWord_2803645) baseStart_2803645 baseEnd_2803645 := by
    simpa [prefixWord, tailWord_2803645, baseEnd_2803645] using wordTrace_append hprefix tailTrace_2803645
  have hstable : (prefixWord ++ tailWord_2803645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803645).length < 2 ^ (prefixWord ++ tailWord_2803645).sum := by decide
  have hdescent : baseEnd_2803645 < baseStart_2803645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803731 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 6]
def baseStart_2803731 : Nat := 118140960795 + 2803731 * 2 ^ 59
def prefixEnd_2803731 : Nat := 4983230072969 + 3 ^ 40 * 2803731 * 2
def baseEnd_2803731 : Nat := 319924806424683360726307

theorem tailTrace_2803731 : CollatzResearch.WordTrace tailWord_2803731 prefixEnd_2803731 319924806424683360726307 := by
  unfold tailWord_2803731
  simp only [CollatzResearch.WordTrace]
  refine ⟨102260470605568900977579047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68173647070379267318386031 102260470605568900977579047)
  ·
    refine ⟨153390705908353351466368571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102260470605568900977579047 153390705908353351466368571)
    ·
      refine ⟨230086058862530027199552857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153390705908353351466368571 230086058862530027199552857)
      ·
        refine ⟨172564544146897520399664643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230086058862530027199552857 172564544146897520399664643)
        ·
          refine ⟨258846816220346280599496965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172564544146897520399664643 258846816220346280599496965)
          ·
            refine ⟨48533778041314927612405681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258846816220346280599496965 48533778041314927612405681)
            ·
              refine ⟨36400333530986195709304261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48533778041314927612405681 36400333530986195709304261)
              ·
                refine ⟨6825062537059911695494549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36400333530986195709304261 6825062537059911695494549)
                ·
                  refine ⟨319924806424683360726307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6825062537059911695494549 319924806424683360726307)
                  ·
                    rfl

theorem cell22_2803731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 6].length) (baseStart_2803731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803731 prefixEnd_2803731 := by exact prefixLift 2803731
  have htrace : WordTrace (prefixWord ++ tailWord_2803731) baseStart_2803731 baseEnd_2803731 := by
    simpa [prefixWord, tailWord_2803731, baseEnd_2803731] using wordTrace_append hprefix tailTrace_2803731
  have hstable : (prefixWord ++ tailWord_2803731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803731).length < 2 ^ (prefixWord ++ tailWord_2803731).sum := by decide
  have hdescent : baseEnd_2803731 < baseStart_2803731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803763 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 4, 3]
def baseStart_2803763 : Nat := 118140960795 + 2803763 * 2 ^ 59
def prefixEnd_2803763 : Nat := 4983230072969 + 3 ^ 40 * 2803763 * 2
def baseEnd_2803763 : Nat := 959785373528012665378823

theorem tailTrace_2803763 : CollatzResearch.WordTrace tailWord_2803763 prefixEnd_2803763 959785373528012665378823 := by
  unfold tailWord_2803763
  simp only [CollatzResearch.WordTrace]
  refine ⟨102261637741452970442743943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68174425160968646961829295 102261637741452970442743943)
  ·
    refine ⟨153392456612179455664115915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102261637741452970442743943 153392456612179455664115915)
    ·
      refine ⟨230088684918269183496173873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153392456612179455664115915 230088684918269183496173873)
      ·
        refine ⟨172566513688701887622130405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230088684918269183496173873 172566513688701887622130405)
        ·
          refine ⟨32356221316631603929149451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172566513688701887622130405 32356221316631603929149451)
          ·
            refine ⟨48534331974947405893724177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32356221316631603929149451 48534331974947405893724177)
            ·
              refine ⟨36400748981210554420293133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48534331974947405893724177 36400748981210554420293133)
              ·
                refine ⟨13650280867953957907609925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36400748981210554420293133 13650280867953957907609925)
                ·
                  refine ⟨2559427662741367107676861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13650280867953957907609925 2559427662741367107676861)
                  ·
                    refine ⟨959785373528012665378823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2559427662741367107676861 959785373528012665378823)
                    ·
                      rfl

theorem cell22_2803763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 3].length) (baseStart_2803763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803763 prefixEnd_2803763 := by exact prefixLift 2803763
  have htrace : WordTrace (prefixWord ++ tailWord_2803763) baseStart_2803763 baseEnd_2803763 := by
    simpa [prefixWord, tailWord_2803763, baseEnd_2803763] using wordTrace_append hprefix tailTrace_2803763
  have hstable : (prefixWord ++ tailWord_2803763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803763).length < 2 ^ (prefixWord ++ tailWord_2803763).sum := by decide
  have hdescent : baseEnd_2803763 < baseStart_2803763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803791 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 2, 7]
def baseStart_2803791 : Nat := 118140960795 + 2803791 * 2 ^ 59
def prefixEnd_2803791 : Nat := 4983230072969 + 3 ^ 40 * 2803791 * 2
def baseEnd_2803791 : Nat := 959794958500229925678737

theorem tailTrace_2803791 : CollatzResearch.WordTrace tailWord_2803791 prefixEnd_2803791 959794958500229925678737 := by
  unfold tailWord_2803791
  simp only [CollatzResearch.WordTrace]
  refine ⟨102262658985351531224763227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68175105990234354149842151 102262658985351531224763227)
  ·
    refine ⟨153393988478027296837144841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102262658985351531224763227 153393988478027296837144841)
    ·
      refine ⟨115045491358520472627858631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153393988478027296837144841 115045491358520472627858631)
      ·
        refine ⟨172568237037780708941787947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115045491358520472627858631 172568237037780708941787947)
        ·
          refine ⟨258852355556671063412681921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172568237037780708941787947 258852355556671063412681921)
          ·
            refine ⟨194139266667503297559511441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258852355556671063412681921 194139266667503297559511441)
            ·
              refine ⟨145604450000627473169633581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194139266667503297559511441 145604450000627473169633581)
              ·
                refine ⟨54601668750235302438612593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145604450000627473169633581 54601668750235302438612593)
                ·
                  refine ⟨40951251562676476828959445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54601668750235302438612593 40951251562676476828959445)
                  ·
                    refine ⟨959794958500229925678737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40951251562676476828959445 959794958500229925678737)
                    ·
                      rfl

theorem cell22_2803791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_2803791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803791 prefixEnd_2803791 := by exact prefixLift 2803791
  have htrace : WordTrace (prefixWord ++ tailWord_2803791) baseStart_2803791 baseEnd_2803791 := by
    simpa [prefixWord, tailWord_2803791, baseEnd_2803791] using wordTrace_append hprefix tailTrace_2803791
  have hstable : (prefixWord ++ tailWord_2803791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803791).length < 2 ^ (prefixWord ++ tailWord_2803791).sum := by decide
  have hdescent : baseEnd_2803791 < baseStart_2803791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803810 : List Nat := [3, 3, 2, 2, 2, 1, 9]
def baseStart_2803810 : Nat := 118140960795 + 2803810 * 2 ^ 59
def prefixEnd_2803810 : Nat := 4983230072969 + 3 ^ 40 * 2803810 * 2
def baseEnd_2803810 : Nat := 35548202318093341090877

theorem tailTrace_2803810 : CollatzResearch.WordTrace tailWord_2803810 prefixEnd_2803810 35548202318093341090877 := by
  unfold tailWord_2803810
  simp only [CollatzResearch.WordTrace]
  refine ⟨25565837993070674367426221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68175567981521798313136589 25565837993070674367426221)
  ·
    refine ⟨9587189247401502887784833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25565837993070674367426221 9587189247401502887784833)
    ·
      refine ⟨7190391935551127165838625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9587189247401502887784833 7190391935551127165838625)
      ·
        refine ⟨5392793951663345374378969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7190391935551127165838625 5392793951663345374378969)
        ·
          refine ⟨4044595463747509030784227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5392793951663345374378969 4044595463747509030784227)
          ·
            refine ⟨6066893195621263546176341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044595463747509030784227 6066893195621263546176341)
            ·
              refine ⟨35548202318093341090877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6066893195621263546176341 35548202318093341090877)
              ·
                rfl

theorem cell22_2803810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 9].length) (baseStart_2803810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803810 prefixEnd_2803810 := by exact prefixLift 2803810
  have htrace : WordTrace (prefixWord ++ tailWord_2803810) baseStart_2803810 baseEnd_2803810 := by
    simpa [prefixWord, tailWord_2803810, baseEnd_2803810] using wordTrace_append hprefix tailTrace_2803810
  have hstable : (prefixWord ++ tailWord_2803810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803810).length < 2 ^ (prefixWord ++ tailWord_2803810).sum := by decide
  have hdescent : baseEnd_2803810 < baseStart_2803810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803825 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 3, 3]
def baseStart_2803825 : Nat := 118140960795 + 2803825 * 2 ^ 59
def prefixEnd_2803825 : Nat := 4983230072969 + 3 ^ 40 * 2803825 * 2
def baseEnd_2803825 : Nat := 959806597395065170328633

theorem tailTrace_2803825 : CollatzResearch.WordTrace tailWord_2803825 prefixEnd_2803825 959806597395065170328633 := by
  unfold tailWord_2803825
  simp only [CollatzResearch.WordTrace]
  refine ⟨102263899067228355031500929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68175932711485570021000619 102263899067228355031500929)
  ·
    refine ⟨76697924300421266273625697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102263899067228355031500929 76697924300421266273625697)
    ·
      refine ⟨57523443225315949705219273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76697924300421266273625697 57523443225315949705219273)
      ·
        refine ⟨43142582418986962278914455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57523443225315949705219273 43142582418986962278914455)
        ·
          refine ⟨64713873628480443418371683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43142582418986962278914455 64713873628480443418371683)
          ·
            refine ⟨97070810442720665127557525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64713873628480443418371683 97070810442720665127557525)
            ·
              refine ⟨4550194239502531177854259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97070810442720665127557525 4550194239502531177854259)
              ·
                refine ⟨6825291359253796766781389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4550194239502531177854259 6825291359253796766781389)
                ·
                  refine ⟨2559484259720173787543021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6825291359253796766781389 2559484259720173787543021)
                  ·
                    refine ⟨959806597395065170328633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2559484259720173787543021 959806597395065170328633)
                    ·
                      rfl

theorem cell22_2803825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_2803825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803825 prefixEnd_2803825 := by exact prefixLift 2803825
  have htrace : WordTrace (prefixWord ++ tailWord_2803825) baseStart_2803825 baseEnd_2803825 := by
    simpa [prefixWord, tailWord_2803825, baseEnd_2803825] using wordTrace_append hprefix tailTrace_2803825
  have hstable : (prefixWord ++ tailWord_2803825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803825).length < 2 ^ (prefixWord ++ tailWord_2803825).sum := by decide
  have hdescent : baseEnd_2803825 < baseStart_2803825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803876 : List Nat := [2, 3, 1, 2, 4, 1, 3, 2, 1, 3]
def baseStart_2803876 : Nat := 118140960795 + 2803876 * 2 ^ 59
def prefixEnd_2803876 : Nat := 4983230072969 + 3 ^ 40 * 2803876 * 2
def baseEnd_2803876 : Nat := 959824055737318037303477

theorem tailTrace_2803876 : CollatzResearch.WordTrace tailWord_2803876 prefixEnd_2803876 959824055737318037303477 := by
  unfold tailWord_2803876
  simp only [CollatzResearch.WordTrace]
  refine ⟨51132879595021795370803741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68177172793362393827738321 51132879595021795370803741)
  ·
    refine ⟨19174829848133173264051403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51132879595021795370803741 19174829848133173264051403)
    ·
      refine ⟨28762244772199759896077105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19174829848133173264051403 28762244772199759896077105)
      ·
        refine ⟨21571683579149819922057829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28762244772199759896077105 21571683579149819922057829)
        ·
          refine ⟨4044690671090591235385843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21571683579149819922057829 4044690671090591235385843)
          ·
            refine ⟨6067036006635886853078765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044690671090591235385843 6067036006635886853078765)
            ·
              refine ⟨2275138502488457569904537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6067036006635886853078765 2275138502488457569904537)
              ·
                refine ⟨1706353876866343177428403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2275138502488457569904537 1706353876866343177428403)
                ·
                  refine ⟨2559530815299514766142605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1706353876866343177428403 2559530815299514766142605)
                  ·
                    refine ⟨959824055737318037303477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2559530815299514766142605 959824055737318037303477)
                    ·
                      rfl

theorem cell22_2803876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_2803876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803876 prefixEnd_2803876 := by exact prefixLift 2803876
  have htrace : WordTrace (prefixWord ++ tailWord_2803876) baseStart_2803876 baseEnd_2803876 := by
    simpa [prefixWord, tailWord_2803876, baseEnd_2803876] using wordTrace_append hprefix tailTrace_2803876
  have hstable : (prefixWord ++ tailWord_2803876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803876).length < 2 ^ (prefixWord ++ tailWord_2803876).sum := by decide
  have hdescent : baseEnd_2803876 < baseStart_2803876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803889 : List Nat := [1, 2, 2, 5, 2, 2, 2, 1, 5]
def baseStart_2803889 : Nat := 118140960795 + 2803889 * 2 ^ 59
def prefixEnd_2803889 : Nat := 4983230072969 + 3 ^ 40 * 2803889 * 2
def baseEnd_2803889 : Nat := 319942835300996778909479

theorem tailTrace_2803889 : CollatzResearch.WordTrace tailWord_2803889 prefixEnd_2803889 319942835300996778909479 := by
  unfold tailWord_2803889
  simp only [CollatzResearch.WordTrace]
  refine ⟨102266233338996493961830721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68177488892664329307887147 102266233338996493961830721)
  ·
    refine ⟨76699675004247370471373041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102266233338996493961830721 76699675004247370471373041)
    ·
      refine ⟨57524756253185527853529781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76699675004247370471373041 57524756253185527853529781)
      ·
        refine ⟨5392945898736143236268417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57524756253185527853529781 5392945898736143236268417)
        ·
          refine ⟨4044709424052107427201313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5392945898736143236268417 4044709424052107427201313)
          ·
            refine ⟨3033532068039080570400985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4044709424052107427201313 3033532068039080570400985)
            ·
              refine ⟨2275149051029310427800739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3033532068039080570400985 2275149051029310427800739)
              ·
                refine ⟨3412723576543965641701109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2275149051029310427800739 3412723576543965641701109)
                ·
                  refine ⟨319942835300996778909479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3412723576543965641701109 319942835300996778909479)
                  ·
                    rfl

theorem cell22_2803889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 5].length) (baseStart_2803889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803889 prefixEnd_2803889 := by exact prefixLift 2803889
  have htrace : WordTrace (prefixWord ++ tailWord_2803889) baseStart_2803889 baseEnd_2803889 := by
    simpa [prefixWord, tailWord_2803889, baseEnd_2803889] using wordTrace_append hprefix tailTrace_2803889
  have hstable : (prefixWord ++ tailWord_2803889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803889).length < 2 ^ (prefixWord ++ tailWord_2803889).sum := by decide
  have hdescent : baseEnd_2803889 < baseStart_2803889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803902 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_2803902 : Nat := 118140960795 + 2803902 * 2 ^ 59
def prefixEnd_2803902 : Nat := 4983230072969 + 3 ^ 40 * 2803902 * 2
def baseEnd_2803902 : Nat := 959832956068662636153397

theorem tailTrace_2803902 : CollatzResearch.WordTrace tailWord_2803902 prefixEnd_2803902 959832956068662636153397 := by
  unfold tailWord_2803902
  simp only [CollatzResearch.WordTrace]
  refine ⟨12783338435993674647756745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68177804991966264788035973 12783338435993674647756745)
  ·
    refine ⟨9587503826995255985817559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12783338435993674647756745 9587503826995255985817559)
    ·
      refine ⟨14381255740492883978726339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9587503826995255985817559 14381255740492883978726339)
      ·
        refine ⟨21571883610739325968089509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14381255740492883978726339 21571883610739325968089509)
        ·
          refine ⟨4044728177013623619016783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21571883610739325968089509 4044728177013623619016783)
          ·
            refine ⟨6067092265520435428525175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044728177013623619016783 6067092265520435428525175)
            ·
              refine ⟨9100638398280653142787763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6067092265520435428525175 9100638398280653142787763)
              ·
                refine ⟨13650957597420979714181645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9100638398280653142787763 13650957597420979714181645)
                ·
                  refine ⟨5119109099032867392818117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13650957597420979714181645 5119109099032867392818117)
                  ·
                    refine ⟨959832956068662636153397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5119109099032867392818117 959832956068662636153397)
                    ·
                      rfl

theorem cell22_2803902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_2803902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803902 prefixEnd_2803902 := by exact prefixLift 2803902
  have htrace : WordTrace (prefixWord ++ tailWord_2803902) baseStart_2803902 baseEnd_2803902 := by
    simpa [prefixWord, tailWord_2803902, baseEnd_2803902] using wordTrace_append hprefix tailTrace_2803902
  have hstable : (prefixWord ++ tailWord_2803902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803902).length < 2 ^ (prefixWord ++ tailWord_2803902).sum := by decide
  have hdescent : baseEnd_2803902 < baseStart_2803902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803928 : List Nat := [2, 1, 2, 2, 4, 11]
def baseStart_2803928 : Nat := 118140960795 + 2803928 * 2 ^ 59
def prefixEnd_2803928 : Nat := 4983230072969 + 3 ^ 40 * 2803928 * 2
def baseEnd_2803928 : Nat := 11849899461728484382757

theorem tailTrace_2803928 : CollatzResearch.WordTrace tailWord_2803928 prefixEnd_2803928 11849899461728484382757 := by
  unfold tailWord_2803928
  simp only [CollatzResearch.WordTrace]
  refine ⟨51133827892927601811250219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68178437190570135748333625 51133827892927601811250219)
  ·
    refine ⟨76700741839391402716875329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51133827892927601811250219 76700741839391402716875329)
    ·
      refine ⟨57525556379543552037656497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76700741839391402716875329 57525556379543552037656497)
      ·
        refine ⟨43144167284657664028242373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57525556379543552037656497 43144167284657664028242373)
        ·
          refine ⟨8089531365873312005295445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43144167284657664028242373 8089531365873312005295445)
          ·
            refine ⟨11849899461728484382757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8089531365873312005295445 11849899461728484382757)
            ·
              rfl

theorem cell22_2803928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 11].length) (baseStart_2803928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803928 prefixEnd_2803928 := by exact prefixLift 2803928
  have htrace : WordTrace (prefixWord ++ tailWord_2803928) baseStart_2803928 baseEnd_2803928 := by
    simpa [prefixWord, tailWord_2803928, baseEnd_2803928] using wordTrace_append hprefix tailTrace_2803928
  have hstable : (prefixWord ++ tailWord_2803928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803928).length < 2 ^ (prefixWord ++ tailWord_2803928).sum := by decide
  have hdescent : baseEnd_2803928 < baseStart_2803928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803930 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 2, 4]
def baseStart_2803930 : Nat := 118140960795 + 2803930 * 2 ^ 59
def prefixEnd_2803930 : Nat := 4983230072969 + 3 ^ 40 * 2803930 * 2
def baseEnd_2803930 : Nat := 959842541040879896453311

theorem tailTrace_2803930 : CollatzResearch.WordTrace tailWord_2803930 prefixEnd_2803930 959842541040879896453311 := by
  unfold tailWord_2803930
  simp only [CollatzResearch.WordTrace]
  refine ⟨25566932182961989491018311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68178485821231971976048829 25566932182961989491018311)
  ·
    refine ⟨38350398274442984236527467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25566932182961989491018311 38350398274442984236527467)
    ·
      refine ⟨57525597411664476354791201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38350398274442984236527467 57525597411664476354791201)
      ·
        refine ⟨43144198058748357266093401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57525597411664476354791201 43144198058748357266093401)
        ·
          refine ⟨32358148544061267949570051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43144198058748357266093401 32358148544061267949570051)
          ·
            refine ⟨48537222816091901924355077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32358148544061267949570051 48537222816091901924355077)
            ·
              refine ⟨9100729278017231610816577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48537222816091901924355077 9100729278017231610816577)
              ·
                refine ⟨6825546958512923708112433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9100729278017231610816577 6825546958512923708112433)
                ·
                  refine ⟨5119160218884692781084325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6825546958512923708112433 5119160218884692781084325)
                  ·
                    refine ⟨959842541040879896453311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5119160218884692781084325 959842541040879896453311)
                    ·
                      rfl

theorem cell22_2803930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_2803930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803930 prefixEnd_2803930 := by exact prefixLift 2803930
  have htrace : WordTrace (prefixWord ++ tailWord_2803930) baseStart_2803930 baseEnd_2803930 := by
    simpa [prefixWord, tailWord_2803930, baseEnd_2803930] using wordTrace_append hprefix tailTrace_2803930
  have hstable : (prefixWord ++ tailWord_2803930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803930).length < 2 ^ (prefixWord ++ tailWord_2803930).sum := by decide
  have hdescent : baseEnd_2803930 < baseStart_2803930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803994 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 3, 3]
def baseStart_2803994 : Nat := 118140960795 + 2803994 * 2 ^ 59
def prefixEnd_2803994 : Nat := 4983230072969 + 3 ^ 40 * 2803994 * 2
def baseEnd_2803994 : Nat := 959864449548805062853115

theorem tailTrace_2803994 : CollatzResearch.WordTrace tailWord_2803994 prefixEnd_2803994 959864449548805062853115 := by
  unfold tailWord_2803994
  simp only [CollatzResearch.WordTrace]
  refine ⟨25567515750904024223600759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68180042002410731262935357 25567515750904024223600759)
  ·
    refine ⟨38351273626356036335401139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25567515750904024223600759 38351273626356036335401139)
    ·
      refine ⟨57526910439534054503101709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38351273626356036335401139 57526910439534054503101709)
      ·
        refine ⟨21572591414825270438663141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57526910439534054503101709 21572591414825270438663141)
        ·
          refine ⟨4044860890279738207249339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21572591414825270438663141 4044860890279738207249339)
          ·
            refine ⟨6067291335419607310874009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044860890279738207249339 6067291335419607310874009)
            ·
              refine ⟨4550468501564705483155507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6067291335419607310874009 4550468501564705483155507)
              ·
                refine ⟨6825702752347058224733261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4550468501564705483155507 6825702752347058224733261)
                ·
                  refine ⟨2559638532130146834274973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6825702752347058224733261 2559638532130146834274973)
                  ·
                    refine ⟨959864449548805062853115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2559638532130146834274973 959864449548805062853115)
                    ·
                      rfl

theorem cell22_2803994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_2803994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2803994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2803994 prefixEnd_2803994 := by exact prefixLift 2803994
  have htrace : WordTrace (prefixWord ++ tailWord_2803994) baseStart_2803994 baseEnd_2803994 := by
    simpa [prefixWord, tailWord_2803994, baseEnd_2803994] using wordTrace_append hprefix tailTrace_2803994
  have hstable : (prefixWord ++ tailWord_2803994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803994).length < 2 ^ (prefixWord ++ tailWord_2803994).sum := by decide
  have hdescent : baseEnd_2803994 < baseStart_2803994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804052 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 6]
def baseStart_2804052 : Nat := 118140960795 + 2804052 * 2 ^ 59
def prefixEnd_2804052 : Nat := 4983230072969 + 3 ^ 40 * 2804052 * 2
def baseEnd_2804052 : Nat := 319961434711370748300979

theorem tailTrace_2804052 : CollatzResearch.WordTrace tailWord_2804052 prefixEnd_2804052 319961434711370748300979 := by
  unfold tailWord_2804052
  simp only [CollatzResearch.WordTrace]
  refine ⟨51136089218702986400007205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68181452291603981866676273 51136089218702986400007205)
  ·
    refine ⟨9588016728506809950001351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51136089218702986400007205 9588016728506809950001351)
    ·
      refine ⟨14382025092760214925002027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9588016728506809950001351 14382025092760214925002027)
      ·
        refine ⟨21573037639140322387503041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14382025092760214925002027 21573037639140322387503041)
        ·
          refine ⟨16179778229355241790627281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21573037639140322387503041 16179778229355241790627281)
          ·
            refine ⟨12134833672016431342970461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16179778229355241790627281 12134833672016431342970461)
            ·
              refine ⟨4550562627006161753613923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12134833672016431342970461 4550562627006161753613923)
              ·
                refine ⟨6825843940509242630420885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4550562627006161753613923 6825843940509242630420885)
                ·
                  refine ⟨319961434711370748300979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6825843940509242630420885 319961434711370748300979)
                  ·
                    rfl

theorem cell22_2804052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_2804052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804052 prefixEnd_2804052 := by exact prefixLift 2804052
  have htrace : WordTrace (prefixWord ++ tailWord_2804052) baseStart_2804052 baseEnd_2804052 := by
    simpa [prefixWord, tailWord_2804052, baseEnd_2804052] using wordTrace_append hprefix tailTrace_2804052
  have hstable : (prefixWord ++ tailWord_2804052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804052).length < 2 ^ (prefixWord ++ tailWord_2804052).sum := by decide
  have hdescent : baseEnd_2804052 < baseStart_2804052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804080 : List Nat := [2, 1, 1, 1, 4, 3, 2, 8]
def baseStart_2804080 : Nat := 118140960795 + 2804080 * 2 ^ 59
def prefixEnd_2804080 : Nat := 4983230072969 + 3 ^ 40 * 2804080 * 2
def baseEnd_2804080 : Nat := 106654876567369945022539

theorem tailTrace_2804080 : CollatzResearch.WordTrace tailWord_2804080 prefixEnd_2804080 106654876567369945022539 := by
  unfold tailWord_2804080
  simp only [CollatzResearch.WordTrace]
  refine ⟨51136599840652266791016847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68182133120869689054689129 51136599840652266791016847)
  ·
    refine ⟨76704899760978400186525271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51136599840652266791016847 76704899760978400186525271)
    ·
      refine ⟨115057349641467600279787907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76704899760978400186525271 115057349641467600279787907)
      ·
        refine ⟨172586024462201400419681861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115057349641467600279787907 172586024462201400419681861)
        ·
          refine ⟨32359879586662762578690349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172586024462201400419681861 32359879586662762578690349)
          ·
            refine ⟨12134954844998535967008881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32359879586662762578690349 12134954844998535967008881)
            ·
              refine ⟨9101216133748901975256661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12134954844998535967008881 9101216133748901975256661)
              ·
                refine ⟨106654876567369945022539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9101216133748901975256661 106654876567369945022539)
                ·
                  rfl

theorem cell22_2804080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 8].length) (baseStart_2804080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804080 prefixEnd_2804080 := by exact prefixLift 2804080
  have htrace : WordTrace (prefixWord ++ tailWord_2804080) baseStart_2804080 baseEnd_2804080 := by
    simpa [prefixWord, tailWord_2804080, baseEnd_2804080] using wordTrace_append hprefix tailTrace_2804080
  have hstable : (prefixWord ++ tailWord_2804080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804080).length < 2 ^ (prefixWord ++ tailWord_2804080).sum := by decide
  have hdescent : baseEnd_2804080 < baseStart_2804080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804082 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_2804082 : Nat := 118140960795 + 2804082 * 2 ^ 59
def prefixEnd_2804082 : Nat := 4983230072969 + 3 ^ 40 * 2804082 * 2
def baseEnd_2804082 : Nat := 959894573747202166652845

theorem tailTrace_2804082 : CollatzResearch.WordTrace tailWord_2804082 prefixEnd_2804082 959894573747202166652845 := by
  unfold tailWord_2804082
  simp only [CollatzResearch.WordTrace]
  refine ⟨25568318156824321980901625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68182181751531525282404333 25568318156824321980901625)
  ·
    refine ⟨19176238617618241485676219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25568318156824321980901625 19176238617618241485676219)
    ·
      refine ⟨28764357926427362228514329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19176238617618241485676219 28764357926427362228514329)
      ·
        refine ⟨21573268444820521671385747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28764357926427362228514329 21573268444820521671385747)
        ·
          refine ⟨32359902667230782507078621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21573268444820521671385747 32359902667230782507078621)
          ·
            refine ⟨12134963500211543440154483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32359902667230782507078621 12134963500211543440154483)
            ·
              refine ⟨18202445250317315160231725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12134963500211543440154483 18202445250317315160231725)
              ·
                refine ⟨6825916968868993185086897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18202445250317315160231725 6825916968868993185086897)
                ·
                  refine ⟨5119437726651744888815173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6825916968868993185086897 5119437726651744888815173)
                  ·
                    refine ⟨959894573747202166652845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5119437726651744888815173 959894573747202166652845)
                    ·
                      rfl

theorem cell22_2804082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_2804082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804082 prefixEnd_2804082 := by exact prefixLift 2804082
  have htrace : WordTrace (prefixWord ++ tailWord_2804082) baseStart_2804082 baseEnd_2804082 := by
    simpa [prefixWord, tailWord_2804082, baseEnd_2804082] using wordTrace_append hprefix tailTrace_2804082
  have hstable : (prefixWord ++ tailWord_2804082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804082).length < 2 ^ (prefixWord ++ tailWord_2804082).sum := by decide
  have hdescent : baseEnd_2804082 < baseStart_2804082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804140 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 3, 7]
def baseStart_2804140 : Nat := 118140960795 + 2804140 * 2 ^ 59
def prefixEnd_2804140 : Nat := 4983230072969 + 3 ^ 40 * 2804140 * 2
def baseEnd_2804140 : Nat := 959914428332509348702667

theorem tailTrace_2804140 : CollatzResearch.WordTrace tailWord_2804140 prefixEnd_2804140 959914428332509348702667 := by
  unfold tailWord_2804140
  simp only [CollatzResearch.WordTrace]
  refine ⟨51137694030543581914608937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68183592040724775886145249 51137694030543581914608937)
  ·
    refine ⟨38353270522907686435956703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51137694030543581914608937 38353270522907686435956703)
    ·
      refine ⟨57529905784361529653935055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38353270522907686435956703 57529905784361529653935055)
      ·
        refine ⟨86294858676542294480902583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57529905784361529653935055 86294858676542294480902583)
        ·
          refine ⟨129442288014813441721353875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86294858676542294480902583 129442288014813441721353875)
          ·
            refine ⟨194163432022220162582030813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129442288014813441721353875 194163432022220162582030813)
            ·
              refine ⟨72811287008332560968261555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194163432022220162582030813 72811287008332560968261555)
              ·
                refine ⟨109216930512498841452392333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72811287008332560968261555 109216930512498841452392333)
                ·
                  refine ⟨40956348942187065544647125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109216930512498841452392333 40956348942187065544647125)
                  ·
                    refine ⟨959914428332509348702667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40956348942187065544647125 959914428332509348702667)
                    ·
                      rfl

theorem cell22_2804140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_2804140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804140 prefixEnd_2804140 := by exact prefixLift 2804140
  have htrace : WordTrace (prefixWord ++ tailWord_2804140) baseStart_2804140 baseEnd_2804140 := by
    simpa [prefixWord, tailWord_2804140, baseEnd_2804140] using wordTrace_append hprefix tailTrace_2804140
  have hstable : (prefixWord ++ tailWord_2804140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804140).length < 2 ^ (prefixWord ++ tailWord_2804140).sum := by decide
  have hdescent : baseEnd_2804140 < baseStart_2804140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804146 : List Nat := [3, 2, 1, 1, 1, 1, 6, 3, 1, 3]
def baseStart_2804146 : Nat := 118140960795 + 2804146 * 2 ^ 59
def prefixEnd_2804146 : Nat := 4983230072969 + 3 ^ 40 * 2804146 * 2
def baseEnd_2804146 : Nat := 959916482255127333052649

theorem tailTrace_2804146 : CollatzResearch.WordTrace tailWord_2804146 prefixEnd_2804146 959916482255127333052649 := by
  unfold tailWord_2804146
  simp only [CollatzResearch.WordTrace]
  refine ⟨25568901724766356713484073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68183737932710284569290861 25568901724766356713484073)
  ·
    refine ⟨19176676293574767535113055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25568901724766356713484073 19176676293574767535113055)
    ·
      refine ⟨28765014440362151302669583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19176676293574767535113055 28765014440362151302669583)
      ·
        refine ⟨43147521660543226954004375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28765014440362151302669583 43147521660543226954004375)
        ·
          refine ⟨64721282490814840431006563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43147521660543226954004375 64721282490814840431006563)
          ·
            refine ⟨97081923736222260646509845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64721282490814840431006563 97081923736222260646509845)
            ·
              refine ⟨4550715175135418467805149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97081923736222260646509845 4550715175135418467805149)
              ·
                refine ⟨1706518190675781925426931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4550715175135418467805149 1706518190675781925426931)
                ·
                  refine ⟨2559777286013672888140397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1706518190675781925426931 2559777286013672888140397)
                  ·
                    refine ⟨959916482255127333052649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2559777286013672888140397 959916482255127333052649)
                    ·
                      rfl

theorem cell22_2804146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_2804146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804146 prefixEnd_2804146 := by exact prefixLift 2804146
  have htrace : WordTrace (prefixWord ++ tailWord_2804146) baseStart_2804146 baseEnd_2804146 := by
    simpa [prefixWord, tailWord_2804146, baseEnd_2804146] using wordTrace_append hprefix tailTrace_2804146
  have hstable : (prefixWord ++ tailWord_2804146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804146).length < 2 ^ (prefixWord ++ tailWord_2804146).sum := by decide
  have hdescent : baseEnd_2804146 < baseStart_2804146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804157 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_2804157 : Nat := 118140960795 + 2804157 * 2 ^ 59
def prefixEnd_2804157 : Nat := 4983230072969 + 3 ^ 40 * 2804157 * 2
def baseEnd_2804157 : Nat := 959920247779926971027615

theorem tailTrace_2804157 : CollatzResearch.WordTrace tailWord_2804157 prefixEnd_2804157 959920247779926971027615 := by
  unfold tailWord_2804157
  simp only [CollatzResearch.WordTrace]
  refine ⟨102276008102025575732586725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68184005401350383821724483 102276008102025575732586725)
  ·
    refine ⟨19176751519129795449860011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102276008102025575732586725 19176751519129795449860011)
    ·
      refine ⟨28765127278694693174790017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19176751519129795449860011 28765127278694693174790017)
      ·
        refine ⟨21573845459021019881092513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28765127278694693174790017 21573845459021019881092513)
        ·
          refine ⟨16180384094265764910819385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21573845459021019881092513 16180384094265764910819385)
          ·
            refine ⟨12135288070699323683114539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16180384094265764910819385 12135288070699323683114539)
            ·
              refine ⟨18202932106048985524671809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12135288070699323683114539 18202932106048985524671809)
              ·
                refine ⟨13652199079536739143503857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18202932106048985524671809 13652199079536739143503857)
                ·
                  refine ⟨10239149309652554357627893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13652199079536739143503857 10239149309652554357627893)
                  ·
                    refine ⟨959920247779926971027615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10239149309652554357627893 959920247779926971027615)
                    ·
                      rfl

theorem cell22_2804157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_2804157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804157 prefixEnd_2804157 := by exact prefixLift 2804157
  have htrace : WordTrace (prefixWord ++ tailWord_2804157) baseStart_2804157 baseEnd_2804157 := by
    simpa [prefixWord, tailWord_2804157, baseEnd_2804157] using wordTrace_append hprefix tailTrace_2804157
  have hstable : (prefixWord ++ tailWord_2804157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804157).length < 2 ^ (prefixWord ++ tailWord_2804157).sum := by decide
  have hdescent : baseEnd_2804157 < baseStart_2804157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804217 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 4, 4]
def baseStart_2804217 : Nat := 118140960795 + 2804217 * 2 ^ 59
def prefixEnd_2804217 : Nat := 4983230072969 + 3 ^ 40 * 2804217 * 2
def baseEnd_2804217 : Nat := 959940787006106814527431

theorem tailTrace_2804217 : CollatzResearch.WordTrace tailWord_2804217 prefixEnd_2804217 959940787006106814527431 := by
  unfold tailWord_2804217
  simp only [CollatzResearch.WordTrace]
  refine ⟨102278196481808205979770905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68185464321205470653180603 102278196481808205979770905)
  ·
    refine ⟨76708647361356154484828179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102278196481808205979770905 76708647361356154484828179)
    ·
      refine ⟨115062971042034231727242269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76708647361356154484828179 115062971042034231727242269)
      ·
        refine ⟨43148614140762836897715851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115062971042034231727242269 43148614140762836897715851)
        ·
          refine ⟨64722921211144255346573777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43148614140762836897715851 64722921211144255346573777)
          ·
            refine ⟨48542190908358191509930333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64722921211144255346573777 48542190908358191509930333)
            ·
              refine ⟨18203321590634321816223875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48542190908358191509930333 18203321590634321816223875)
              ·
                refine ⟨27304982385951482724335813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18203321590634321816223875 27304982385951482724335813)
                ·
                  refine ⟨5119684197365903010812965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27304982385951482724335813 5119684197365903010812965)
                  ·
                    refine ⟨959940787006106814527431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5119684197365903010812965 959940787006106814527431)
                    ·
                      rfl

theorem cell22_2804217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_2804217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804217 prefixEnd_2804217 := by exact prefixLift 2804217
  have htrace : WordTrace (prefixWord ++ tailWord_2804217) baseStart_2804217 baseEnd_2804217 := by
    simpa [prefixWord, tailWord_2804217, baseEnd_2804217] using wordTrace_append hprefix tailTrace_2804217
  have hstable : (prefixWord ++ tailWord_2804217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804217).length < 2 ^ (prefixWord ++ tailWord_2804217).sum := by decide
  have hdescent : baseEnd_2804217 < baseStart_2804217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804221 : List Nat := [1, 4, 1, 1, 1, 3, 5, 2, 4]
def baseStart_2804221 : Nat := 118140960795 + 2804221 * 2 ^ 59
def prefixEnd_2804221 : Nat := 4983230072969 + 3 ^ 40 * 2804221 * 2
def baseEnd_2804221 : Nat := 319980718762617379142473

theorem tailTrace_2804221 : CollatzResearch.WordTrace tailWord_2804221 prefixEnd_2804221 319980718762617379142473 := by
  unfold tailWord_2804221
  simp only [CollatzResearch.WordTrace]
  refine ⟨102278342373793714662916517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68185561582529143108611011 102278342373793714662916517)
  ·
    refine ⟨19177189195086321499296847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102278342373793714662916517 19177189195086321499296847)
    ·
      refine ⟨28765783792629482248945271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19177189195086321499296847 28765783792629482248945271)
      ·
        refine ⟨43148675688944223373417907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28765783792629482248945271 43148675688944223373417907)
        ·
          refine ⟨64723013533416335060126861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43148675688944223373417907 64723013533416335060126861)
          ·
            refine ⟨24271130075031125647547573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64723013533416335060126861 24271130075031125647547573)
            ·
              refine ⟨2275418444534168029457585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24271130075031125647547573 2275418444534168029457585)
              ·
                refine ⟨1706563833400626022093189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2275418444534168029457585 1706563833400626022093189)
                ·
                  refine ⟨319980718762617379142473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1706563833400626022093189 319980718762617379142473)
                  ·
                    rfl

theorem cell22_2804221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_2804221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804221 prefixEnd_2804221 := by exact prefixLift 2804221
  have htrace : WordTrace (prefixWord ++ tailWord_2804221) baseStart_2804221 baseEnd_2804221 := by
    simpa [prefixWord, tailWord_2804221, baseEnd_2804221] using wordTrace_append hprefix tailTrace_2804221
  have hstable : (prefixWord ++ tailWord_2804221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804221).length < 2 ^ (prefixWord ++ tailWord_2804221).sum := by decide
  have hdescent : baseEnd_2804221 < baseStart_2804221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804236 : List Nat := [2, 2, 1, 2, 4, 2, 1, 3, 2, 3]
def baseStart_2804236 : Nat := 118140960795 + 2804236 * 2 ^ 59
def prefixEnd_2804236 : Nat := 4983230072969 + 3 ^ 40 * 2804236 * 2
def baseEnd_2804236 : Nat := 959947291094397098302373

theorem tailTrace_2804236 : CollatzResearch.WordTrace tailWord_2804236 prefixEnd_2804236 959947291094397098302373 := by
  unfold tailWord_2804236
  simp only [CollatzResearch.WordTrace]
  refine ⟨51139444734369686112356281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68185926312492914816475041 51139444734369686112356281)
  ·
    refine ⟨38354583550777264584267211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51139444734369686112356281 38354583550777264584267211)
    ·
      refine ⟨57531875326165896876400817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38354583550777264584267211 57531875326165896876400817)
      ·
        refine ⟨43148906494624422657300613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57531875326165896876400817 43148906494624422657300613)
        ·
          refine ⟨8090419967742079248243865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43148906494624422657300613 8090419967742079248243865)
          ·
            refine ⟨6067814975806559436182899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8090419967742079248243865 6067814975806559436182899)
            ·
              refine ⟨9101722463709839154274349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6067814975806559436182899 9101722463709839154274349)
              ·
                refine ⟨3413145923891189682852881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9101722463709839154274349 3413145923891189682852881)
                ·
                  refine ⟨2559859442918392262139661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3413145923891189682852881 2559859442918392262139661)
                  ·
                    refine ⟨959947291094397098302373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2559859442918392262139661 959947291094397098302373)
                    ·
                      rfl

theorem cell22_2804236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_2804236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804236 prefixEnd_2804236 := by exact prefixLift 2804236
  have htrace : WordTrace (prefixWord ++ tailWord_2804236) baseStart_2804236 baseEnd_2804236 := by
    simpa [prefixWord, tailWord_2804236, baseEnd_2804236] using wordTrace_append hprefix tailTrace_2804236
  have hstable : (prefixWord ++ tailWord_2804236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804236).length < 2 ^ (prefixWord ++ tailWord_2804236).sum := by decide
  have hdescent : baseEnd_2804236 < baseStart_2804236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804328 : List Nat := [2, 1, 4, 3, 2, 2, 1, 2, 5]
def baseStart_2804328 : Nat := 118140960795 + 2804328 * 2 ^ 59
def prefixEnd_2804328 : Nat := 4983230072969 + 3 ^ 40 * 2804328 * 2
def baseEnd_2804328 : Nat := 319992928191513175000697

theorem tailTrace_2804328 : CollatzResearch.WordTrace tailWord_2804328 prefixEnd_2804328 319992928191513175000697 := by
  unfold tailWord_2804328
  simp only [CollatzResearch.WordTrace]
  refine ⟨51141122492203035968530819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68188163322937381291374425 51141122492203035968530819)
  ·
    refine ⟨76711683738304553952796229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51141122492203035968530819 76711683738304553952796229)
    ·
      refine ⟨14383440700932103866149293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76711683738304553952796229 14383440700932103866149293)
      ·
        refine ⟨5393790262849538949805985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14383440700932103866149293 5393790262849538949805985)
        ·
          refine ⟨4045342697137154212354489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5393790262849538949805985 4045342697137154212354489)
          ·
            refine ⟨3034007022852865659265867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4045342697137154212354489 3034007022852865659265867)
            ·
              refine ⟨4551010534279298488898801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034007022852865659265867 4551010534279298488898801)
              ·
                refine ⟨3413257900709473866674101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4551010534279298488898801 3413257900709473866674101)
                ·
                  refine ⟨319992928191513175000697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3413257900709473866674101 319992928191513175000697)
                  ·
                    rfl

theorem cell22_2804328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 5].length) (baseStart_2804328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804328 prefixEnd_2804328 := by exact prefixLift 2804328
  have htrace : WordTrace (prefixWord ++ tailWord_2804328) baseStart_2804328 baseEnd_2804328 := by
    simpa [prefixWord, tailWord_2804328, baseEnd_2804328] using wordTrace_append hprefix tailTrace_2804328
  have hstable : (prefixWord ++ tailWord_2804328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804328).length < 2 ^ (prefixWord ++ tailWord_2804328).sum := by decide
  have hdescent : baseEnd_2804328 < baseStart_2804328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804337 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 2, 9]
def baseStart_2804337 : Nat := 118140960795 + 2804337 * 2 ^ 59
def prefixEnd_2804337 : Nat := 4983230072969 + 3 ^ 40 * 2804337 * 2
def baseEnd_2804337 : Nat := 959981865458466501527063

theorem tailTrace_2804337 : CollatzResearch.WordTrace tailWord_2804337 prefixEnd_2804337 959981865458466501527063 := by
  unfold tailWord_2804337
  simp only [CollatzResearch.WordTrace]
  refine ⟨102282573241373466474139265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68188382160915644316092843 102282573241373466474139265)
  ·
    refine ⟨76711929931030099855604449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102282573241373466474139265 76711929931030099855604449)
    ·
      refine ⟨57533947448272574891703337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76711929931030099855604449 57533947448272574891703337)
      ·
        refine ⟨43150460586204431168777503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57533947448272574891703337 43150460586204431168777503)
        ·
          refine ⟨64725690879306646753166255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43150460586204431168777503 64725690879306646753166255)
          ·
            refine ⟨97088536318959970129749383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64725690879306646753166255 97088536318959970129749383)
            ·
              refine ⟨145632804478439955194624075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97088536318959970129749383 145632804478439955194624075)
              ·
                refine ⟨218449206717659932791936113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145632804478439955194624075 218449206717659932791936113)
                ·
                  refine ⟨163836905038244949593952085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218449206717659932791936113 163836905038244949593952085)
                  ·
                    refine ⟨959981865458466501527063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 163836905038244949593952085 959981865458466501527063)
                    ·
                      rfl

theorem cell22_2804337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_2804337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804337 prefixEnd_2804337 := by exact prefixLift 2804337
  have htrace : WordTrace (prefixWord ++ tailWord_2804337) baseStart_2804337 baseEnd_2804337 := by
    simpa [prefixWord, tailWord_2804337, baseEnd_2804337] using wordTrace_append hprefix tailTrace_2804337
  have hstable : (prefixWord ++ tailWord_2804337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804337).length < 2 ^ (prefixWord ++ tailWord_2804337).sum := by decide
  have hdescent : baseEnd_2804337 < baseStart_2804337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804367 : List Nat := [1, 1, 2, 1, 1, 1, 1, 14]
def baseStart_2804367 : Nat := 118140960795 + 2804367 * 2 ^ 59
def prefixEnd_2804367 : Nat := 4983230072969 + 3 ^ 40 * 2804367 * 2
def baseEnd_2804367 : Nat := 106665792785728491475219

theorem tailTrace_2804367 : CollatzResearch.WordTrace tailWord_2804367 prefixEnd_2804367 106665792785728491475219 := by
  unfold tailWord_2804367
  simp only [CollatzResearch.WordTrace]
  refine ⟨102283667431264781597731355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68189111620843187731820903 102283667431264781597731355)
  ·
    refine ⟨153425501146897172396597033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102283667431264781597731355 153425501146897172396597033)
    ·
      refine ⟨115069125860172879297447775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153425501146897172396597033 115069125860172879297447775)
      ·
        refine ⟨172603688790259318946171663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115069125860172879297447775 172603688790259318946171663)
        ·
          refine ⟨258905533185388978419257495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172603688790259318946171663 258905533185388978419257495)
          ·
            refine ⟨388358299778083467628886243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258905533185388978419257495 388358299778083467628886243)
            ·
              refine ⟨582537449667125201443329365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388358299778083467628886243 582537449667125201443329365)
              ·
                refine ⟨106665792785728491475219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 582537449667125201443329365 106665792785728491475219)
                ·
                  rfl

theorem cell22_2804367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 14].length) (baseStart_2804367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804367 prefixEnd_2804367 := by exact prefixLift 2804367
  have htrace : WordTrace (prefixWord ++ tailWord_2804367) baseStart_2804367 baseEnd_2804367 := by
    simpa [prefixWord, tailWord_2804367, baseEnd_2804367] using wordTrace_append hprefix tailTrace_2804367
  have hstable : (prefixWord ++ tailWord_2804367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804367).length < 2 ^ (prefixWord ++ tailWord_2804367).sum := by decide
  have hdescent : baseEnd_2804367 < baseStart_2804367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804405 : List Nat := [1, 3, 3, 3, 1, 1, 4, 1, 2, 3]
def baseStart_2804405 : Nat := 118140960795 + 2804405 * 2 ^ 59
def prefixEnd_2804405 : Nat := 4983230072969 + 3 ^ 40 * 2804405 * 2
def baseEnd_2804405 : Nat := 960005143248136990826855

theorem tailTrace_2804405 : CollatzResearch.WordTrace tailWord_2804405 prefixEnd_2804405 960005143248136990826855 := by
  unfold tailWord_2804405
  simp only [CollatzResearch.WordTrace]
  refine ⟨102285053405127114087614669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68190035603418076058409779 102285053405127114087614669)
  ·
    refine ⟨38356895026922667782855501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102285053405127114087614669 38356895026922667782855501)
    ·
      refine ⟨14383835635096000418570813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38356895026922667782855501 14383835635096000418570813)
      ·
        refine ⟨5393938363161000156964055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14383835635096000418570813 5393938363161000156964055)
        ·
          refine ⟨8090907544741500235446083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5393938363161000156964055 8090907544741500235446083)
          ·
            refine ⟨12136361317112250353169125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8090907544741500235446083 12136361317112250353169125)
            ·
              refine ⟨2275567746958546941219211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12136361317112250353169125 2275567746958546941219211)
              ·
                refine ⟨3413351620437820411828817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2275567746958546941219211 3413351620437820411828817)
                ·
                  refine ⟨2560013715328365308871613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3413351620437820411828817 2560013715328365308871613)
                  ·
                    refine ⟨960005143248136990826855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2560013715328365308871613 960005143248136990826855)
                    ·
                      rfl

theorem cell22_2804405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_2804405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804405 prefixEnd_2804405 := by exact prefixLift 2804405
  have htrace : WordTrace (prefixWord ++ tailWord_2804405) baseStart_2804405 baseEnd_2804405 := by
    simpa [prefixWord, tailWord_2804405, baseEnd_2804405] using wordTrace_append hprefix tailTrace_2804405
  have hstable : (prefixWord ++ tailWord_2804405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804405).length < 2 ^ (prefixWord ++ tailWord_2804405).sum := by decide
  have hdescent : baseEnd_2804405 < baseStart_2804405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804433 : List Nat := [1, 2, 2, 1, 2, 3, 2, 5, 1, 3]
def baseStart_2804433 : Nat := 118140960795 + 2804433 * 2 ^ 59
def prefixEnd_2804433 : Nat := 4983230072969 + 3 ^ 40 * 2804433 * 2
def baseEnd_2804433 : Nat := 960014728220354251126769

theorem tailTrace_2804433 : CollatzResearch.WordTrace tailWord_2804433 prefixEnd_2804433 960014728220354251126769 := by
  unfold tailWord_2804433
  simp only [CollatzResearch.WordTrace]
  refine ⟨102286074649025674869633953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68190716432683783246422635 102286074649025674869633953)
  ·
    refine ⟨76714555986769256152225465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102286074649025674869633953 76714555986769256152225465)
    ·
      refine ⟨57535916990076942114169099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76714555986769256152225465 57535916990076942114169099)
      ·
        refine ⟨86303875485115413171253649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57535916990076942114169099 86303875485115413171253649)
        ·
          refine ⟨64727906613836559878440237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86303875485115413171253649 64727906613836559878440237)
          ·
            refine ⟨24272964980188709954415089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64727906613836559878440237 24272964980188709954415089)
            ·
              refine ⟨18204723735141532465811317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24272964980188709954415089 18204723735141532465811317)
              ·
                refine ⟨1706692850169518668669811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18204723735141532465811317 1706692850169518668669811)
                ·
                  refine ⟨2560039275254278003004717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1706692850169518668669811 2560039275254278003004717)
                  ·
                    refine ⟨960014728220354251126769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2560039275254278003004717 960014728220354251126769)
                    ·
                      rfl

theorem cell22_2804433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_2804433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804433 prefixEnd_2804433 := by exact prefixLift 2804433
  have htrace : WordTrace (prefixWord ++ tailWord_2804433) baseStart_2804433 baseEnd_2804433 := by
    simpa [prefixWord, tailWord_2804433, baseEnd_2804433] using wordTrace_append hprefix tailTrace_2804433
  have hstable : (prefixWord ++ tailWord_2804433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804433).length < 2 ^ (prefixWord ++ tailWord_2804433).sum := by decide
  have hdescent : baseEnd_2804433 < baseStart_2804433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804461 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_2804461 : Nat := 118140960795 + 2804461 * 2 ^ 59
def prefixEnd_2804461 : Nat := 4983230072969 + 3 ^ 40 * 2804461 * 2
def baseEnd_2804461 : Nat := 960024313192571511426683

theorem tailTrace_2804461 : CollatzResearch.WordTrace tailWord_2804461 prefixEnd_2804461 960024313192571511426683 := by
  unfold tailWord_2804461
  simp only [CollatzResearch.WordTrace]
  refine ⟨102287095892924235651653237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68191397261949490434435491 102287095892924235651653237)
  ·
    refine ⟨9589415239961647092342491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102287095892924235651653237 9589415239961647092342491)
    ·
      refine ⟨14384122859942470638513737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9589415239961647092342491 14384122859942470638513737)
      ·
        refine ⟨10788092144956852978885303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14384122859942470638513737 10788092144956852978885303)
        ·
          refine ⟨16182138217435279468327955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10788092144956852978885303 16182138217435279468327955)
          ·
            refine ⟨24273207326152919202491933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16182138217435279468327955 24273207326152919202491933)
            ·
              refine ⟨9102452747307344700934475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24273207326152919202491933 9102452747307344700934475)
              ·
                refine ⟨13653679120961017051401713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9102452747307344700934475 13653679120961017051401713)
                ·
                  refine ⟨10240259340720762788551285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13653679120961017051401713 10240259340720762788551285)
                  ·
                    refine ⟨960024313192571511426683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10240259340720762788551285 960024313192571511426683)
                    ·
                      rfl

theorem cell22_2804461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_2804461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804461 prefixEnd_2804461 := by exact prefixLift 2804461
  have htrace : WordTrace (prefixWord ++ tailWord_2804461) baseStart_2804461 baseEnd_2804461 := by
    simpa [prefixWord, tailWord_2804461, baseEnd_2804461] using wordTrace_append hprefix tailTrace_2804461
  have hstable : (prefixWord ++ tailWord_2804461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804461).length < 2 ^ (prefixWord ++ tailWord_2804461).sum := by decide
  have hdescent : baseEnd_2804461 < baseStart_2804461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804474 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 8]
def baseStart_2804474 : Nat := 118140960795 + 2804474 * 2 ^ 59
def prefixEnd_2804474 : Nat := 4983230072969 + 3 ^ 40 * 2804474 * 2
def baseEnd_2804474 : Nat := 320009587786081270283881

theorem tailTrace_2804474 : CollatzResearch.WordTrace tailWord_2804474 prefixEnd_2804474 320009587786081270283881 := by
  unfold tailWord_2804474
  simp only [CollatzResearch.WordTrace]
  refine ⟨25571892510469284717969119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68191713361251425914584317 25571892510469284717969119)
  ·
    refine ⟨38357838765703927076953679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25571892510469284717969119 38357838765703927076953679)
    ·
      refine ⟨57536758148555890615430519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38357838765703927076953679 57536758148555890615430519)
      ·
        refine ⟨86305137222833835923145779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57536758148555890615430519 86305137222833835923145779)
        ·
          refine ⟨129457705834250753884718669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86305137222833835923145779 129457705834250753884718669)
          ·
            refine ⟨48546639687844032706769501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129457705834250753884718669 48546639687844032706769501)
            ·
              refine ⟨18204989882941512265038563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48546639687844032706769501 18204989882941512265038563)
              ·
                refine ⟨27307484824412268397557845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18204989882941512265038563 27307484824412268397557845)
                ·
                  refine ⟨320009587786081270283881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27307484824412268397557845 320009587786081270283881)
                  ·
                    rfl

theorem cell22_2804474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_2804474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804474 prefixEnd_2804474 := by exact prefixLift 2804474
  have htrace : WordTrace (prefixWord ++ tailWord_2804474) baseStart_2804474 baseEnd_2804474 := by
    simpa [prefixWord, tailWord_2804474, baseEnd_2804474] using wordTrace_append hprefix tailTrace_2804474
  have hstable : (prefixWord ++ tailWord_2804474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804474).length < 2 ^ (prefixWord ++ tailWord_2804474).sum := by decide
  have hdescent : baseEnd_2804474 < baseStart_2804474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804476 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 3, 4]
def baseStart_2804476 : Nat := 118140960795 + 2804476 * 2 ^ 59
def prefixEnd_2804476 : Nat := 4983230072969 + 3 ^ 40 * 2804476 * 2
def baseEnd_2804476 : Nat := 960029447999116472301637

theorem tailTrace_2804476 : CollatzResearch.WordTrace tailWord_2804476 prefixEnd_2804476 960029447999116472301637 := by
  unfold tailWord_2804476
  simp only [CollatzResearch.WordTrace]
  refine ⟨51143821493934946606724641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68191761991913262142299521 51143821493934946606724641)
  ·
    refine ⟨38357866120451209955043481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51143821493934946606724641 38357866120451209955043481)
    ·
      refine ⟨28768399590338407466282611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38357866120451209955043481 28768399590338407466282611)
      ·
        refine ⟨43152599385507611199423917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28768399590338407466282611 43152599385507611199423917)
        ·
          refine ⟨16182224769565354199783969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43152599385507611199423917 16182224769565354199783969)
          ·
            refine ⟨12136668577174015649837977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16182224769565354199783969 12136668577174015649837977)
            ·
              refine ⟨9102501432880511737378483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12136668577174015649837977 9102501432880511737378483)
              ·
                refine ⟨13653752149320767606067725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9102501432880511737378483 13653752149320767606067725)
                ·
                  refine ⟨5120157055995287852275397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13653752149320767606067725 5120157055995287852275397)
                  ·
                    refine ⟨960029447999116472301637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5120157055995287852275397 960029447999116472301637)
                    ·
                      rfl

theorem cell22_2804476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_2804476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804476 prefixEnd_2804476 := by exact prefixLift 2804476
  have htrace : WordTrace (prefixWord ++ tailWord_2804476) baseStart_2804476 baseEnd_2804476 := by
    simpa [prefixWord, tailWord_2804476, baseEnd_2804476] using wordTrace_append hprefix tailTrace_2804476
  have hstable : (prefixWord ++ tailWord_2804476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804476).length < 2 ^ (prefixWord ++ tailWord_2804476).sum := by decide
  have hdescent : baseEnd_2804476 < baseStart_2804476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804508 : List Nat := [2, 2, 3, 1, 1, 3, 2, 4, 4]
def baseStart_2804508 : Nat := 118140960795 + 2804508 * 2 ^ 59
def prefixEnd_2804508 : Nat := 4983230072969 + 3 ^ 40 * 2804508 * 2
def baseEnd_2804508 : Nat := 320013467417693018500513

theorem tailTrace_2804508 : CollatzResearch.WordTrace tailWord_2804508 prefixEnd_2804508 320013467417693018500513 := by
  unfold tailWord_2804508
  simp only [CollatzResearch.WordTrace]
  refine ⟨51144405061876981339307089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68192540082502641785742785 51144405061876981339307089)
  ·
    refine ⟨38358303796407736004480317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51144405061876981339307089 38358303796407736004480317)
    ·
      refine ⟨14384363923652901001680119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38358303796407736004480317 14384363923652901001680119)
      ·
        refine ⟨21576545885479351502520179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14384363923652901001680119 21576545885479351502520179)
        ·
          refine ⟨32364818828219027253780269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21576545885479351502520179 32364818828219027253780269)
          ·
            refine ⟨12136807060582135220167601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32364818828219027253780269 12136807060582135220167601)
            ·
              refine ⟨9102605295436601415125701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12136807060582135220167601 9102605295436601415125701)
              ·
                refine ⟨1706738492894362765336069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9102605295436601415125701 1706738492894362765336069)
                ·
                  refine ⟨320013467417693018500513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1706738492894362765336069 320013467417693018500513)
                  ·
                    rfl

theorem cell22_2804508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_2804508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804508 prefixEnd_2804508 := by exact prefixLift 2804508
  have htrace : WordTrace (prefixWord ++ tailWord_2804508) baseStart_2804508 baseEnd_2804508 := by
    simpa [prefixWord, tailWord_2804508, baseEnd_2804508] using wordTrace_append hprefix tailTrace_2804508
  have hstable : (prefixWord ++ tailWord_2804508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804508).length < 2 ^ (prefixWord ++ tailWord_2804508).sum := by decide
  have hdescent : baseEnd_2804508 < baseStart_2804508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804542 : List Nat := [4, 2, 1, 2, 3, 2, 1, 3, 4]
def baseStart_2804542 : Nat := 118140960795 + 2804542 * 2 ^ 59
def prefixEnd_2804542 : Nat := 4983230072969 + 3 ^ 40 * 2804542 * 2
def baseEnd_2804542 : Nat := 320017347049304766717145

theorem tailTrace_2804542 : CollatzResearch.WordTrace tailWord_2804542 prefixEnd_2804542 320017347049304766717145 := by
  unfold tailWord_2804542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12786256275703848310668985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68193366803753857656901253 12786256275703848310668985)
  ·
    refine ⟨9589692206777886233001739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12786256275703848310668985 9589692206777886233001739)
    ·
      refine ⟨14384538310166829349502609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9589692206777886233001739 14384538310166829349502609)
      ·
        refine ⟨10788403732625122012126957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14384538310166829349502609 10788403732625122012126957)
        ·
          refine ⟨4045651399734420754547609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10788403732625122012126957 4045651399734420754547609)
          ·
            refine ⟨3034238549800815565910707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4045651399734420754547609 3034238549800815565910707)
            ·
              refine ⟨4551357824701223348866061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034238549800815565910707 4551357824701223348866061)
              ·
                refine ⟨1706759184262958755824773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4551357824701223348866061 1706759184262958755824773)
                ·
                  refine ⟨320017347049304766717145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1706759184262958755824773 320017347049304766717145)
                  ·
                    rfl

theorem cell22_2804542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_2804542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804542 prefixEnd_2804542 := by exact prefixLift 2804542
  have htrace : WordTrace (prefixWord ++ tailWord_2804542) baseStart_2804542 baseEnd_2804542 := by
    simpa [prefixWord, tailWord_2804542, baseEnd_2804542] using wordTrace_append hprefix tailTrace_2804542
  have hstable : (prefixWord ++ tailWord_2804542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804542).length < 2 ^ (prefixWord ++ tailWord_2804542).sum := by decide
  have hdescent : baseEnd_2804542 < baseStart_2804542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804628 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2804628 : Nat := 118140960795 + 2804628 * 2 ^ 59
def prefixEnd_2804628 : Nat := 4983230072969 + 3 ^ 40 * 2804628 * 2
def baseEnd_2804628 : Nat := 960081480705438742501171

theorem tailTrace_2804628 : CollatzResearch.WordTrace tailWord_2804628 prefixEnd_2804628 960081480705438742501171 := by
  unfold tailWord_2804628
  simp only [CollatzResearch.WordTrace]
  refine ⟨51146593441659611586491269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68195457922212815448655025 51146593441659611586491269)
  ·
    refine ⟨9589986270311177172467113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51146593441659611586491269 9589986270311177172467113)
    ·
      refine ⟨7192489702733382879350335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9589986270311177172467113 7192489702733382879350335)
      ·
        refine ⟨10788734554100074319025503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7192489702733382879350335 10788734554100074319025503)
        ·
          refine ⟨16183101831150111478538255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10788734554100074319025503 16183101831150111478538255)
          ·
            refine ⟨24274652746725167217807383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16183101831150111478538255 24274652746725167217807383)
            ·
              refine ⟨36411979120087750826711075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24274652746725167217807383 36411979120087750826711075)
              ·
                refine ⟨54617968680131626240066613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36411979120087750826711075 54617968680131626240066613)
                ·
                  refine ⟨5120434563762339960006245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54617968680131626240066613 5120434563762339960006245)
                  ·
                    refine ⟨960081480705438742501171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5120434563762339960006245 960081480705438742501171)
                    ·
                      rfl

theorem cell22_2804628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2804628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804628 prefixEnd_2804628 := by exact prefixLift 2804628
  have htrace : WordTrace (prefixWord ++ tailWord_2804628) baseStart_2804628 baseEnd_2804628 := by
    simpa [prefixWord, tailWord_2804628, baseEnd_2804628] using wordTrace_append hprefix tailTrace_2804628
  have hstable : (prefixWord ++ tailWord_2804628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804628).length < 2 ^ (prefixWord ++ tailWord_2804628).sum := by decide
  have hdescent : baseEnd_2804628 < baseStart_2804628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804722 : List Nat := [3, 2, 1, 5, 2, 1, 8]
def baseStart_2804722 : Nat := 118140960795 + 2804722 * 2 ^ 59
def prefixEnd_2804722 : Nat := 4983230072969 + 3 ^ 40 * 2804722 * 2
def baseEnd_2804722 : Nat := 35559765141720512246329

theorem tailTrace_2804722 : CollatzResearch.WordTrace tailWord_2804722 prefixEnd_2804722 35559765141720512246329 := by
  unfold tailWord_2804722
  simp only [CollatzResearch.WordTrace]
  refine ⟨25574153836244669306726105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68197743563319118151269613 25574153836244669306726105)
  ·
    refine ⟨19180615377183501980044579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25574153836244669306726105 19180615377183501980044579)
    ·
      refine ⟨28770923065775252970066869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19180615377183501980044579 28770923065775252970066869)
      ·
        refine ⟨2697274037416429965943769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28770923065775252970066869 2697274037416429965943769)
        ·
          refine ⟨2022955528062322474457827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2697274037416429965943769 2022955528062322474457827)
          ·
            refine ⟨3034433292093483711686741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022955528062322474457827 3034433292093483711686741)
            ·
              refine ⟨35559765141720512246329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3034433292093483711686741 35559765141720512246329)
              ·
                rfl

theorem cell22_2804722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 8].length) (baseStart_2804722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804722 prefixEnd_2804722 := by exact prefixLift 2804722
  have htrace : WordTrace (prefixWord ++ tailWord_2804722) baseStart_2804722 baseEnd_2804722 := by
    simpa [prefixWord, tailWord_2804722, baseEnd_2804722] using wordTrace_append hprefix tailTrace_2804722
  have hstable : (prefixWord ++ tailWord_2804722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804722).length < 2 ^ (prefixWord ++ tailWord_2804722).sum := by decide
  have hdescent : baseEnd_2804722 < baseStart_2804722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804733 : List Nat := [1, 4, 1, 1, 1, 2, 1, 6, 5]
def baseStart_2804733 : Nat := 118140960795 + 2804733 * 2 ^ 59
def prefixEnd_2804733 : Nat := 4983230072969 + 3 ^ 40 * 2804733 * 2
def baseEnd_2804733 : Nat := 320039141450417822875283

theorem tailTrace_2804733 : CollatzResearch.WordTrace tailWord_2804733 prefixEnd_2804733 320039141450417822875283 := by
  unfold tailWord_2804733
  simp only [CollatzResearch.WordTrace]
  refine ⟨102297016547938826105554853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68198011031959217403703235 102297016547938826105554853)
  ·
    refine ⟨19180690602738529894791535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102297016547938826105554853 19180690602738529894791535)
    ·
      refine ⟨28771035904107794842187303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19180690602738529894791535 28771035904107794842187303)
      ·
        refine ⟨43156553856161692263280955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28771035904107794842187303 43156553856161692263280955)
        ·
          refine ⟨64734830784242538394921433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43156553856161692263280955 64734830784242538394921433)
          ·
            refine ⟨48551123088181903796191075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64734830784242538394921433 48551123088181903796191075)
            ·
              refine ⟨72826684632272855694286613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48551123088181903796191075 72826684632272855694286613)
              ·
                refine ⟨3413750842137790110669685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72826684632272855694286613 3413750842137790110669685)
                ·
                  refine ⟨320039141450417822875283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3413750842137790110669685 320039141450417822875283)
                  ·
                    rfl

theorem cell22_2804733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_2804733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804733 prefixEnd_2804733 := by exact prefixLift 2804733
  have htrace : WordTrace (prefixWord ++ tailWord_2804733) baseStart_2804733 baseEnd_2804733 := by
    simpa [prefixWord, tailWord_2804733, baseEnd_2804733] using wordTrace_append hprefix tailTrace_2804733
  have hstable : (prefixWord ++ tailWord_2804733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804733).length < 2 ^ (prefixWord ++ tailWord_2804733).sum := by decide
  have hdescent : baseEnd_2804733 < baseStart_2804733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804737 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 3, 3]
def baseStart_2804737 : Nat := 118140960795 + 2804737 * 2 ^ 59
def prefixEnd_2804737 : Nat := 4983230072969 + 3 ^ 40 * 2804737 * 2
def baseEnd_2804737 : Nat := 960118793632998791525837

theorem tailTrace_2804737 : CollatzResearch.WordTrace tailWord_2804737 prefixEnd_2804737 960118793632998791525837 := by
  unfold tailWord_2804737
  simp only [CollatzResearch.WordTrace]
  refine ⟨102297162439924334788700465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68198108293282889859133643 102297162439924334788700465)
  ·
    refine ⟨76722871829943251091525349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102297162439924334788700465 76722871829943251091525349)
    ·
      refine ⟨14385538468114359579661003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76722871829943251091525349 14385538468114359579661003)
      ·
        refine ⟨21578307702171539369491505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14385538468114359579661003 21578307702171539369491505)
        ·
          refine ⟨16183730776628654527118629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21578307702171539369491505 16183730776628654527118629)
          ·
            refine ⟨3034449520617872723834743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16183730776628654527118629 3034449520617872723834743)
            ·
              refine ⟨4551674280926809085752115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034449520617872723834743 4551674280926809085752115)
              ·
                refine ⟨6827511421390213628628173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4551674280926809085752115 6827511421390213628628173)
                ·
                  refine ⟨2560316783021330110735565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6827511421390213628628173 2560316783021330110735565)
                  ·
                    refine ⟨960118793632998791525837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2560316783021330110735565 960118793632998791525837)
                    ·
                      rfl

theorem cell22_2804737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_2804737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804737 prefixEnd_2804737 := by exact prefixLift 2804737
  have htrace : WordTrace (prefixWord ++ tailWord_2804737) baseStart_2804737 baseEnd_2804737 := by
    simpa [prefixWord, tailWord_2804737, baseEnd_2804737] using wordTrace_append hprefix tailTrace_2804737
  have hstable : (prefixWord ++ tailWord_2804737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804737).length < 2 ^ (prefixWord ++ tailWord_2804737).sum := by decide
  have hdescent : baseEnd_2804737 < baseStart_2804737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804750 : List Nat := [4, 1, 1, 2, 2, 3, 1, 3, 5]
def baseStart_2804750 : Nat := 118140960795 + 2804750 * 2 ^ 59
def prefixEnd_2804750 : Nat := 4983230072969 + 3 ^ 40 * 2804750 * 2
def baseEnd_2804750 : Nat := 320041081266223696983599

theorem tailTrace_2804750 : CollatzResearch.WordTrace tailWord_2804750 prefixEnd_2804750 320041081266223696983599 := by
  unfold tailWord_2804750
  simp only [CollatzResearch.WordTrace]
  refine ⟨12787204573609654751115463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68198424392584825339282469 12787204573609654751115463)
  ·
    refine ⟨19180806860414482126673195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12787204573609654751115463 19180806860414482126673195)
    ·
      refine ⟨28771210290621723190009793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19180806860414482126673195 28771210290621723190009793)
      ·
        refine ⟨21578407717966292392507345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28771210290621723190009793 21578407717966292392507345)
        ·
          refine ⟨16183805788474719294380509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21578407717966292392507345 16183805788474719294380509)
          ·
            refine ⟨6068927170678019735392691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16183805788474719294380509 6068927170678019735392691)
            ·
              refine ⟨9103390756017029603089037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6068927170678019735392691 9103390756017029603089037)
              ·
                refine ⟨3413771533506386101158389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9103390756017029603089037 3413771533506386101158389)
                ·
                  refine ⟨320041081266223696983599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3413771533506386101158389 320041081266223696983599)
                  ·
                    rfl

theorem cell22_2804750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_2804750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804750 prefixEnd_2804750 := by exact prefixLift 2804750
  have htrace : WordTrace (prefixWord ++ tailWord_2804750) baseStart_2804750 baseEnd_2804750 := by
    simpa [prefixWord, tailWord_2804750, baseEnd_2804750] using wordTrace_append hprefix tailTrace_2804750
  have hstable : (prefixWord ++ tailWord_2804750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804750).length < 2 ^ (prefixWord ++ tailWord_2804750).sum := by decide
  have hdescent : baseEnd_2804750 < baseStart_2804750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804788 : List Nat := [2, 5, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_2804788 : Nat := 118140960795 + 2804788 * 2 ^ 59
def prefixEnd_2804788 : Nat := 4983230072969 + 3 ^ 40 * 2804788 * 2
def baseEnd_2804788 : Nat := 960136251975251658500681

theorem tailTrace_2804788 : CollatzResearch.WordTrace tailWord_2804788 prefixEnd_2804788 960136251975251658500681 := by
  unfold tailWord_2804788
  simp only [CollatzResearch.WordTrace]
  refine ⟨51149511281369785249403509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68199348375159713665871345 51149511281369785249403509)
  ·
    refine ⟨4795266682628417367131579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51149511281369785249403509 4795266682628417367131579)
    ·
      refine ⟨7192900023942626050697369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4795266682628417367131579 7192900023942626050697369)
      ·
        refine ⟨5394675017956969538023027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7192900023942626050697369 5394675017956969538023027)
        ·
          refine ⟨8092012526935454307034541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5394675017956969538023027 8092012526935454307034541)
          ·
            refine ⟨3034504697600795365137953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8092012526935454307034541 3034504697600795365137953)
            ·
              refine ⟨2275878523200596523853465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3034504697600795365137953 2275878523200596523853465)
              ·
                refine ⟨1706908892400447392890099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2275878523200596523853465 1706908892400447392890099)
                ·
                  refine ⟨2560363338600671089335149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1706908892400447392890099 2560363338600671089335149)
                  ·
                    refine ⟨960136251975251658500681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2560363338600671089335149 960136251975251658500681)
                    ·
                      rfl

theorem cell22_2804788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_2804788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804788 prefixEnd_2804788 := by exact prefixLift 2804788
  have htrace : WordTrace (prefixWord ++ tailWord_2804788) baseStart_2804788 baseEnd_2804788 := by
    simpa [prefixWord, tailWord_2804788, baseEnd_2804788] using wordTrace_append hprefix tailTrace_2804788
  have hstable : (prefixWord ++ tailWord_2804788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804788).length < 2 ^ (prefixWord ++ tailWord_2804788).sum := by decide
  have hdescent : baseEnd_2804788 < baseStart_2804788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804808 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 1, 6]
def baseStart_2804808 : Nat := 118140960795 + 2804808 * 2 ^ 59
def prefixEnd_2804808 : Nat := 4983230072969 + 3 ^ 40 * 2804808 * 2
def baseEnd_2804808 : Nat := 960143098383978273000619

theorem tailTrace_2804808 : CollatzResearch.WordTrace tailWord_2804808 prefixEnd_2804808 960143098383978273000619 := by
  unfold tailWord_2804808
  simp only [CollatzResearch.WordTrace]
  refine ⟨51149876011333556957267539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68199834681778075943023385 51149876011333556957267539)
  ·
    refine ⟨76724814017000335435901309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51149876011333556957267539 76724814017000335435901309)
    ·
      refine ⟨28771805256375125788462991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76724814017000335435901309 28771805256375125788462991)
      ·
        refine ⟨43157707884562688682694487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28771805256375125788462991 43157707884562688682694487)
        ·
          refine ⟨64736561826844033024041731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43157707884562688682694487 64736561826844033024041731)
          ·
            refine ⟨97104842740266049536062597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64736561826844033024041731 97104842740266049536062597)
            ·
              refine ⟨18207158013799884288011737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97104842740266049536062597 18207158013799884288011737)
              ·
                refine ⟨13655368510349913216008803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18207158013799884288011737 13655368510349913216008803)
                ·
                  refine ⟨20483052765524869824013205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13655368510349913216008803 20483052765524869824013205)
                  ·
                    refine ⟨960143098383978273000619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20483052765524869824013205 960143098383978273000619)
                    ·
                      rfl

theorem cell22_2804808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_2804808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804808 prefixEnd_2804808 := by exact prefixLift 2804808
  have htrace : WordTrace (prefixWord ++ tailWord_2804808) baseStart_2804808 baseEnd_2804808 := by
    simpa [prefixWord, tailWord_2804808, baseEnd_2804808] using wordTrace_append hprefix tailTrace_2804808
  have hstable : (prefixWord ++ tailWord_2804808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804808).length < 2 ^ (prefixWord ++ tailWord_2804808).sum := by decide
  have hdescent : baseEnd_2804808 < baseStart_2804808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804883 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 1, 7]
def baseStart_2804883 : Nat := 118140960795 + 2804883 * 2 ^ 59
def prefixEnd_2804883 : Nat := 4983230072969 + 3 ^ 40 * 2804883 * 2
def baseEnd_2804883 : Nat := 960168772416703077375389

theorem tailTrace_2804883 : CollatzResearch.WordTrace tailWord_2804883 prefixEnd_2804883 960168772416703077375389 := by
  unfold tailWord_2804883
  simp only [CollatzResearch.WordTrace]
  refine ⟨102302487497395401723515303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68201658331596934482343535 102302487497395401723515303)
  ·
    refine ⟨153453731246093102585272955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102302487497395401723515303 153453731246093102585272955)
    ·
      refine ⟨230180596869139653877909433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153453731246093102585272955 230180596869139653877909433)
      ·
        refine ⟨172635447651854740408432075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230180596869139653877909433 172635447651854740408432075)
        ·
          refine ⟨258953171477782110612648113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172635447651854740408432075 258953171477782110612648113)
          ·
            refine ⟨194214878608336582959486085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258953171477782110612648113 194214878608336582959486085)
            ·
              refine ⟨36415289739063109304903641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194214878608336582959486085 36415289739063109304903641)
              ·
                refine ⟨27311467304297331978677731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36415289739063109304903641 27311467304297331978677731)
                ·
                  refine ⟨40967200956445997968016597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27311467304297331978677731 40967200956445997968016597)
                  ·
                    refine ⟨960168772416703077375389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40967200956445997968016597 960168772416703077375389)
                    ·
                      rfl

theorem cell22_2804883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 7].length) (baseStart_2804883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804883 prefixEnd_2804883 := by exact prefixLift 2804883
  have htrace : WordTrace (prefixWord ++ tailWord_2804883) baseStart_2804883 baseEnd_2804883 := by
    simpa [prefixWord, tailWord_2804883, baseEnd_2804883] using wordTrace_append hprefix tailTrace_2804883
  have hstable : (prefixWord ++ tailWord_2804883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804883).length < 2 ^ (prefixWord ++ tailWord_2804883).sum := by decide
  have hdescent : baseEnd_2804883 < baseStart_2804883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804906 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 3, 3]
def baseStart_2804906 : Nat := 118140960795 + 2804906 * 2 ^ 59
def prefixEnd_2804906 : Nat := 4983230072969 + 3 ^ 40 * 2804906 * 2
def baseEnd_2804906 : Nat := 960176645786738684050319

theorem tailTrace_2804906 : CollatzResearch.WordTrace tailWord_2804906 prefixEnd_2804906 960176645786738684050319 := by
  unfold tailWord_2804906
  simp only [CollatzResearch.WordTrace]
  refine ⟨25575831594078019162900643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68202217584208051101068381 25575831594078019162900643)
  ·
    refine ⟨38363747391117028744350965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25575831594078019162900643 38363747391117028744350965)
    ·
      refine ⟨3596601317917221444782903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38363747391117028744350965 3596601317917221444782903)
      ·
        refine ⟨5394901976875832167174355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3596601317917221444782903 5394901976875832167174355)
        ·
          refine ⟨8092352965313748250761533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5394901976875832167174355 8092352965313748250761533)
          ·
            refine ⟨3034632361992655594035575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8092352965313748250761533 3034632361992655594035575)
            ·
              refine ⟨4551948542988983391053363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034632361992655594035575 4551948542988983391053363)
              ·
                refine ⟨6827922814483475086580045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4551948542988983391053363 6827922814483475086580045)
                ·
                  refine ⟨2560471055431303157467517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6827922814483475086580045 2560471055431303157467517)
                  ·
                    refine ⟨960176645786738684050319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2560471055431303157467517 960176645786738684050319)
                    ·
                      rfl

theorem cell22_2804906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_2804906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804906 prefixEnd_2804906 := by exact prefixLift 2804906
  have htrace : WordTrace (prefixWord ++ tailWord_2804906) baseStart_2804906 baseEnd_2804906 := by
    simpa [prefixWord, tailWord_2804906, baseEnd_2804906] using wordTrace_append hprefix tailTrace_2804906
  have hstable : (prefixWord ++ tailWord_2804906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804906).length < 2 ^ (prefixWord ++ tailWord_2804906).sum := by decide
  have hdescent : baseEnd_2804906 < baseStart_2804906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804964 : List Nat := [2, 3, 1, 1, 1, 2, 6, 2, 4]
def baseStart_2804964 : Nat := 118140960795 + 2804964 * 2 ^ 59
def prefixEnd_2804964 : Nat := 4983230072969 + 3 ^ 40 * 2804964 * 2
def baseEnd_2804964 : Nat := 320065500124015288700047

theorem tailTrace_2804964 : CollatzResearch.WordTrace tailWord_2804964 prefixEnd_2804964 320065500124015288700047 := by
  unfold tailWord_2804964
  simp only [CollatzResearch.WordTrace]
  refine ⟨51152720905050976278606973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68203627873401301704809297 51152720905050976278606973)
  ·
    refine ⟨19182270339394116104477615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51152720905050976278606973 19182270339394116104477615)
    ·
      refine ⟨28773405509091174156716423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19182270339394116104477615 28773405509091174156716423)
      ·
        refine ⟨43160108263636761235074635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28773405509091174156716423 43160108263636761235074635)
        ·
          refine ⟨64740162395455141852611953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43160108263636761235074635 64740162395455141852611953)
          ·
            refine ⟨48555121796591356389458965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64740162395455141852611953 48555121796591356389458965)
            ·
              refine ⟨2276021334215219830755889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48555121796591356389458965 2276021334215219830755889)
              ·
                refine ⟨1707016000661414873066917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2276021334215219830755889 1707016000661414873066917)
                ·
                  refine ⟨320065500124015288700047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1707016000661414873066917 320065500124015288700047)
                  ·
                    rfl

theorem cell22_2804964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_2804964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804964 prefixEnd_2804964 := by exact prefixLift 2804964
  have htrace : WordTrace (prefixWord ++ tailWord_2804964) baseStart_2804964 baseEnd_2804964 := by
    simpa [prefixWord, tailWord_2804964, baseEnd_2804964] using wordTrace_append hprefix tailTrace_2804964
  have hstable : (prefixWord ++ tailWord_2804964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804964).length < 2 ^ (prefixWord ++ tailWord_2804964).sum := by decide
  have hdescent : baseEnd_2804964 < baseStart_2804964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804994 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_2804994 : Nat := 118140960795 + 2804994 * 2 ^ 59
def prefixEnd_2804994 : Nat := 4983230072969 + 3 ^ 40 * 2804994 * 2
def baseEnd_2804994 : Nat := 960206769985135787850049

theorem tailTrace_2804994 : CollatzResearch.WordTrace tailWord_2804994 prefixEnd_2804994 960206769985135787850049 := by
  unfold tailWord_2804994
  simp only [CollatzResearch.WordTrace]
  refine ⟨25576633999998316920201509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68204357333328845120537357 25576633999998316920201509)
  ·
    refine ⟨4795618874999684422537783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25576633999998316920201509 4795618874999684422537783)
    ·
      refine ⟨7193428312499526633806675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4795618874999684422537783 7193428312499526633806675)
      ·
        refine ⟨10790142468749289950710013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7193428312499526633806675 10790142468749289950710013)
        ·
          refine ⟨4046303425780983731516255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10790142468749289950710013 4046303425780983731516255)
          ·
            refine ⟨6069455138671475597274383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4046303425780983731516255 6069455138671475597274383)
            ·
              refine ⟨9104182708007213395911575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6069455138671475597274383 9104182708007213395911575)
              ·
                refine ⟨13656274062010820093867363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9104182708007213395911575 13656274062010820093867363)
                ·
                  refine ⟨20484411093016230140801045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13656274062010820093867363 20484411093016230140801045)
                  ·
                    refine ⟨960206769985135787850049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20484411093016230140801045 960206769985135787850049)
                    ·
                      rfl

theorem cell22_2804994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_2804994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2804994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2804994 prefixEnd_2804994 := by exact prefixLift 2804994
  have htrace : WordTrace (prefixWord ++ tailWord_2804994) baseStart_2804994 baseEnd_2804994 := by
    simpa [prefixWord, tailWord_2804994, baseEnd_2804994] using wordTrace_append hprefix tailTrace_2804994
  have hstable : (prefixWord ++ tailWord_2804994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804994).length < 2 ^ (prefixWord ++ tailWord_2804994).sum := by decide
  have hdescent : baseEnd_2804994 < baseStart_2804994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805065 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 8]
def baseStart_2805065 : Nat := 118140960795 + 2805065 * 2 ^ 59
def prefixEnd_2805065 : Nat := 4983230072969 + 3 ^ 40 * 2805065 * 2
def baseEnd_2805065 : Nat := 320077024912038423108277

theorem tailTrace_2805065 : CollatzResearch.WordTrace tailWord_2805065 prefixEnd_2805065 320077024912038423108277 := by
  unfold tailWord_2805065
  simp only [CollatzResearch.WordTrace]
  refine ⟨102309125582736046806640649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68206083721824031204427099 102309125582736046806640649)
  ·
    refine ⟨76731844187052035104980487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102309125582736046806640649 76731844187052035104980487)
    ·
      refine ⟨115097766280578052657470731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76731844187052035104980487 115097766280578052657470731)
      ·
        refine ⟨172646649420867078986206097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115097766280578052657470731 172646649420867078986206097)
        ·
          refine ⟨129484987065650309239654573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172646649420867078986206097 129484987065650309239654573)
          ·
            refine ⟨48556870149618865964870465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129484987065650309239654573 48556870149618865964870465)
            ·
              refine ⟨36417652612214149473652849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48556870149618865964870465 36417652612214149473652849)
              ·
                refine ⟨27313239459160612105239637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36417652612214149473652849 27313239459160612105239637)
                ·
                  refine ⟨320077024912038423108277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27313239459160612105239637 320077024912038423108277)
                  ·
                    rfl

theorem cell22_2805065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 8].length) (baseStart_2805065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805065 prefixEnd_2805065 := by exact prefixLift 2805065
  have htrace : WordTrace (prefixWord ++ tailWord_2805065) baseStart_2805065 baseEnd_2805065 := by
    simpa [prefixWord, tailWord_2805065, baseEnd_2805065] using wordTrace_append hprefix tailTrace_2805065
  have hstable : (prefixWord ++ tailWord_2805065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805065).length < 2 ^ (prefixWord ++ tailWord_2805065).sum := by decide
  have hdescent : baseEnd_2805065 < baseStart_2805065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805082 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 6]
def baseStart_2805082 : Nat := 118140960795 + 2805082 * 2 ^ 59
def prefixEnd_2805082 : Nat := 4983230072969 + 3 ^ 40 * 2805082 * 2
def baseEnd_2805082 : Nat := 320078964727844297216593

theorem tailTrace_2805082 : CollatzResearch.WordTrace tailWord_2805082 prefixEnd_2805082 320078964727844297216593 := by
  unfold tailWord_2805082
  simp only [CollatzResearch.WordTrace]
  refine ⟨25577436405918614677502375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68206497082449639140006333 25577436405918614677502375)
  ·
    refine ⟨38366154608877922016253563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25577436405918614677502375 38366154608877922016253563)
    ·
      refine ⟨57549231913316883024380345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38366154608877922016253563 57549231913316883024380345)
      ·
        refine ⟨43161923934987662268285259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57549231913316883024380345 43161923934987662268285259)
        ·
          refine ⟨64742885902481493402427889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43161923934987662268285259 64742885902481493402427889)
          ·
            refine ⟨48557164426861120051820917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64742885902481493402427889 48557164426861120051820917)
            ·
              refine ⟨4552234165018230004858211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48557164426861120051820917 4552234165018230004858211)
              ·
                refine ⟨6828351247527345007287317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4552234165018230004858211 6828351247527345007287317)
                ·
                  refine ⟨320078964727844297216593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6828351247527345007287317 320078964727844297216593)
                  ·
                    rfl

theorem cell22_2805082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_2805082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805082 prefixEnd_2805082 := by exact prefixLift 2805082
  have htrace : WordTrace (prefixWord ++ tailWord_2805082) baseStart_2805082 baseEnd_2805082 := by
    simpa [prefixWord, tailWord_2805082, baseEnd_2805082] using wordTrace_append hprefix tailTrace_2805082
  have hstable : (prefixWord ++ tailWord_2805082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805082).length < 2 ^ (prefixWord ++ tailWord_2805082).sum := by decide
  have hdescent : baseEnd_2805082 < baseStart_2805082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805097 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 6, 3]
def baseStart_2805097 : Nat := 118140960795 + 2805097 * 2 ^ 59
def prefixEnd_2805097 : Nat := 4983230072969 + 3 ^ 40 * 2805097 * 2
def baseEnd_2805097 : Nat := 960242028990077852524733

theorem tailTrace_2805097 : CollatzResearch.WordTrace tailWord_2805097 prefixEnd_2805097 960242028990077852524733 := by
  unfold tailWord_2805097
  simp only [CollatzResearch.WordTrace]
  refine ⟨102310292718620116271805545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68206861812413410847870363 102310292718620116271805545)
  ·
    refine ⟨76732719538965087203854159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102310292718620116271805545 76732719538965087203854159)
    ·
      refine ⟨115099079308447630805781239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76732719538965087203854159 115099079308447630805781239)
      ·
        refine ⟨172648618962671446208671859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115099079308447630805781239 172648618962671446208671859)
        ·
          refine ⟨258972928444007169313007789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172648618962671446208671859 258972928444007169313007789)
          ·
            refine ⟨97114848166502688492377921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258972928444007169313007789 97114848166502688492377921)
            ·
              refine ⟨72836136124877016369283441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97114848166502688492377921 72836136124877016369283441)
              ·
                refine ⟨54627102093657762276962581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72836136124877016369283441 54627102093657762276962581)
                ·
                  refine ⟨2560645410640207606732621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54627102093657762276962581 2560645410640207606732621)
                  ·
                    refine ⟨960242028990077852524733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2560645410640207606732621 960242028990077852524733)
                    ·
                      rfl

theorem cell22_2805097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 3].length) (baseStart_2805097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805097 prefixEnd_2805097 := by exact prefixLift 2805097
  have htrace : WordTrace (prefixWord ++ tailWord_2805097) baseStart_2805097 baseEnd_2805097 := by
    simpa [prefixWord, tailWord_2805097, baseEnd_2805097] using wordTrace_append hprefix tailTrace_2805097
  have hstable : (prefixWord ++ tailWord_2805097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805097).length < 2 ^ (prefixWord ++ tailWord_2805097).sum := by decide
  have hdescent : baseEnd_2805097 < baseStart_2805097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805101 : List Nat := [1, 5, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_2805101 : Nat := 118140960795 + 2805101 * 2 ^ 59
def prefixEnd_2805101 : Nat := 4983230072969 + 3 ^ 40 * 2805101 * 2
def baseEnd_2805101 : Nat := 960243398271823175424721

theorem tailTrace_2805101 : CollatzResearch.WordTrace tailWord_2805101 prefixEnd_2805101 960243398271823175424721 := by
  unfold tailWord_2805101
  simp only [CollatzResearch.WordTrace]
  refine ⟨102310438610605624954951157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68206959073737083303300771 102310438610605624954951157)
  ·
    refine ⟨9591603619744277339526671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102310438610605624954951157 9591603619744277339526671)
    ·
      refine ⟨14387405429616416009290007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9591603619744277339526671 14387405429616416009290007)
      ·
        refine ⟨21581108144424624013935011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14387405429616416009290007 21581108144424624013935011)
        ·
          refine ⟨32371662216636936020902517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21581108144424624013935011 32371662216636936020902517)
          ·
            refine ⟨3034843332809712751959611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32371662216636936020902517 3034843332809712751959611)
            ·
              refine ⟨4552264999214569127939417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034843332809712751959611 4552264999214569127939417)
              ·
                refine ⟨3414198749410926845954563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4552264999214569127939417 3414198749410926845954563)
                ·
                  refine ⟨5121298124116390268931845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3414198749410926845954563 5121298124116390268931845)
                  ·
                    refine ⟨960243398271823175424721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5121298124116390268931845 960243398271823175424721)
                    ·
                      rfl

theorem cell22_2805101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_2805101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805101 prefixEnd_2805101 := by exact prefixLift 2805101
  have htrace : WordTrace (prefixWord ++ tailWord_2805101) baseStart_2805101 baseEnd_2805101 := by
    simpa [prefixWord, tailWord_2805101, baseEnd_2805101] using wordTrace_append hprefix tailTrace_2805101
  have hstable : (prefixWord ++ tailWord_2805101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805101).length < 2 ^ (prefixWord ++ tailWord_2805101).sum := by decide
  have hdescent : baseEnd_2805101 < baseStart_2805101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805176 : List Nat := [2, 1, 2, 1, 2, 2, 3, 5, 1, 3]
def baseStart_2805176 : Nat := 118140960795 + 2805176 * 2 ^ 59
def prefixEnd_2805176 : Nat := 4983230072969 + 3 ^ 40 * 2805176 * 2
def baseEnd_2805176 : Nat := 960269072304547979799491

theorem tailTrace_2805176 : CollatzResearch.WordTrace tailWord_2805176 prefixEnd_2805176 960269072304547979799491 := by
  unfold tailWord_2805176
  simp only [CollatzResearch.WordTrace]
  refine ⟨51156587042666956381965691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68208782723555941842620921 51156587042666956381965691)
  ·
    refine ⟨76734880564000434572948537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51156587042666956381965691 76734880564000434572948537)
    ·
      refine ⟨57551160423000325929711403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76734880564000434572948537 57551160423000325929711403)
      ·
        refine ⟨86326740634500488894567105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57551160423000325929711403 86326740634500488894567105)
        ·
          refine ⟨64745055475875366670925329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86326740634500488894567105 64745055475875366670925329)
          ·
            refine ⟨48558791606906525003193997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64745055475875366670925329 48558791606906525003193997)
            ·
              refine ⟨18209546852589946876197749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48558791606906525003193997 18209546852589946876197749)
              ·
                refine ⟨1707145017430307519643539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18209546852589946876197749 1707145017430307519643539)
                ·
                  refine ⟨2560717526145461279465309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1707145017430307519643539 2560717526145461279465309)
                  ·
                    refine ⟨960269072304547979799491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2560717526145461279465309 960269072304547979799491)
                    ·
                      rfl

theorem cell22_2805176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_2805176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805176 prefixEnd_2805176 := by exact prefixLift 2805176
  have htrace : WordTrace (prefixWord ++ tailWord_2805176) baseStart_2805176 baseEnd_2805176 := by
    simpa [prefixWord, tailWord_2805176, baseEnd_2805176] using wordTrace_append hprefix tailTrace_2805176
  have hstable : (prefixWord ++ tailWord_2805176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805176).length < 2 ^ (prefixWord ++ tailWord_2805176).sum := by decide
  have hdescent : baseEnd_2805176 < baseStart_2805176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805187 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 2, 5]
def baseStart_2805187 : Nat := 118140960795 + 2805187 * 2 ^ 59
def prefixEnd_2805187 : Nat := 4983230072969 + 3 ^ 40 * 2805187 * 2
def baseEnd_2805187 : Nat := 960272837829347617774457

theorem tailTrace_2805187 : CollatzResearch.WordTrace tailWord_2805187 prefixEnd_2805187 960272837829347617774457 := by
  unfold tailWord_2805187
  simp only [CollatzResearch.WordTrace]
  refine ⟨102313575288294061642581815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68209050192196041095054543 102313575288294061642581815)
  ·
    refine ⟨153470362932441092463872723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102313575288294061642581815 153470362932441092463872723)
    ·
      refine ⟨230205544398661638695809085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153470362932441092463872723 230205544398661638695809085)
      ·
        refine ⟨86327079149498114510928407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230205544398661638695809085 86327079149498114510928407)
        ·
          refine ⟨129490618724247171766392611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86327079149498114510928407 129490618724247171766392611)
          ·
            refine ⟨194235928086370757649588917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129490618724247171766392611 194235928086370757649588917)
            ·
              refine ⟨18209618258097258529648961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 194235928086370757649588917 18209618258097258529648961)
              ·
                refine ⟨13657213693572943897236721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18209618258097258529648961 13657213693572943897236721)
                ·
                  refine ⟨10242910270179707922927541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13657213693572943897236721 10242910270179707922927541)
                  ·
                    refine ⟨960272837829347617774457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10242910270179707922927541 960272837829347617774457)
                    ·
                      rfl

theorem cell22_2805187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 5].length) (baseStart_2805187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805187 prefixEnd_2805187 := by exact prefixLift 2805187
  have htrace : WordTrace (prefixWord ++ tailWord_2805187) baseStart_2805187 baseEnd_2805187 := by
    simpa [prefixWord, tailWord_2805187, baseEnd_2805187] using wordTrace_append hprefix tailTrace_2805187
  have hstable : (prefixWord ++ tailWord_2805187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805187).length < 2 ^ (prefixWord ++ tailWord_2805187).sum := by decide
  have hdescent : baseEnd_2805187 < baseStart_2805187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805247 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 3, 6]
def baseStart_2805247 : Nat := 118140960795 + 2805247 * 2 ^ 59
def prefixEnd_2805247 : Nat := 4983230072969 + 3 ^ 40 * 2805247 * 2
def baseEnd_2805247 : Nat := 960293377055527461274273

theorem tailTrace_2805247 : CollatzResearch.WordTrace tailWord_2805247 prefixEnd_2805247 960293377055527461274273 := by
  unfold tailWord_2805247
  simp only [CollatzResearch.WordTrace]
  refine ⟨102315763668076691889765995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68210509112051127926510663 102315763668076691889765995)
  ·
    refine ⟨153473645502115037834648993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102315763668076691889765995 153473645502115037834648993)
    ·
      refine ⟨115105234126586278375986745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153473645502115037834648993 115105234126586278375986745)
      ·
        refine ⟨86328925594939708781990059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115105234126586278375986745 86328925594939708781990059)
        ·
          refine ⟨129493388392409563172985089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86328925594939708781990059 129493388392409563172985089)
          ·
            refine ⟨97120041294307172379738817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129493388392409563172985089 97120041294307172379738817)
            ·
              refine ⟨72840030970730379284804113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97120041294307172379738817 72840030970730379284804113)
              ·
                refine ⟨54630023228047784463603085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72840030970730379284804113 54630023228047784463603085)
                ·
                  refine ⟨20486258710517919173851157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54630023228047784463603085 20486258710517919173851157)
                  ·
                    refine ⟨960293377055527461274273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20486258710517919173851157 960293377055527461274273)
                    ·
                      rfl

theorem cell22_2805247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_2805247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805247 prefixEnd_2805247 := by exact prefixLift 2805247
  have htrace : WordTrace (prefixWord ++ tailWord_2805247) baseStart_2805247 baseEnd_2805247 := by
    simpa [prefixWord, tailWord_2805247, baseEnd_2805247] using wordTrace_append hprefix tailTrace_2805247
  have hstable : (prefixWord ++ tailWord_2805247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805247).length < 2 ^ (prefixWord ++ tailWord_2805247).sum := by decide
  have hdescent : baseEnd_2805247 < baseStart_2805247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805281 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 2, 4]
def baseStart_2805281 : Nat := 118140960795 + 2805281 * 2 ^ 59
def prefixEnd_2805281 : Nat := 4983230072969 + 3 ^ 40 * 2805281 * 2
def baseEnd_2805281 : Nat := 960305015950362705924169

theorem tailTrace_2805281 : CollatzResearch.WordTrace tailWord_2805281 prefixEnd_2805281 960305015950362705924169 := by
  unfold tailWord_2805281
  simp only [CollatzResearch.WordTrace]
  refine ⟨102317003749953515696503697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68211335833302343797669131 102317003749953515696503697)
  ·
    refine ⟨76737752812465136772377773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102317003749953515696503697 76737752812465136772377773)
    ·
      refine ⟨28776657304674426289641665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76737752812465136772377773 28776657304674426289641665)
      ·
        refine ⟨21582492978505819717231249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28776657304674426289641665 21582492978505819717231249)
        ·
          refine ⟨16186869733879364787923437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21582492978505819717231249 16186869733879364787923437)
          ·
            refine ⟨6070076150204761795471289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16186869733879364787923437 6070076150204761795471289)
            ·
              refine ⟨4552557112653571346603467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6070076150204761795471289 4552557112653571346603467)
              ·
                refine ⟨6828835668980357019905201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4552557112653571346603467 6828835668980357019905201)
                ·
                  refine ⟨5121626751735267764928901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6828835668980357019905201 5121626751735267764928901)
                  ·
                    refine ⟨960305015950362705924169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5121626751735267764928901 960305015950362705924169)
                    ·
                      rfl

theorem cell22_2805281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_2805281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805281 prefixEnd_2805281 := by exact prefixLift 2805281
  have htrace : WordTrace (prefixWord ++ tailWord_2805281) baseStart_2805281 baseEnd_2805281 := by
    simpa [prefixWord, tailWord_2805281, baseEnd_2805281] using wordTrace_append hprefix tailTrace_2805281
  have hstable : (prefixWord ++ tailWord_2805281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805281).length < 2 ^ (prefixWord ++ tailWord_2805281).sum := by decide
  have hdescent : baseEnd_2805281 < baseStart_2805281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805302 : List Nat := [5, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_2805302 : Nat := 118140960795 + 2805302 * 2 ^ 59
def prefixEnd_2805302 : Nat := 4983230072969 + 3 ^ 40 * 2805302 * 2
def baseEnd_2805302 : Nat := 320104068226508550383035

theorem tailTrace_2805302 : CollatzResearch.WordTrace tailWord_2805302 prefixEnd_2805302 320104068226508550383035 := by
  unfold tailWord_2805302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6394860605179839767688635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68211846455251624188678773 6394860605179839767688635)
  ·
    refine ⟨9592290907769759651532953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6394860605179839767688635 9592290907769759651532953)
    ·
      refine ⟨7194218180827319738649715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9592290907769759651532953 7194218180827319738649715)
      ·
        refine ⟨10791327271240979607974573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7194218180827319738649715 10791327271240979607974573)
        ·
          refine ⟨4046747726715367352990465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10791327271240979607974573 4046747726715367352990465)
          ·
            refine ⟨3035060795036525514742849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4046747726715367352990465 3035060795036525514742849)
            ·
              refine ⟨2276295596277394136057137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3035060795036525514742849 2276295596277394136057137)
              ·
                refine ⟨1707221697208045602042853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2276295596277394136057137 1707221697208045602042853)
                ·
                  refine ⟨320104068226508550383035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1707221697208045602042853 320104068226508550383035)
                  ·
                    rfl

theorem cell22_2805302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_2805302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805302 prefixEnd_2805302 := by exact prefixLift 2805302
  have htrace : WordTrace (prefixWord ++ tailWord_2805302) baseStart_2805302 baseEnd_2805302 := by
    simpa [prefixWord, tailWord_2805302, baseEnd_2805302] using wordTrace_append hprefix tailTrace_2805302
  have hstable : (prefixWord ++ tailWord_2805302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805302).length < 2 ^ (prefixWord ++ tailWord_2805302).sum := by decide
  have hdescent : baseEnd_2805302 < baseStart_2805302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805386 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 6]
def baseStart_2805386 : Nat := 118140960795 + 2805386 * 2 ^ 59
def prefixEnd_2805386 : Nat := 4983230072969 + 3 ^ 40 * 2805386 * 2
def baseEnd_2805386 : Nat := 320113653198725810682949

theorem tailTrace_2805386 : CollatzResearch.WordTrace tailWord_2805386 prefixEnd_2805386 320113653198725810682949 := by
  unfold tailWord_2805386
  simp only [CollatzResearch.WordTrace]
  refine ⟨25580208353643279657269003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68213888943048745752717341 25580208353643279657269003)
  ·
    refine ⟨38370312530464919485903505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25580208353643279657269003 38370312530464919485903505)
    ·
      refine ⟨28777734397848689614427629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38370312530464919485903505 28777734397848689614427629)
      ·
        refine ⟨10791650399193258605410361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28777734397848689614427629 10791650399193258605410361)
        ·
          refine ⟨8093737799394943954057771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10791650399193258605410361 8093737799394943954057771)
          ·
            refine ⟨12140606699092415931086657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8093737799394943954057771 12140606699092415931086657)
            ·
              refine ⟨9105455024319311948314993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12140606699092415931086657 9105455024319311948314993)
              ·
                refine ⟨6829091268239483961236245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9105455024319311948314993 6829091268239483961236245)
                ·
                  refine ⟨320113653198725810682949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6829091268239483961236245 320113653198725810682949)
                  ·
                    rfl

theorem cell22_2805386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_2805386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805386 prefixEnd_2805386 := by exact prefixLift 2805386
  have htrace : WordTrace (prefixWord ++ tailWord_2805386) baseStart_2805386 baseEnd_2805386 := by
    simpa [prefixWord, tailWord_2805386, baseEnd_2805386] using wordTrace_append hprefix tailTrace_2805386
  have hstable : (prefixWord ++ tailWord_2805386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805386).length < 2 ^ (prefixWord ++ tailWord_2805386).sum := by decide
  have hdescent : baseEnd_2805386 < baseStart_2805386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805431 : List Nat := [1, 1, 3, 1, 5, 2, 2, 7]
def baseStart_2805431 : Nat := 118140960795 + 2805431 * 2 ^ 59
def prefixEnd_2805431 : Nat := 4983230072969 + 3 ^ 40 * 2805431 * 2
def baseEnd_2805431 : Nat := 106706262668423590519301

theorem tailTrace_2805431 : CollatzResearch.WordTrace tailWord_2805431 prefixEnd_2805431 106706262668423590519301 := by
  unfold tailWord_2805431
  simp only [CollatzResearch.WordTrace]
  refine ⟨102322474699410091314464147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68214983132940060876309431 102322474699410091314464147)
  ·
    refine ⟨153483712049115136971696221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102322474699410091314464147 153483712049115136971696221)
    ·
      refine ⟨57556392018418176364386083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153483712049115136971696221 57556392018418176364386083)
      ·
        refine ⟨86334588027627264546579125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57556392018418176364386083 86334588027627264546579125)
        ·
          refine ⟨8093867627590056051241793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86334588027627264546579125 8093867627590056051241793)
          ·
            refine ⟨6070400720692542038431345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8093867627590056051241793 6070400720692542038431345)
            ·
              refine ⟨4552800540519406528823509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6070400720692542038431345 4552800540519406528823509)
              ·
                refine ⟨106706262668423590519301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4552800540519406528823509 106706262668423590519301)
                ·
                  rfl

theorem cell22_2805431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 7].length) (baseStart_2805431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805431 prefixEnd_2805431 := by exact prefixLift 2805431
  have htrace : WordTrace (prefixWord ++ tailWord_2805431) baseStart_2805431 baseEnd_2805431 := by
    simpa [prefixWord, tailWord_2805431, baseEnd_2805431] using wordTrace_append hprefix tailTrace_2805431
  have hstable : (prefixWord ++ tailWord_2805431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805431).length < 2 ^ (prefixWord ++ tailWord_2805431).sum := by decide
  have hdescent : baseEnd_2805431 < baseStart_2805431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805538 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 6]
def baseStart_2805538 : Nat := 118140960795 + 2805538 * 2 ^ 59
def prefixEnd_2805538 : Nat := 4983230072969 + 3 ^ 40 * 2805538 * 2
def baseEnd_2805538 : Nat := 320130997434166567416127

theorem tailTrace_2805538 : CollatzResearch.WordTrace tailWord_2805538 prefixEnd_2805538 320130997434166567416127 := by
  unfold tailWord_2805538
  simp only [CollatzResearch.WordTrace]
  refine ⟨25581594327505612147152317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68217584873348299059072845 25581594327505612147152317)
  ·
    refine ⟨9593097872814604555182119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25581594327505612147152317 9593097872814604555182119)
    ·
      refine ⟨14389646809221906832773179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9593097872814604555182119 14389646809221906832773179)
      ·
        refine ⟨21584470213832860249159769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14389646809221906832773179 21584470213832860249159769)
        ·
          refine ⟨16188352660374645186869827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21584470213832860249159769 16188352660374645186869827)
          ·
            refine ⟨24282528990561967780304741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16188352660374645186869827 24282528990561967780304741)
            ·
              refine ⟨4552974185730368958807139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24282528990561967780304741 4552974185730368958807139)
              ·
                refine ⟨6829461278595553438210709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4552974185730368958807139 6829461278595553438210709)
                ·
                  refine ⟨320130997434166567416127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6829461278595553438210709 320130997434166567416127)
                  ·
                    rfl

theorem cell22_2805538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_2805538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805538 prefixEnd_2805538 := by exact prefixLift 2805538
  have htrace : WordTrace (prefixWord ++ tailWord_2805538) baseStart_2805538 baseEnd_2805538 := by
    simpa [prefixWord, tailWord_2805538, baseEnd_2805538] using wordTrace_append hprefix tailTrace_2805538
  have hstable : (prefixWord ++ tailWord_2805538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805538).length < 2 ^ (prefixWord ++ tailWord_2805538).sum := by decide
  have hdescent : baseEnd_2805538 < baseStart_2805538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805551 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 4, 4]
def baseStart_2805551 : Nat := 118140960795 + 2805551 * 2 ^ 59
def prefixEnd_2805551 : Nat := 4983230072969 + 3 ^ 40 * 2805551 * 2
def baseEnd_2805551 : Nat := 960397442468172001673341

theorem tailTrace_2805551 : CollatzResearch.WordTrace tailWord_2805551 prefixEnd_2805551 960397442468172001673341 := by
  unfold tailWord_2805551
  simp only [CollatzResearch.WordTrace]
  refine ⟨102326851458975351808832507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68217900972650234539221671 102326851458975351808832507)
  ·
    refine ⟨153490277188463027713248761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102326851458975351808832507 153490277188463027713248761)
    ·
      refine ⟨115117707891347270784936571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153490277188463027713248761 115117707891347270784936571)
      ·
        refine ⟨172676561837020906177404857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115117707891347270784936571 172676561837020906177404857)
        ·
          refine ⟨129507421377765679633053643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172676561837020906177404857 129507421377765679633053643)
          ·
            refine ⟨194261132066648519449580465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129507421377765679633053643 194261132066648519449580465)
            ·
              refine ⟨145695849049986389587185349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194261132066648519449580465 145695849049986389587185349)
              ·
                refine ⟨27317971696872448047597253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145695849049986389587185349 27317971696872448047597253)
                ·
                  refine ⟨5122119693163584008924485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27317971696872448047597253 5122119693163584008924485)
                  ·
                    refine ⟨960397442468172001673341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5122119693163584008924485 960397442468172001673341)
                    ·
                      rfl

theorem cell22_2805551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_2805551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805551 prefixEnd_2805551 := by exact prefixLift 2805551
  have htrace : WordTrace (prefixWord ++ tailWord_2805551) baseStart_2805551 baseEnd_2805551 := by
    simpa [prefixWord, tailWord_2805551, baseEnd_2805551] using wordTrace_append hprefix tailTrace_2805551
  have hstable : (prefixWord ++ tailWord_2805551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805551).length < 2 ^ (prefixWord ++ tailWord_2805551).sum := by decide
  have hdescent : baseEnd_2805551 < baseStart_2805551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805553 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 1, 5]
def baseStart_2805553 : Nat := 118140960795 + 2805553 * 2 ^ 59
def prefixEnd_2805553 : Nat := 4983230072969 + 3 ^ 40 * 2805553 * 2
def baseEnd_2805553 : Nat := 960398127109044663123335

theorem tailTrace_2805553 : CollatzResearch.WordTrace tailWord_2805553 prefixEnd_2805553 960398127109044663123335 := by
  unfold tailWord_2805553
  simp only [CollatzResearch.WordTrace]
  refine ⟨102326924404968106150405313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68217949603312070766936875 102326924404968106150405313)
  ·
    refine ⟨76745193303726079612803985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102326924404968106150405313 76745193303726079612803985)
    ·
      refine ⟨57558894977794559709602989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76745193303726079612803985 57558894977794559709602989)
      ·
        refine ⟨21584585616672959891101121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57558894977794559709602989 21584585616672959891101121)
        ·
          refine ⟨16188439212504719918325841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21584585616672959891101121 16188439212504719918325841)
          ·
            refine ⟨12141329409378539938744381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16188439212504719918325841 12141329409378539938744381)
            ·
              refine ⟨4552998528516952477029143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12141329409378539938744381 4552998528516952477029143)
              ·
                refine ⟨6829497792775428715543715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4552998528516952477029143 6829497792775428715543715)
                ·
                  refine ⟨10244246689163143073315573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6829497792775428715543715 10244246689163143073315573)
                  ·
                    refine ⟨960398127109044663123335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10244246689163143073315573 960398127109044663123335)
                    ·
                      rfl

theorem cell22_2805553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_2805553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805553 prefixEnd_2805553 := by exact prefixLift 2805553
  have htrace : WordTrace (prefixWord ++ tailWord_2805553) baseStart_2805553 baseEnd_2805553 := by
    simpa [prefixWord, tailWord_2805553, baseEnd_2805553] using wordTrace_append hprefix tailTrace_2805553
  have hstable : (prefixWord ++ tailWord_2805553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805553).length < 2 ^ (prefixWord ++ tailWord_2805553).sum := by decide
  have hdescent : baseEnd_2805553 < baseStart_2805553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805604 : List Nat := [2, 3, 1, 1, 5, 2, 2, 1, 2, 3]
def baseStart_2805604 : Nat := 118140960795 + 2805604 * 2 ^ 59
def prefixEnd_2805604 : Nat := 4983230072969 + 3 ^ 40 * 2805604 * 2
def baseEnd_2805604 : Nat := 960415585451297530098179

theorem tailTrace_2805604 : CollatzResearch.WordTrace tailWord_2805604 prefixEnd_2805604 960415585451297530098179 := by
  unfold tailWord_2805604
  simp only [CollatzResearch.WordTrace]
  refine ⟨51164392263891670930255933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68219189685188894573674577 51164392263891670930255933)
  ·
    refine ⟨19186647098959376598845975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51164392263891670930255933 19186647098959376598845975)
    ·
      refine ⟨28779970648439064898268963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19186647098959376598845975 28779970648439064898268963)
      ·
        refine ⟨43169955972658597347403445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28779970648439064898268963 43169955972658597347403445)
        ·
          refine ⟨4047183372436743501319073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43169955972658597347403445 4047183372436743501319073)
          ·
            refine ⟨3035387529327557625989305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4047183372436743501319073 3035387529327557625989305)
            ·
              refine ⟨2276540646995668219491979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3035387529327557625989305 2276540646995668219491979)
              ·
                refine ⟨3414810970493502329237969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2276540646995668219491979 3414810970493502329237969)
                ·
                  refine ⟨2561108227870126746928477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3414810970493502329237969 2561108227870126746928477)
                  ·
                    refine ⟨960415585451297530098179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2561108227870126746928477 960415585451297530098179)
                    ·
                      rfl

theorem cell22_2805604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_2805604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805604 prefixEnd_2805604 := by exact prefixLift 2805604
  have htrace : WordTrace (prefixWord ++ tailWord_2805604) baseStart_2805604 baseEnd_2805604 := by
    simpa [prefixWord, tailWord_2805604, baseEnd_2805604] using wordTrace_append hprefix tailTrace_2805604
  have hstable : (prefixWord ++ tailWord_2805604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805604).length < 2 ^ (prefixWord ++ tailWord_2805604).sum := by decide
  have hdescent : baseEnd_2805604 < baseStart_2805604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805660 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 2, 5]
def baseStart_2805660 : Nat := 118140960795 + 2805660 * 2 ^ 59
def prefixEnd_2805660 : Nat := 4983230072969 + 3 ^ 40 * 2805660 * 2
def baseEnd_2805660 : Nat := 960434755395732050698007

theorem tailTrace_2805660 : CollatzResearch.WordTrace tailWord_2805660 prefixEnd_2805660 960434755395732050698007 := by
  unfold tailWord_2805660
  simp only [CollatzResearch.WordTrace]
  refine ⟨51165413507790231712275217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68220551343720308949700289 51165413507790231712275217)
  ·
    refine ⟨38374060130842673784206413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51165413507790231712275217 38374060130842673784206413)
    ·
      refine ⟨14390272549066002669077405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38374060130842673784206413 14390272549066002669077405)
      ·
        refine ⟨5396352205899751000904027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14390272549066002669077405 5396352205899751000904027)
        ·
          refine ⟨8094528308849626501356041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5396352205899751000904027 8094528308849626501356041)
          ·
            refine ⟨6070896231637219876017031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8094528308849626501356041 6070896231637219876017031)
            ·
              refine ⟨9106344347455829814025547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6070896231637219876017031 9106344347455829814025547)
              ·
                refine ⟨13659516521183744721038321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9106344347455829814025547 13659516521183744721038321)
                ·
                  refine ⟨10244637390887808540778741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13659516521183744721038321 10244637390887808540778741)
                  ·
                    refine ⟨960434755395732050698007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10244637390887808540778741 960434755395732050698007)
                    ·
                      rfl

theorem cell22_2805660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_2805660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805660 prefixEnd_2805660 := by exact prefixLift 2805660
  have htrace : WordTrace (prefixWord ++ tailWord_2805660) baseStart_2805660 baseEnd_2805660 := by
    simpa [prefixWord, tailWord_2805660, baseEnd_2805660] using wordTrace_append hprefix tailTrace_2805660
  have hstable : (prefixWord ++ tailWord_2805660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805660).length < 2 ^ (prefixWord ++ tailWord_2805660).sum := by decide
  have hdescent : baseEnd_2805660 < baseStart_2805660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805688 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 1, 5]
def baseStart_2805688 : Nat := 118140960795 + 2805688 * 2 ^ 59
def prefixEnd_2805688 : Nat := 4983230072969 + 3 ^ 40 * 2805688 * 2
def baseEnd_2805688 : Nat := 960444340367949310997921

theorem tailTrace_2805688 : CollatzResearch.WordTrace tailWord_2805688 prefixEnd_2805688 960444340367949310997921 := by
  unfold tailWord_2805688
  simp only [CollatzResearch.WordTrace]
  refine ⟨51165924129739512103284859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68221232172986016137713145 51165924129739512103284859)
  ·
    refine ⟨76748886194609268154927289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51165924129739512103284859 76748886194609268154927289)
    ·
      refine ⟨57561664645956951116195467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76748886194609268154927289 57561664645956951116195467)
      ·
        refine ⟨86342496968935426674293201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57561664645956951116195467 86342496968935426674293201)
        ·
          refine ⟨64756872726701570005719901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86342496968935426674293201 64756872726701570005719901)
          ·
            refine ⟨24283827272513088752144963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64756872726701570005719901 24283827272513088752144963)
            ·
              refine ⟨36425740908769633128217445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24283827272513088752144963 36425740908769633128217445)
              ·
                refine ⟨6829826420394306211540771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36425740908769633128217445 6829826420394306211540771)
                ·
                  refine ⟨10244739630591459317311157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6829826420394306211540771 10244739630591459317311157)
                  ·
                    refine ⟨960444340367949310997921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10244739630591459317311157 960444340367949310997921)
                    ·
                      rfl

theorem cell22_2805688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_2805688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805688 prefixEnd_2805688 := by exact prefixLift 2805688
  have htrace : WordTrace (prefixWord ++ tailWord_2805688) baseStart_2805688 baseEnd_2805688 := by
    simpa [prefixWord, tailWord_2805688, baseEnd_2805688] using wordTrace_append hprefix tailTrace_2805688
  have hstable : (prefixWord ++ tailWord_2805688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805688).length < 2 ^ (prefixWord ++ tailWord_2805688).sum := by decide
  have hdescent : baseEnd_2805688 < baseStart_2805688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805703 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 4, 4]
def baseStart_2805703 : Nat := 118140960795 + 2805703 * 2 ^ 59
def prefixEnd_2805703 : Nat := 4983230072969 + 3 ^ 40 * 2805703 * 2
def baseEnd_2805703 : Nat := 960449475174494271872875

theorem tailTrace_2805703 : CollatzResearch.WordTrace tailWord_2805703 prefixEnd_2805703 960449475174494271872875 := by
  unfold tailWord_2805703
  simp only [CollatzResearch.WordTrace]
  refine ⟨102332395354424681768365763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68221596902949787845577175 102332395354424681768365763)
  ·
    refine ⟨153498593031637022652548645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102332395354424681768365763 153498593031637022652548645)
    ·
      refine ⟨28780986193431941747352871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153498593031637022652548645 28780986193431941747352871)
      ·
        refine ⟨43171479290147912621029307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28780986193431941747352871 43171479290147912621029307)
        ·
          refine ⟨64757218935221868931543961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43171479290147912621029307 64757218935221868931543961)
          ·
            refine ⟨48567914201416401698657971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64757218935221868931543961 48567914201416401698657971)
            ·
              refine ⟨72851871302124602547986957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48567914201416401698657971 72851871302124602547986957)
              ·
                refine ⟨27319451738296725955495109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72851871302124602547986957 27319451738296725955495109)
                ·
                  refine ⟨5122397200930636116655333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27319451738296725955495109 5122397200930636116655333)
                  ·
                    refine ⟨960449475174494271872875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5122397200930636116655333 960449475174494271872875)
                    ·
                      rfl

theorem cell22_2805703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_2805703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805703 prefixEnd_2805703 := by exact prefixLift 2805703
  have htrace : WordTrace (prefixWord ++ tailWord_2805703) baseStart_2805703 baseEnd_2805703 := by
    simpa [prefixWord, tailWord_2805703, baseEnd_2805703] using wordTrace_append hprefix tailTrace_2805703
  have hstable : (prefixWord ++ tailWord_2805703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805703).length < 2 ^ (prefixWord ++ tailWord_2805703).sum := by decide
  have hdescent : baseEnd_2805703 < baseStart_2805703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805722 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 1, 5]
def baseStart_2805722 : Nat := 118140960795 + 2805722 * 2 ^ 59
def prefixEnd_2805722 : Nat := 4983230072969 + 3 ^ 40 * 2805722 * 2
def baseEnd_2805722 : Nat := 960455979262784555647817

theorem tailTrace_2805722 : CollatzResearch.WordTrace tailWord_2805722 prefixEnd_2805722 960455979262784555647817 := by
  unfold tailWord_2805722
  simp only [CollatzResearch.WordTrace]
  refine ⟨25583272085338962003326855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68222058894237232008871613 25583272085338962003326855)
  ·
    refine ⟨38374908128008443004990283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25583272085338962003326855 38374908128008443004990283)
    ·
      refine ⟨57562362192012664507485425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38374908128008443004990283 57562362192012664507485425)
      ·
        refine ⟨43171771644009498380614069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57562362192012664507485425 43171771644009498380614069)
        ·
          refine ⟨4047353591625890473182569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43171771644009498380614069 4047353591625890473182569)
          ·
            refine ⟨3035515193719417854886927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4047353591625890473182569 3035515193719417854886927)
            ·
              refine ⟨4553272790579126782330391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3035515193719417854886927 4553272790579126782330391)
              ·
                refine ⟨6829909185868690173495587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4553272790579126782330391 6829909185868690173495587)
                ·
                  refine ⟨10244863778803035260243381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6829909185868690173495587 10244863778803035260243381)
                  ·
                    refine ⟨960455979262784555647817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10244863778803035260243381 960455979262784555647817)
                    ·
                      rfl

theorem cell22_2805722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_2805722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805722 prefixEnd_2805722 := by exact prefixLift 2805722
  have htrace : WordTrace (prefixWord ++ tailWord_2805722) baseStart_2805722 baseEnd_2805722 := by
    simpa [prefixWord, tailWord_2805722, baseEnd_2805722] using wordTrace_append hprefix tailTrace_2805722
  have hstable : (prefixWord ++ tailWord_2805722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805722).length < 2 ^ (prefixWord ++ tailWord_2805722).sum := by decide
  have hdescent : baseEnd_2805722 < baseStart_2805722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805735 : List Nat := [1, 1, 5, 2, 3, 1, 1, 8]
def baseStart_2805735 : Nat := 118140960795 + 2805735 * 2 ^ 59
def prefixEnd_2805735 : Nat := 4983230072969 + 3 ^ 40 * 2805735 * 2
def baseEnd_2805735 : Nat := 106717825492050761674753

theorem tailTrace_2805735 : CollatzResearch.WordTrace tailWord_2805735 prefixEnd_2805735 106717825492050761674753 := by
  unfold tailWord_2805735
  simp only [CollatzResearch.WordTrace]
  refine ⟨102333562490308751233530659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68222374993539167489020439 102333562490308751233530659)
  ·
    refine ⟨153500343735463126850295989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102333562490308751233530659 153500343735463126850295989)
    ·
      refine ⟨14390657225199668142215249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153500343735463126850295989 14390657225199668142215249)
      ·
        refine ⟨10792992918899751106661437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14390657225199668142215249 10792992918899751106661437)
        ·
          refine ⟨4047372344587406664998039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10792992918899751106661437 4047372344587406664998039)
          ·
            refine ⟨6071058516881109997497059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4047372344587406664998039 6071058516881109997497059)
            ·
              refine ⟨9106587775321664996245589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6071058516881109997497059 9106587775321664996245589)
              ·
                refine ⟨106717825492050761674753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9106587775321664996245589 106717825492050761674753)
                ·
                  rfl

theorem cell22_2805735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 8].length) (baseStart_2805735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805735 prefixEnd_2805735 := by exact prefixLift 2805735
  have htrace : WordTrace (prefixWord ++ tailWord_2805735) baseStart_2805735 baseEnd_2805735 := by
    simpa [prefixWord, tailWord_2805735, baseEnd_2805735] using wordTrace_append hprefix tailTrace_2805735
  have hstable : (prefixWord ++ tailWord_2805735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805735).length < 2 ^ (prefixWord ++ tailWord_2805735).sum := by decide
  have hdescent : baseEnd_2805735 < baseStart_2805735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805741 : List Nat := [1, 5, 1, 4, 1, 2, 1, 3, 4]
def baseStart_2805741 : Nat := 118140960795 + 2805741 * 2 ^ 59
def prefixEnd_2805741 : Nat := 4983230072969 + 3 ^ 40 * 2805741 * 2
def baseEnd_2805741 : Nat := 320154161117024946474253

theorem tailTrace_2805741 : CollatzResearch.WordTrace tailWord_2805741 prefixEnd_2805741 320154161117024946474253 := by
  unfold tailWord_2805741
  simp only [CollatzResearch.WordTrace]
  refine ⟨102333781328287014258249077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68222520885524676172166051 102333781328287014258249077)
  ·
    refine ⟨9593791999526907586710851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102333781328287014258249077 9593791999526907586710851)
    ·
      refine ⟨14390687999290361380066277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9593791999526907586710851 14390687999290361380066277)
      ·
        refine ⟨2698253999866942758762427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14390687999290361380066277 2698253999866942758762427)
        ·
          refine ⟨4047380999800414138143641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2698253999866942758762427 4047380999800414138143641)
          ·
            refine ⟨3035535749850310603607731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4047380999800414138143641 3035535749850310603607731)
            ·
              refine ⟨4553303624775465905411597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3035535749850310603607731 4553303624775465905411597)
              ·
                refine ⟨1707488859290799714529349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4553303624775465905411597 1707488859290799714529349)
                ·
                  refine ⟨320154161117024946474253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1707488859290799714529349 320154161117024946474253)
                  ·
                    rfl

theorem cell22_2805741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_2805741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805741 prefixEnd_2805741 := by exact prefixLift 2805741
  have htrace : WordTrace (prefixWord ++ tailWord_2805741) baseStart_2805741 baseEnd_2805741 := by
    simpa [prefixWord, tailWord_2805741, baseEnd_2805741] using wordTrace_append hprefix tailTrace_2805741
  have hstable : (prefixWord ++ tailWord_2805741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805741).length < 2 ^ (prefixWord ++ tailWord_2805741).sum := by decide
  have hdescent : baseEnd_2805741 < baseStart_2805741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805767 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 3, 3]
def baseStart_2805767 : Nat := 118140960795 + 2805767 * 2 ^ 59
def prefixEnd_2805767 : Nat := 4983230072969 + 3 ^ 40 * 2805767 * 2
def baseEnd_2805767 : Nat := 960471383682419438272679

theorem tailTrace_2805767 : CollatzResearch.WordTrace tailWord_2805767 prefixEnd_2805767 960471383682419438272679 := by
  unfold tailWord_2805767
  simp only [CollatzResearch.WordTrace]
  refine ⟨102334729626192820698695555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68223153084128547132463703 102334729626192820698695555)
  ·
    refine ⟨153502094439289231048043333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102334729626192820698695555 153502094439289231048043333)
    ·
      refine ⟨28781642707366730821508125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153502094439289231048043333 28781642707366730821508125)
      ·
        refine ⟨10793116015262524058065547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28781642707366730821508125 10793116015262524058065547)
        ·
          refine ⟨16189674022893786087098321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10793116015262524058065547 16189674022893786087098321)
          ·
            refine ⟨12142255517170339565323741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16189674022893786087098321 12142255517170339565323741)
            ·
              refine ⟨4553345818938877336996403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12142255517170339565323741 4553345818938877336996403)
              ·
                refine ⟨6830018728408316005494605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4553345818938877336996403 6830018728408316005494605)
                ·
                  refine ⟨2561257023153118502060477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6830018728408316005494605 2561257023153118502060477)
                  ·
                    refine ⟨960471383682419438272679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2561257023153118502060477 960471383682419438272679)
                    ·
                      rfl

theorem cell22_2805767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_2805767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805767 prefixEnd_2805767 := by exact prefixLift 2805767
  have htrace : WordTrace (prefixWord ++ tailWord_2805767) baseStart_2805767 baseEnd_2805767 := by
    simpa [prefixWord, tailWord_2805767, baseEnd_2805767] using wordTrace_append hprefix tailTrace_2805767
  have hstable : (prefixWord ++ tailWord_2805767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805767).length < 2 ^ (prefixWord ++ tailWord_2805767).sum := by decide
  have hdescent : baseEnd_2805767 < baseStart_2805767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805773 : List Nat := [1, 7, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_2805773 : Nat := 118140960795 + 2805773 * 2 ^ 59
def prefixEnd_2805773 : Nat := 4983230072969 + 3 ^ 40 * 2805773 * 2
def baseEnd_2805773 : Nat := 960473437605037422622661

theorem tailTrace_2805773 : CollatzResearch.WordTrace tailWord_2805773 prefixEnd_2805773 960473437605037422622661 := by
  unfold tailWord_2805773
  simp only [CollatzResearch.WordTrace]
  refine ⟨102334948464171083723413973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68223298976114055815609315 102334948464171083723413973)
  ·
    refine ⟨2398475354629009774767515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 102334948464171083723413973 2398475354629009774767515)
    ·
      refine ⟨3597713031943514662151273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2398475354629009774767515 3597713031943514662151273)
      ·
        refine ⟨2698284773957635996613455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3597713031943514662151273 2698284773957635996613455)
        ·
          refine ⟨4047427160936453994920183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2698284773957635996613455 4047427160936453994920183)
          ·
            refine ⟨6071140741404680992380275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4047427160936453994920183 6071140741404680992380275)
            ·
              refine ⟨9106711112107021488570413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6071140741404680992380275 9106711112107021488570413)
              ·
                refine ⟨3415016667040133058213905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9106711112107021488570413 3415016667040133058213905)
                ·
                  refine ⟨2561262500280099793660429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3415016667040133058213905 2561262500280099793660429)
                  ·
                    refine ⟨960473437605037422622661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2561262500280099793660429 960473437605037422622661)
                    ·
                      rfl

theorem cell22_2805773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_2805773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805773 prefixEnd_2805773 := by exact prefixLift 2805773
  have htrace : WordTrace (prefixWord ++ tailWord_2805773) baseStart_2805773 baseEnd_2805773 := by
    simpa [prefixWord, tailWord_2805773, baseEnd_2805773] using wordTrace_append hprefix tailTrace_2805773
  have hstable : (prefixWord ++ tailWord_2805773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805773).length < 2 ^ (prefixWord ++ tailWord_2805773).sum := by decide
  have hdescent : baseEnd_2805773 < baseStart_2805773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805840 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 8, 3]
def baseStart_2805840 : Nat := 118140960795 + 2805840 * 2 ^ 59
def prefixEnd_2805840 : Nat := 4983230072969 + 3 ^ 40 * 2805840 * 2
def baseEnd_2805840 : Nat := 960496373074271581197455

theorem tailTrace_2805840 : CollatzResearch.WordTrace tailWord_2805840 prefixEnd_2805840 960496373074271581197455 := by
  unfold tailWord_2805840
  simp only [CollatzResearch.WordTrace]
  refine ⟨51168696077464177083051487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68224928103285569444068649 51168696077464177083051487)
  ·
    refine ⟨76753044116196265624577231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51168696077464177083051487 76753044116196265624577231)
    ·
      refine ⟨115129566174294398436865847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76753044116196265624577231 115129566174294398436865847)
      ·
        refine ⟨172694349261441597655298771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115129566174294398436865847 172694349261441597655298771)
        ·
          refine ⟨259041523892162396482948157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172694349261441597655298771 259041523892162396482948157)
          ·
            refine ⟨97140571459560898681105559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 259041523892162396482948157 97140571459560898681105559)
            ·
              refine ⟨145710857189341348021658339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97140571459560898681105559 145710857189341348021658339)
              ·
                refine ⟨218566285784012022032487509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145710857189341348021658339 218566285784012022032487509)
                ·
                  refine ⟨2561323661531390883193213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 218566285784012022032487509 2561323661531390883193213)
                  ·
                    refine ⟨960496373074271581197455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2561323661531390883193213 960496373074271581197455)
                    ·
                      rfl

theorem cell22_2805840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 8, 3].length) (baseStart_2805840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805840 prefixEnd_2805840 := by exact prefixLift 2805840
  have htrace : WordTrace (prefixWord ++ tailWord_2805840) baseStart_2805840 baseEnd_2805840 := by
    simpa [prefixWord, tailWord_2805840, baseEnd_2805840] using wordTrace_append hprefix tailTrace_2805840
  have hstable : (prefixWord ++ tailWord_2805840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805840).length < 2 ^ (prefixWord ++ tailWord_2805840).sum := by decide
  have hdescent : baseEnd_2805840 < baseStart_2805840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805842 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 6]
def baseStart_2805842 : Nat := 118140960795 + 2805842 * 2 ^ 59
def prefixEnd_2805842 : Nat := 4983230072969 + 3 ^ 40 * 2805842 * 2
def baseEnd_2805842 : Nat := 320165685905048080882483

theorem tailTrace_2805842 : CollatzResearch.WordTrace tailWord_2805842 prefixEnd_2805842 320165685905048080882483 := by
  unfold tailWord_2805842
  simp only [CollatzResearch.WordTrace]
  refine ⟨25584366275230277126918945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68224976733947405671783853 25584366275230277126918945)
  ·
    refine ⟨19188274706422707845189209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25584366275230277126918945 19188274706422707845189209)
    ·
      refine ⟨14391206029817030883891907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19188274706422707845189209 14391206029817030883891907)
      ·
        refine ⟨21586809044725546325837861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14391206029817030883891907 21586809044725546325837861)
        ·
          refine ⟨4047526695886039936094599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21586809044725546325837861 4047526695886039936094599)
          ·
            refine ⟨6071290043829059904141899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4047526695886039936094599 6071290043829059904141899)
            ·
              refine ⟨9106935065743589856212849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6071290043829059904141899 9106935065743589856212849)
              ·
                refine ⟨6830201299307692392159637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9106935065743589856212849 6830201299307692392159637)
                ·
                  refine ⟨320165685905048080882483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6830201299307692392159637 320165685905048080882483)
                  ·
                    rfl

theorem cell22_2805842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_2805842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805842 prefixEnd_2805842 := by exact prefixLift 2805842
  have htrace : WordTrace (prefixWord ++ tailWord_2805842) baseStart_2805842 baseEnd_2805842 := by
    simpa [prefixWord, tailWord_2805842, baseEnd_2805842] using wordTrace_append hprefix tailTrace_2805842
  have hstable : (prefixWord ++ tailWord_2805842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805842).length < 2 ^ (prefixWord ++ tailWord_2805842).sum := by decide
  have hdescent : baseEnd_2805842 < baseStart_2805842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805855 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 2, 4]
def baseStart_2805855 : Nat := 118140960795 + 2805855 * 2 ^ 59
def prefixEnd_2805855 : Nat := 4983230072969 + 3 ^ 40 * 2805855 * 2
def baseEnd_2805855 : Nat := 960501507880816542072409

theorem tailTrace_2805855 : CollatzResearch.WordTrace tailWord_2805855 prefixEnd_2805855 960501507880816542072409 := by
  unfold tailWord_2805855
  simp only [CollatzResearch.WordTrace]
  refine ⟨102337939249874011727899019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68225292833249341151932679 102337939249874011727899019)
  ·
    refine ⟨153506908874811017591848529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102337939249874011727899019 153506908874811017591848529)
    ·
      refine ⟨115130181656108263193886397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153506908874811017591848529 115130181656108263193886397)
      ·
        refine ⟨43173818121040598697707399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115130181656108263193886397 43173818121040598697707399)
        ·
          refine ⟨64760727181560898046561099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43173818121040598697707399 64760727181560898046561099)
          ·
            refine ⟨97141090772341347069841649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64760727181560898046561099 97141090772341347069841649)
            ·
              refine ⟨72855818079256010302381237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97141090772341347069841649 72855818079256010302381237)
              ·
                refine ⟨6830232944930250965848241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72855818079256010302381237 6830232944930250965848241)
                ·
                  refine ⟨5122674708697688224386181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6830232944930250965848241 5122674708697688224386181)
                  ·
                    refine ⟨960501507880816542072409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5122674708697688224386181 960501507880816542072409)
                    ·
                      rfl

theorem cell22_2805855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_2805855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805855 prefixEnd_2805855 := by exact prefixLift 2805855
  have htrace : WordTrace (prefixWord ++ tailWord_2805855) baseStart_2805855 baseEnd_2805855 := by
    simpa [prefixWord, tailWord_2805855, baseEnd_2805855] using wordTrace_append hprefix tailTrace_2805855
  have hstable : (prefixWord ++ tailWord_2805855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805855).length < 2 ^ (prefixWord ++ tailWord_2805855).sum := by decide
  have hdescent : baseEnd_2805855 < baseStart_2805855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805870 : List Nat := [4, 1, 2, 2, 1, 1, 11]
def baseStart_2805870 : Nat := 118140960795 + 2805870 * 2 ^ 59
def prefixEnd_2805870 : Nat := 4983230072969 + 3 ^ 40 * 2805870 * 2
def baseEnd_2805870 : Nat := 35574320099531907516569

theorem tailTrace_2805870 : CollatzResearch.WordTrace tailWord_2805870 prefixEnd_2805870 35574320099531907516569 := by
  unfold tailWord_2805870
  simp only [CollatzResearch.WordTrace]
  refine ⟨12792310793102458661211883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68225657563213112859796709 12792310793102458661211883)
  ·
    refine ⟨19188466189653687991817825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12792310793102458661211883 19188466189653687991817825)
    ·
      refine ⟨14391349642240265993863369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19188466189653687991817825 14391349642240265993863369)
      ·
        refine ⟨10793512231680199495397527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14391349642240265993863369 10793512231680199495397527)
        ·
          refine ⟨16190268347520299243096291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10793512231680199495397527 16190268347520299243096291)
          ·
            refine ⟨24285402521280448864644437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16190268347520299243096291 24285402521280448864644437)
            ·
              refine ⟨35574320099531907516569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24285402521280448864644437 35574320099531907516569)
              ·
                rfl

theorem cell22_2805870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 11].length) (baseStart_2805870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805870 prefixEnd_2805870 := by exact prefixLift 2805870
  have htrace : WordTrace (prefixWord ++ tailWord_2805870) baseStart_2805870 baseEnd_2805870 := by
    simpa [prefixWord, tailWord_2805870, baseEnd_2805870] using wordTrace_append hprefix tailTrace_2805870
  have hstable : (prefixWord ++ tailWord_2805870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805870).length < 2 ^ (prefixWord ++ tailWord_2805870).sum := by decide
  have hdescent : baseEnd_2805870 < baseStart_2805870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805874 : List Nat := [3, 2, 1, 2, 2, 2, 3, 2, 2, 3]
def baseStart_2805874 : Nat := 118140960795 + 2805874 * 2 ^ 59
def prefixEnd_2805874 : Nat := 4983230072969 + 3 ^ 40 * 2805874 * 2
def baseEnd_2805874 : Nat := 960508011969106825847351

theorem tailTrace_2805874 : CollatzResearch.WordTrace tailWord_2805874 prefixEnd_2805874 960508011969106825847351 := by
  unfold tailWord_2805874
  simp only [CollatzResearch.WordTrace]
  refine ⟨25584658059201294493210169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68225754824536785315227117 25584658059201294493210169)
  ·
    refine ⟨19188493544400970869907627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25584658059201294493210169 19188493544400970869907627)
    ·
      refine ⟨28782740316601456304861441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19188493544400970869907627 28782740316601456304861441)
      ·
        refine ⟨21587055237451092228646081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28782740316601456304861441 21587055237451092228646081)
        ·
          refine ⟨16190291428088319171484561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21587055237451092228646081 16190291428088319171484561)
          ·
            refine ⟨12142718571066239378613421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16190291428088319171484561 12142718571066239378613421)
            ·
              refine ⟨4553519464149839766980033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12142718571066239378613421 4553519464149839766980033)
              ·
                refine ⟨3415139598112379825235025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4553519464149839766980033 3415139598112379825235025)
                ·
                  refine ⟨2561354698584284868926269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3415139598112379825235025 2561354698584284868926269)
                  ·
                    refine ⟨960508011969106825847351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2561354698584284868926269 960508011969106825847351)
                    ·
                      rfl

theorem cell22_2805874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_2805874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805874 prefixEnd_2805874 := by exact prefixLift 2805874
  have htrace : WordTrace (prefixWord ++ tailWord_2805874) baseStart_2805874 baseEnd_2805874 := by
    simpa [prefixWord, tailWord_2805874, baseEnd_2805874] using wordTrace_append hprefix tailTrace_2805874
  have hstable : (prefixWord ++ tailWord_2805874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805874).length < 2 ^ (prefixWord ++ tailWord_2805874).sum := by decide
  have hdescent : baseEnd_2805874 < baseStart_2805874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805960 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 8]
def baseStart_2805960 : Nat := 118140960795 + 2805960 * 2 ^ 59
def prefixEnd_2805960 : Nat := 4983230072969 + 3 ^ 40 * 2805960 * 2
def baseEnd_2805960 : Nat := 320179150508877089399029

theorem tailTrace_2805960 : CollatzResearch.WordTrace tailWord_2805960 prefixEnd_2805960 320179150508877089399029 := by
  unfold tailWord_2805960
  simp only [CollatzResearch.WordTrace]
  refine ⟨51170884457246807330235667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68227845942995743106980889 51170884457246807330235667)
  ·
    refine ⟨76756326685870210995353501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51170884457246807330235667 76756326685870210995353501)
    ·
      refine ⟨28783622507201329123257563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76756326685870210995353501 28783622507201329123257563)
      ·
        refine ⟨43175433760801993684886345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28783622507201329123257563 43175433760801993684886345)
        ·
          refine ⟨32381575320601495263664759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43175433760801993684886345 32381575320601495263664759)
          ·
            refine ⟨48572362980902242895497139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32381575320601495263664759 48572362980902242895497139)
            ·
              refine ⟨72858544471353364343245709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48572362980902242895497139 72858544471353364343245709)
              ·
                refine ⟨27321954176757511628717141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72858544471353364343245709 27321954176757511628717141)
                ·
                  refine ⟨320179150508877089399029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27321954176757511628717141 320179150508877089399029)
                  ·
                    rfl

theorem cell22_2805960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 8].length) (baseStart_2805960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805960 prefixEnd_2805960 := by exact prefixLift 2805960
  have htrace : WordTrace (prefixWord ++ tailWord_2805960) baseStart_2805960 baseEnd_2805960 := by
    simpa [prefixWord, tailWord_2805960, baseEnd_2805960] using wordTrace_append hprefix tailTrace_2805960
  have hstable : (prefixWord ++ tailWord_2805960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805960).length < 2 ^ (prefixWord ++ tailWord_2805960).sum := by decide
  have hdescent : baseEnd_2805960 < baseStart_2805960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805962 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 3, 4]
def baseStart_2805962 : Nat := 118140960795 + 2805962 * 2 ^ 59
def prefixEnd_2805962 : Nat := 4983230072969 + 3 ^ 40 * 2805962 * 2
def baseEnd_2805962 : Nat := 960538136167503929647081

theorem tailTrace_2805962 : CollatzResearch.WordTrace tailWord_2805962 prefixEnd_2805962 960538136167503929647081 := by
  unfold tailWord_2805962
  simp only [CollatzResearch.WordTrace]
  refine ⟨25585460465121592250511035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68227894573657579334696093 25585460465121592250511035)
  ·
    refine ⟨38378190697682388375766553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25585460465121592250511035 38378190697682388375766553)
    ·
      refine ⟨28783643023261791281824915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38378190697682388375766553 28783643023261791281824915)
      ·
        refine ⟨43175464534892686922737373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28783643023261791281824915 43175464534892686922737373)
        ·
          refine ⟨16190799200584757596026515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43175464534892686922737373 16190799200584757596026515)
          ·
            refine ⟨24286198800877136394039773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16190799200584757596026515 24286198800877136394039773)
            ·
              refine ⟨9107324550328926147764915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24286198800877136394039773 9107324550328926147764915)
              ·
                refine ⟨13660986825493389221647373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9107324550328926147764915 13660986825493389221647373)
                ·
                  refine ⟨5122870059560020958117765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13660986825493389221647373 5122870059560020958117765)
                  ·
                    refine ⟨960538136167503929647081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5122870059560020958117765 960538136167503929647081)
                    ·
                      rfl

theorem cell22_2805962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_2805962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805962 prefixEnd_2805962 := by exact prefixLift 2805962
  have htrace : WordTrace (prefixWord ++ tailWord_2805962) baseStart_2805962 baseEnd_2805962 := by
    simpa [prefixWord, tailWord_2805962, baseEnd_2805962] using wordTrace_append hprefix tailTrace_2805962
  have hstable : (prefixWord ++ tailWord_2805962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805962).length < 2 ^ (prefixWord ++ tailWord_2805962).sum := by decide
  have hdescent : baseEnd_2805962 < baseStart_2805962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805987 : List Nat := [1, 1, 1, 8, 2, 1, 2, 2, 1, 3]
def baseStart_2805987 : Nat := 118140960795 + 2805987 * 2 ^ 59
def prefixEnd_2805987 : Nat := 4983230072969 + 3 ^ 40 * 2805987 * 2
def baseEnd_2805987 : Nat := 960546694178412197772005

theorem tailTrace_2805987 : CollatzResearch.WordTrace tailWord_2805987 prefixEnd_2805987 960546694178412197772005 := by
  unfold tailWord_2805987
  simp only [CollatzResearch.WordTrace]
  refine ⟨102342753685395798271704215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68228502456930532181136143 102342753685395798271704215)
  ·
    refine ⟨153514130528093697407556323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102342753685395798271704215 153514130528093697407556323)
    ·
      refine ⟨230271195792140546111334485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153514130528093697407556323 230271195792140546111334485)
      ·
        refine ⟨2698490575689147024742201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 230271195792140546111334485 2698490575689147024742201)
        ·
          refine ⟨2023867931766860268556651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2698490575689147024742201 2023867931766860268556651)
          ·
            refine ⟨3035801897650290402834977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2023867931766860268556651 3035801897650290402834977)
            ·
              refine ⟨2276851423237717802126233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3035801897650290402834977 2276851423237717802126233)
              ·
                refine ⟨1707638567428288351594675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2276851423237717802126233 1707638567428288351594675)
                ·
                  refine ⟨2561457851142432527392013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1707638567428288351594675 2561457851142432527392013)
                  ·
                    refine ⟨960546694178412197772005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2561457851142432527392013 960546694178412197772005)
                    ·
                      rfl

theorem cell22_2805987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 1, 3].length) (baseStart_2805987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805987 prefixEnd_2805987 := by exact prefixLift 2805987
  have htrace : WordTrace (prefixWord ++ tailWord_2805987) baseStart_2805987 baseEnd_2805987 := by
    simpa [prefixWord, tailWord_2805987, baseEnd_2805987] using wordTrace_append hprefix tailTrace_2805987
  have hstable : (prefixWord ++ tailWord_2805987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805987).length < 2 ^ (prefixWord ++ tailWord_2805987).sum := by decide
  have hdescent : baseEnd_2805987 < baseStart_2805987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805994 : List Nat := [3, 1, 3, 1, 1, 2, 3, 4, 4]
def baseStart_2805994 : Nat := 118140960795 + 2805994 * 2 ^ 59
def prefixEnd_2805994 : Nat := 4983230072969 + 3 ^ 40 * 2805994 * 2
def baseEnd_2805994 : Nat := 320183030140488837615661

theorem tailTrace_2805994 : CollatzResearch.WordTrace tailWord_2805994 prefixEnd_2805994 320183030140488837615661 := by
  unfold tailWord_2805994
  simp only [CollatzResearch.WordTrace]
  refine ⟨25585752249092609616802259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68228672664246958978139357 25585752249092609616802259)
  ·
    refine ⟨38378628373638914425203389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25585752249092609616802259 38378628373638914425203389)
    ·
      refine ⟨14391985640114592909451271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38378628373638914425203389 14391985640114592909451271)
      ·
        refine ⟨21587978460171889364176907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14391985640114592909451271 21587978460171889364176907)
        ·
          refine ⟨32381967690257834046265361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21587978460171889364176907 32381967690257834046265361)
          ·
            refine ⟨24286475767693375534699021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32381967690257834046265361 24286475767693375534699021)
            ·
              refine ⟨9107428412885015825512133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24286475767693375534699021 9107428412885015825512133)
              ·
                refine ⟨1707642827415940467283525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9107428412885015825512133 1707642827415940467283525)
                ·
                  refine ⟨320183030140488837615661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1707642827415940467283525 320183030140488837615661)
                  ·
                    rfl

theorem cell22_2805994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_2805994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2805994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2805994 prefixEnd_2805994 := by exact prefixLift 2805994
  have htrace : WordTrace (prefixWord ++ tailWord_2805994) baseStart_2805994 baseEnd_2805994 := by
    simpa [prefixWord, tailWord_2805994, baseEnd_2805994] using wordTrace_append hprefix tailTrace_2805994
  have hstable : (prefixWord ++ tailWord_2805994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805994).length < 2 ^ (prefixWord ++ tailWord_2805994).sum := by decide
  have hdescent : baseEnd_2805994 < baseStart_2805994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806024 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 2, 4]
def baseStart_2806024 : Nat := 118140960795 + 2806024 * 2 ^ 59
def prefixEnd_2806024 : Nat := 4983230072969 + 3 ^ 40 * 2806024 * 2
def baseEnd_2806024 : Nat := 960559360034556434596891

theorem tailTrace_2806024 : CollatzResearch.WordTrace tailWord_2806024 prefixEnd_2806024 960559360034556434596891 := by
  unfold tailWord_2806024
  simp only [CollatzResearch.WordTrace]
  refine ⟨51172051593130876795400563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68229402124174502393867417 51172051593130876795400563)
  ·
    refine ⟨76758077389696315193100845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51172051593130876795400563 76758077389696315193100845)
    ·
      refine ⟨28784279021136118197412817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76758077389696315193100845 28784279021136118197412817)
      ·
        refine ⟨21588209265852088648059613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28784279021136118197412817 21588209265852088648059613)
        ·
          refine ⟨8095578474694533243022355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21588209265852088648059613 8095578474694533243022355)
          ·
            refine ⟨12143367712041799864533533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8095578474694533243022355 12143367712041799864533533)
            ·
              refine ⟨4553762892015674949200075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12143367712041799864533533 4553762892015674949200075)
              ·
                refine ⟨6830644338023512423800113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4553762892015674949200075 6830644338023512423800113)
                ·
                  refine ⟨5122983253517634317850085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6830644338023512423800113 5122983253517634317850085)
                  ·
                    refine ⟨960559360034556434596891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5122983253517634317850085 960559360034556434596891)
                    ·
                      rfl

theorem cell22_2806024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_2806024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806024 prefixEnd_2806024 := by exact prefixLift 2806024
  have htrace : WordTrace (prefixWord ++ tailWord_2806024) baseStart_2806024 baseEnd_2806024 := by
    simpa [prefixWord, tailWord_2806024, baseEnd_2806024] using wordTrace_append hprefix tailTrace_2806024
  have hstable : (prefixWord ++ tailWord_2806024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806024).length < 2 ^ (prefixWord ++ tailWord_2806024).sum := by decide
  have hdescent : baseEnd_2806024 < baseStart_2806024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806212 : List Nat := [2, 3, 3, 2, 3, 1, 1, 2, 2, 3]
def baseStart_2806212 : Nat := 118140960795 + 2806212 * 2 ^ 59
def prefixEnd_2806212 : Nat := 4983230072969 + 3 ^ 40 * 2806212 * 2
def baseEnd_2806212 : Nat := 960623716276586610896315

theorem tailTrace_2806212 : CollatzResearch.WordTrace tailWord_2806212 prefixEnd_2806212 960623716276586610896315 := by
  unfold tailWord_2806212
  simp only [CollatzResearch.WordTrace]
  refine ⟨51175480054790330849322445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68233973406387107799096593 51175480054790330849322445)
  ·
    refine ⟨19190805020546374068495917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51175480054790330849322445 19190805020546374068495917)
    ·
      refine ⟨7196551882704890275685969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19190805020546374068495917 7196551882704890275685969)
      ·
        refine ⟨5397413912028667706764477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7196551882704890275685969 5397413912028667706764477)
        ·
          refine ⟨2024030217010750390036679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5397413912028667706764477 2024030217010750390036679)
          ·
            refine ⟨3036045325516125585055019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024030217010750390036679 3036045325516125585055019)
            ·
              refine ⟨4554067988274188377582529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3036045325516125585055019 4554067988274188377582529)
              ·
                refine ⟨3415550991205641283186897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4554067988274188377582529 3415550991205641283186897)
                ·
                  refine ⟨2561663243404230962390173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3415550991205641283186897 2561663243404230962390173)
                  ·
                    refine ⟨960623716276586610896315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2561663243404230962390173 960623716276586610896315)
                    ·
                      rfl

theorem cell22_2806212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_2806212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806212 prefixEnd_2806212 := by exact prefixLift 2806212
  have htrace : WordTrace (prefixWord ++ tailWord_2806212) baseStart_2806212 baseEnd_2806212 := by
    simpa [prefixWord, tailWord_2806212, baseEnd_2806212] using wordTrace_append hprefix tailTrace_2806212
  have hstable : (prefixWord ++ tailWord_2806212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806212).length < 2 ^ (prefixWord ++ tailWord_2806212).sum := by decide
  have hdescent : baseEnd_2806212 < baseStart_2806212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806234 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 2, 5]
def baseStart_2806234 : Nat := 118140960795 + 2806234 * 2 ^ 59
def prefixEnd_2806234 : Nat := 4983230072969 + 3 ^ 40 * 2806234 * 2
def baseEnd_2806234 : Nat := 960631247326185886846247

theorem tailTrace_2806234 : CollatzResearch.WordTrace tailWord_2806234 prefixEnd_2806234 960631247326185886846247 := by
  unfold tailWord_2806234
  simp only [CollatzResearch.WordTrace]
  refine ⟨25587940628875239863986439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68234508343667306303963837 25587940628875239863986439)
  ·
    refine ⟨38381910943312859795979659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25587940628875239863986439 38381910943312859795979659)
    ·
      refine ⟨57572866414969289693969489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38381910943312859795979659 57572866414969289693969489)
      ·
        refine ⟨43179649811226967270477117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57572866414969289693969489 43179649811226967270477117)
        ·
          refine ⟨16192368679210112726428919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43179649811226967270477117 16192368679210112726428919)
          ·
            refine ⟨24288553018815169089643379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16192368679210112726428919 24288553018815169089643379)
            ·
              refine ⟨36432829528222753634465069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24288553018815169089643379 36432829528222753634465069)
              ·
                refine ⟨13662311073083532612924401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36432829528222753634465069 13662311073083532612924401)
                ·
                  refine ⟨10246733304812649459693301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13662311073083532612924401 10246733304812649459693301)
                  ·
                    refine ⟨960631247326185886846247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10246733304812649459693301 960631247326185886846247)
                    ·
                      rfl

theorem cell22_2806234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_2806234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806234 prefixEnd_2806234 := by exact prefixLift 2806234
  have htrace : WordTrace (prefixWord ++ tailWord_2806234) baseStart_2806234 baseEnd_2806234 := by
    simpa [prefixWord, tailWord_2806234, baseEnd_2806234] using wordTrace_append hprefix tailTrace_2806234
  have hstable : (prefixWord ++ tailWord_2806234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806234).length < 2 ^ (prefixWord ++ tailWord_2806234).sum := by decide
  have hdescent : baseEnd_2806234 < baseStart_2806234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806242 : List Nat := [3, 3, 3, 2, 2, 1, 2, 6]
def baseStart_2806242 : Nat := 118140960795 + 2806242 * 2 ^ 59
def prefixEnd_2806242 : Nat := 4983230072969 + 3 ^ 40 * 2806242 * 2
def baseEnd_2806242 : Nat := 106737109543297392516247

theorem tailTrace_2806242 : CollatzResearch.WordTrace tailWord_2806242 prefixEnd_2806242 106737109543297392516247 := by
  unfold tailWord_2806242
  simp only [CollatzResearch.WordTrace]
  refine ⟨25588013574867994205559245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68234702866314651214824653 25588013574867994205559245)
  ·
    refine ⟨9595505090575497827084717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25588013574867994205559245 9595505090575497827084717)
    ·
      refine ⟨3598314408965811685156769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9595505090575497827084717 3598314408965811685156769)
      ·
        refine ⟨2698735806724358763867577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3598314408965811685156769 2698735806724358763867577)
        ·
          refine ⟨2024051855043269072900683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2698735806724358763867577 2024051855043269072900683)
          ·
            refine ⟨3036077782564903609351025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024051855043269072900683 3036077782564903609351025)
            ·
              refine ⟨2277058336923677707013269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3036077782564903609351025 2277058336923677707013269)
              ·
                refine ⟨106737109543297392516247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2277058336923677707013269 106737109543297392516247)
                ·
                  rfl

theorem cell22_2806242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 6].length) (baseStart_2806242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806242 prefixEnd_2806242 := by exact prefixLift 2806242
  have htrace : WordTrace (prefixWord ++ tailWord_2806242) baseStart_2806242 baseEnd_2806242 := by
    simpa [prefixWord, tailWord_2806242, baseEnd_2806242] using wordTrace_append hprefix tailTrace_2806242
  have hstable : (prefixWord ++ tailWord_2806242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806242).length < 2 ^ (prefixWord ++ tailWord_2806242).sum := by decide
  have hdescent : baseEnd_2806242 < baseStart_2806242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806274 : List Nat := [3, 4, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_2806274 : Nat := 118140960795 + 2806274 * 2 ^ 59
def prefixEnd_2806274 : Nat := 4983230072969 + 3 ^ 40 * 2806274 * 2
def baseEnd_2806274 : Nat := 960644940143639115846125

theorem tailTrace_2806274 : CollatzResearch.WordTrace tailWord_2806274 prefixEnd_2806274 960644940143639115846125 := by
  unfold tailWord_2806274
  simp only [CollatzResearch.WordTrace]
  refine ⟨25588305358839011571850469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68235480956904030858267917 25588305358839011571850469)
  ·
    refine ⟨4797807254782314669721963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25588305358839011571850469 4797807254782314669721963)
    ·
      refine ⟨7196710882173472004582945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4797807254782314669721963 7196710882173472004582945)
      ·
        refine ⟨5397533161630104003437209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7196710882173472004582945 5397533161630104003437209)
        ·
          refine ⟨4048149871222578002577907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5397533161630104003437209 4048149871222578002577907)
          ·
            refine ⟨6072224806833867003866861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4048149871222578002577907 6072224806833867003866861)
            ·
              refine ⟨2277084302562700126450073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6072224806833867003866861 2277084302562700126450073)
              ·
                refine ⟨1707813226922025094837555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2277084302562700126450073 1707813226922025094837555)
                ·
                  refine ⟨2561719840383037642256333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1707813226922025094837555 2561719840383037642256333)
                  ·
                    refine ⟨960644940143639115846125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2561719840383037642256333 960644940143639115846125)
                    ·
                      rfl

theorem cell22_2806274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_2806274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806274 prefixEnd_2806274 := by exact prefixLift 2806274
  have htrace : WordTrace (prefixWord ++ tailWord_2806274) baseStart_2806274 baseEnd_2806274 := by
    simpa [prefixWord, tailWord_2806274, baseEnd_2806274] using wordTrace_append hprefix tailTrace_2806274
  have hstable : (prefixWord ++ tailWord_2806274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806274).length < 2 ^ (prefixWord ++ tailWord_2806274).sum := by decide
  have hdescent : baseEnd_2806274 < baseStart_2806274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806309 : List Nat := [1, 3, 1, 2, 2, 1, 4, 8]
def baseStart_2806309 : Nat := 118140960795 + 2806309 * 2 ^ 59
def prefixEnd_2806309 : Nat := 4983230072969 + 3 ^ 40 * 2806309 * 2
def baseEnd_2806309 : Nat := 106739657928767854580113

theorem tailTrace_2806309 : CollatzResearch.WordTrace tailWord_2806309 prefixEnd_2806309 106739657928767854580113 := by
  unfold tailWord_2806309
  simp only [CollatzResearch.WordTrace]
  refine ⟨102354497990229247264925981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68236331993486164843283987 102354497990229247264925981)
  ·
    refine ⟨38382936746335967724347243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102354497990229247264925981 38382936746335967724347243)
    ·
      refine ⟨57574405119503951586520865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38382936746335967724347243 57574405119503951586520865)
      ·
        refine ⟨43180803839627963689890649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57574405119503951586520865 43180803839627963689890649)
        ·
          refine ⟨32385602879720972767417987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43180803839627963689890649 32385602879720972767417987)
          ·
            refine ⟨48578404319581459151126981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32385602879720972767417987 48578404319581459151126981)
            ·
              refine ⟨9108450809921523590836309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48578404319581459151126981 9108450809921523590836309)
              ·
                refine ⟨106739657928767854580113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9108450809921523590836309 106739657928767854580113)
                ·
                  rfl

theorem cell22_2806309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 8].length) (baseStart_2806309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806309 prefixEnd_2806309 := by exact prefixLift 2806309
  have htrace : WordTrace (prefixWord ++ tailWord_2806309) baseStart_2806309 baseEnd_2806309 := by
    simpa [prefixWord, tailWord_2806309, baseEnd_2806309] using wordTrace_append hprefix tailTrace_2806309
  have hstable : (prefixWord ++ tailWord_2806309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806309).length < 2 ^ (prefixWord ++ tailWord_2806309).sum := by decide
  have hdescent : baseEnd_2806309 < baseStart_2806309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806326 : List Nat := [5, 1, 2, 1, 2, 11]
def baseStart_2806326 : Nat := 118140960795 + 2806326 * 2 ^ 59
def prefixEnd_2806326 : Nat := 4983230072969 + 3 ^ 40 * 2806326 * 2
def baseEnd_2806326 : Nat := 11860033837115164364765

theorem tailTrace_2806326 : CollatzResearch.WordTrace tailWord_2806326 prefixEnd_2806326 11860033837115164364765 := by
  unfold tailWord_2806326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6397194876947978698018427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68236745354111772778863221 6397194876947978698018427)
  ·
    refine ⟨9595792315421968047027641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6397194876947978698018427 9595792315421968047027641)
    ·
      refine ⟨7196844236566476035270731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9595792315421968047027641 7196844236566476035270731)
      ·
        refine ⟨10795266354849714052906097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7196844236566476035270731 10795266354849714052906097)
        ·
          refine ⟨8096449766137285539679573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10795266354849714052906097 8096449766137285539679573)
          ·
            refine ⟨11860033837115164364765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8096449766137285539679573 11860033837115164364765)
            ·
              rfl

theorem cell22_2806326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 11].length) (baseStart_2806326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806326 prefixEnd_2806326 := by exact prefixLift 2806326
  have htrace : WordTrace (prefixWord ++ tailWord_2806326) baseStart_2806326 baseEnd_2806326 := by
    simpa [prefixWord, tailWord_2806326, baseEnd_2806326] using wordTrace_append hprefix tailTrace_2806326
  have hstable : (prefixWord ++ tailWord_2806326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806326).length < 2 ^ (prefixWord ++ tailWord_2806326).sum := by decide
  have hdescent : baseEnd_2806326 < baseStart_2806326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806426 : List Nat := [3, 1, 1, 6, 2, 1, 1, 3, 1, 3]
def baseStart_2806426 : Nat := 118140960795 + 2806426 * 2 ^ 59
def prefixEnd_2806426 : Nat := 4983230072969 + 3 ^ 40 * 2806426 * 2
def baseEnd_2806426 : Nat := 960696972849961386045659

theorem tailTrace_2806426 : CollatzResearch.WordTrace tailWord_2806426 prefixEnd_2806426 960696972849961386045659 := by
  unfold tailWord_2806426
  simp only [CollatzResearch.WordTrace]
  refine ⟨25589691332701344061733783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68239176887203584164623421 25589691332701344061733783)
  ·
    refine ⟨38384536999052016092600675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25589691332701344061733783 38384536999052016092600675)
    ·
      refine ⟨57576805498578024138901013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38384536999052016092600675 57576805498578024138901013)
      ·
        refine ⟨2698912757745844881510985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57576805498578024138901013 2698912757745844881510985)
        ·
          refine ⟨2024184568309383661133239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2698912757745844881510985 2024184568309383661133239)
          ·
            refine ⟨3036276852464075491699859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024184568309383661133239 3036276852464075491699859)
            ·
              refine ⟨4554415278696113237549789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3036276852464075491699859 4554415278696113237549789)
              ·
                refine ⟨1707905729511042464081171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4554415278696113237549789 1707905729511042464081171)
                ·
                  refine ⟨2561858594266563696121757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1707905729511042464081171 2561858594266563696121757)
                  ·
                    refine ⟨960696972849961386045659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2561858594266563696121757 960696972849961386045659)
                    ·
                      rfl

theorem cell22_2806426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_2806426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806426 prefixEnd_2806426 := by exact prefixLift 2806426
  have htrace : WordTrace (prefixWord ++ tailWord_2806426) baseStart_2806426 baseEnd_2806426 := by
    simpa [prefixWord, tailWord_2806426, baseEnd_2806426] using wordTrace_append hprefix tailTrace_2806426
  have hstable : (prefixWord ++ tailWord_2806426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806426).length < 2 ^ (prefixWord ++ tailWord_2806426).sum := by decide
  have hdescent : baseEnd_2806426 < baseStart_2806426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806448 : List Nat := [2, 1, 1, 1, 2, 1, 3, 6, 2, 3]
def baseStart_2806448 : Nat := 118140960795 + 2806448 * 2 ^ 59
def prefixEnd_2806448 : Nat := 4983230072969 + 3 ^ 40 * 2806448 * 2
def baseEnd_2806448 : Nat := 960704503899560661995591

theorem tailTrace_2806448 : CollatzResearch.WordTrace tailWord_2806448 prefixEnd_2806448 960704503899560661995591 := by
  unfold tailWord_2806448
  simp only [CollatzResearch.WordTrace]
  refine ⟨51179783868362837002117999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68239711824483782669490665 51179783868362837002117999)
  ·
    refine ⟨76769675802544255503176999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51179783868362837002117999 76769675802544255503176999)
    ·
      refine ⟨115154513703816383254765499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76769675802544255503176999 115154513703816383254765499)
      ·
        refine ⟨172731770555724574882148249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115154513703816383254765499 172731770555724574882148249)
        ·
          refine ⟨129548827916793431161611187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172731770555724574882148249 129548827916793431161611187)
          ·
            refine ⟨194323241875190146742416781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129548827916793431161611187 194323241875190146742416781)
            ·
              refine ⟨72871215703196305028406293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194323241875190146742416781 72871215703196305028406293)
              ·
                refine ⟨3415838236087326798206545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72871215703196305028406293 3415838236087326798206545)
                ·
                  refine ⟨2561878677065495098654909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3415838236087326798206545 2561878677065495098654909)
                  ·
                    refine ⟨960704503899560661995591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2561878677065495098654909 960704503899560661995591)
                    ·
                      rfl

theorem cell22_2806448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 2, 3].length) (baseStart_2806448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806448 prefixEnd_2806448 := by exact prefixLift 2806448
  have htrace : WordTrace (prefixWord ++ tailWord_2806448) baseStart_2806448 baseEnd_2806448 := by
    simpa [prefixWord, tailWord_2806448, baseEnd_2806448] using wordTrace_append hprefix tailTrace_2806448
  have hstable : (prefixWord ++ tailWord_2806448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806448).length < 2 ^ (prefixWord ++ tailWord_2806448).sum := by decide
  have hdescent : baseEnd_2806448 < baseStart_2806448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806461 : List Nat := [1, 4, 1, 2, 1, 3, 1, 9]
def baseStart_2806461 : Nat := 118140960795 + 2806461 * 2 ^ 59
def prefixEnd_2806461 : Nat := 4983230072969 + 3 ^ 40 * 2806461 * 2
def baseEnd_2806461 : Nat := 106745439340581440157839

theorem tailTrace_2806461 : CollatzResearch.WordTrace tailWord_2806461 prefixEnd_2806461 106745439340581440157839 := by
  unfold tailWord_2806461
  simp only [CollatzResearch.WordTrace]
  refine ⟨102360041885678577224459237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68240027923785718149639491 102360041885678577224459237)
  ·
    refine ⟨19192507853564733229586107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102360041885678577224459237 19192507853564733229586107)
    ·
      refine ⟨28788761780347099844379161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19192507853564733229586107 28788761780347099844379161)
      ·
        refine ⟨21591571335260324883284371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28788761780347099844379161 21591571335260324883284371)
        ·
          refine ⟨32387357002890487324926557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21591571335260324883284371 32387357002890487324926557)
          ·
            refine ⟨12145258876083932746847459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32387357002890487324926557 12145258876083932746847459)
            ·
              refine ⟨18217888314125899120271189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12145258876083932746847459 18217888314125899120271189)
              ·
                refine ⟨106745439340581440157839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18217888314125899120271189 106745439340581440157839)
                ·
                  rfl

theorem cell22_2806461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 9].length) (baseStart_2806461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806461 prefixEnd_2806461 := by exact prefixLift 2806461
  have htrace : WordTrace (prefixWord ++ tailWord_2806461) baseStart_2806461 baseEnd_2806461 := by
    simpa [prefixWord, tailWord_2806461, baseEnd_2806461] using wordTrace_append hprefix tailTrace_2806461
  have hstable : (prefixWord ++ tailWord_2806461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806461).length < 2 ^ (prefixWord ++ tailWord_2806461).sum := by decide
  have hdescent : baseEnd_2806461 < baseStart_2806461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806615 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 2, 4]
def baseStart_2806615 : Nat := 118140960795 + 2806615 * 2 ^ 59
def prefixEnd_2806615 : Nat := 4983230072969 + 3 ^ 40 * 2806615 * 2
def baseEnd_2806615 : Nat := 960761671412427893070079

theorem tailTrace_2806615 : CollatzResearch.WordTrace tailWord_2806615 prefixEnd_2806615 960761671412427893070079 := by
  unfold tailWord_2806615
  simp only [CollatzResearch.WordTrace]
  refine ⟨102365658727120661525565299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68243772484747107683710199 102365658727120661525565299)
  ·
    refine ⟨153548488090680992288347949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102365658727120661525565299 153548488090680992288347949)
    ·
      refine ⟨57580683034005372108130481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153548488090680992288347949 57580683034005372108130481)
      ·
        refine ⟨43185512275504029081097861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57580683034005372108130481 43185512275504029081097861)
        ·
          refine ⟨8097283551657005452705849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43185512275504029081097861 8097283551657005452705849)
          ·
            refine ⟨6072962663742754089529387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8097283551657005452705849 6072962663742754089529387)
            ·
              refine ⟨9109443995614131134294081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6072962663742754089529387 9109443995614131134294081)
              ·
                refine ⟨6832082996710598350720561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9109443995614131134294081 6832082996710598350720561)
                ·
                  refine ⟨5124062247532948763040421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6832082996710598350720561 5124062247532948763040421)
                  ·
                    refine ⟨960761671412427893070079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5124062247532948763040421 960761671412427893070079)
                    ·
                      rfl

theorem cell22_2806615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_2806615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806615 prefixEnd_2806615 := by exact prefixLift 2806615
  have htrace : WordTrace (prefixWord ++ tailWord_2806615) baseStart_2806615 baseEnd_2806615 := by
    simpa [prefixWord, tailWord_2806615, baseEnd_2806615] using wordTrace_append hprefix tailTrace_2806615
  have hstable : (prefixWord ++ tailWord_2806615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806615).length < 2 ^ (prefixWord ++ tailWord_2806615).sum := by decide
  have hdescent : baseEnd_2806615 < baseStart_2806615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806673 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 2, 5]
def baseStart_2806673 : Nat := 118140960795 + 2806673 * 2 ^ 59
def prefixEnd_2806673 : Nat := 4983230072969 + 3 ^ 40 * 2806673 * 2
def baseEnd_2806673 : Nat := 960781525997735075119901

theorem tailTrace_2806673 : CollatzResearch.WordTrace tailWord_2806673 prefixEnd_2806673 960781525997735075119901 := by
  unfold tailWord_2806673
  simp only [CollatzResearch.WordTrace]
  refine ⟨102367774160910537431176673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68245182773940358287451115 102367774160910537431176673)
  ·
    refine ⟨76775830620682903073382505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102367774160910537431176673 76775830620682903073382505)
    ·
      refine ⟨57581872965512177305036879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76775830620682903073382505 57581872965512177305036879)
      ·
        refine ⟨86372809448268265957555319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57581872965512177305036879 86372809448268265957555319)
        ·
          refine ⟨129559214172402398936332979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86372809448268265957555319 129559214172402398936332979)
          ·
            refine ⟨194338821258603598404499469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129559214172402398936332979 194338821258603598404499469)
            ·
              refine ⟨72877057971976349401687301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194338821258603598404499469 72877057971976349401687301)
              ·
                refine ⟨13664448369745565512816369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72877057971976349401687301 13664448369745565512816369)
                ·
                  refine ⟨10248336277309174134612277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13664448369745565512816369 10248336277309174134612277)
                  ·
                    refine ⟨960781525997735075119901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10248336277309174134612277 960781525997735075119901)
                    ·
                      rfl

theorem cell22_2806673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_2806673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806673 prefixEnd_2806673 := by exact prefixLift 2806673
  have htrace : WordTrace (prefixWord ++ tailWord_2806673) baseStart_2806673 baseEnd_2806673 := by
    simpa [prefixWord, tailWord_2806673, baseEnd_2806673] using wordTrace_append hprefix tailTrace_2806673
  have hstable : (prefixWord ++ tailWord_2806673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806673).length < 2 ^ (prefixWord ++ tailWord_2806673).sum := by decide
  have hdescent : baseEnd_2806673 < baseStart_2806673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806690 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_2806690 : Nat := 118140960795 + 2806690 * 2 ^ 59
def prefixEnd_2806690 : Nat := 4983230072969 + 3 ^ 40 * 2806690 * 2
def baseEnd_2806690 : Nat := 960787345445152697444849

theorem tailTrace_2806690 : CollatzResearch.WordTrace tailWord_2806690 prefixEnd_2806690 960787345445152697444849 := by
  unfold tailWord_2806690
  simp only [CollatzResearch.WordTrace]
  refine ⟨25592098550462237333636381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68245596134565966223030349 25592098550462237333636381)
  ·
    refine ⟨9597036956423339000113643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25592098550462237333636381 9597036956423339000113643)
    ·
      refine ⟨14395555434635008500170465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9597036956423339000113643 14395555434635008500170465)
      ·
        refine ⟨10796666575976256375127849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14395555434635008500170465 10796666575976256375127849)
        ·
          refine ⟨8097499931982192281345887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10796666575976256375127849 8097499931982192281345887)
          ·
            refine ⟨12146249897973288422018831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8097499931982192281345887 12146249897973288422018831)
            ·
              refine ⟨18219374846959932633028247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12146249897973288422018831 18219374846959932633028247)
              ·
                refine ⟨27329062270439898949542371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18219374846959932633028247 27329062270439898949542371)
                ·
                  refine ⟨40993593405659848424313557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27329062270439898949542371 40993593405659848424313557)
                  ·
                    refine ⟨960787345445152697444849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40993593405659848424313557 960787345445152697444849)
                    ·
                      rfl

theorem cell22_2806690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_2806690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806690 prefixEnd_2806690 := by exact prefixLift 2806690
  have htrace : WordTrace (prefixWord ++ tailWord_2806690) baseStart_2806690 baseEnd_2806690 := by
    simpa [prefixWord, tailWord_2806690, baseEnd_2806690] using wordTrace_append hprefix tailTrace_2806690
  have hstable : (prefixWord ++ tailWord_2806690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806690).length < 2 ^ (prefixWord ++ tailWord_2806690).sum := by decide
  have hdescent : baseEnd_2806690 < baseStart_2806690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806887 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 1, 5]
def baseStart_2806887 : Nat := 118140960795 + 2806887 * 2 ^ 59
def prefixEnd_2806887 : Nat := 4983230072969 + 3 ^ 40 * 2806887 * 2
def baseEnd_2806887 : Nat := 960854782571109850269245

theorem tailTrace_2806887 : CollatzResearch.WordTrace tailWord_2806887 prefixEnd_2806887 960854782571109850269245 := by
  unfold tailWord_2806887
  simp only [CollatzResearch.WordTrace]
  refine ⟨102375579382135251979466915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68250386254756834652977943 102375579382135251979466915)
  ·
    refine ⟨153563369073202877969200373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102375579382135251979466915 153563369073202877969200373)
    ·
      refine ⟨14396565850612769809612535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153563369073202877969200373 14396565850612769809612535)
      ·
        refine ⟨21594848775919154714418803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14396565850612769809612535 21594848775919154714418803)
        ·
          refine ⟨32392273163878732071628205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21594848775919154714418803 32392273163878732071628205)
          ·
            refine ⟨12147102436454524526860577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32392273163878732071628205 12147102436454524526860577)
            ·
              refine ⟨9110326827340893395145433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12147102436454524526860577 9110326827340893395145433)
              ·
                refine ⟨6832745120505670046359075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9110326827340893395145433 6832745120505670046359075)
                ·
                  refine ⟨10249117680758505069538613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6832745120505670046359075 10249117680758505069538613)
                  ·
                    refine ⟨960854782571109850269245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10249117680758505069538613 960854782571109850269245)
                    ·
                      rfl

theorem cell22_2806887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_2806887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806887 prefixEnd_2806887 := by exact prefixLift 2806887
  have htrace : WordTrace (prefixWord ++ tailWord_2806887) baseStart_2806887 baseEnd_2806887 := by
    simpa [prefixWord, tailWord_2806887, baseEnd_2806887] using wordTrace_append hprefix tailTrace_2806887
  have hstable : (prefixWord ++ tailWord_2806887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806887).length < 2 ^ (prefixWord ++ tailWord_2806887).sum := by decide
  have hdescent : baseEnd_2806887 < baseStart_2806887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806889 : List Nat := [1, 2, 1, 1, 1, 7, 2, 3, 4]
def baseStart_2806889 : Nat := 118140960795 + 2806889 * 2 ^ 59
def prefixEnd_2806889 : Nat := 4983230072969 + 3 ^ 40 * 2806889 * 2
def baseEnd_2806889 : Nat := 320285155737327503906413

theorem tailTrace_2806889 : CollatzResearch.WordTrace tailWord_2806889 prefixEnd_2806889 320285155737327503906413 := by
  unfold tailWord_2806889
  simp only [CollatzResearch.WordTrace]
  refine ⟨102375652328128006321039721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68250434885418670880693147 102375652328128006321039721)
  ·
    refine ⟨76781739246096004740779791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102375652328128006321039721 76781739246096004740779791)
    ·
      refine ⟨115172608869144007111169687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76781739246096004740779791 115172608869144007111169687)
      ·
        refine ⟨172758913303716010666754531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115172608869144007111169687 172758913303716010666754531)
        ·
          refine ⟨259138369955574016000131797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172758913303716010666754531 259138369955574016000131797)
          ·
            refine ⟨6073555545833766000003089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 259138369955574016000131797 6073555545833766000003089)
            ·
              refine ⟨4555166659375324500002317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6073555545833766000003089 4555166659375324500002317)
              ·
                refine ⟨1708187497265746687500869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4555166659375324500002317 1708187497265746687500869)
                ·
                  refine ⟨320285155737327503906413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1708187497265746687500869 320285155737327503906413)
                  ·
                    rfl

theorem cell22_2806889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 4].length) (baseStart_2806889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806889 prefixEnd_2806889 := by exact prefixLift 2806889
  have htrace : WordTrace (prefixWord ++ tailWord_2806889) baseStart_2806889 baseEnd_2806889 := by
    simpa [prefixWord, tailWord_2806889, baseEnd_2806889] using wordTrace_append hprefix tailTrace_2806889
  have hstable : (prefixWord ++ tailWord_2806889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806889).length < 2 ^ (prefixWord ++ tailWord_2806889).sum := by decide
  have hdescent : baseEnd_2806889 < baseStart_2806889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806904 : List Nat := [2, 1, 2, 1, 1, 1, 7, 2, 2, 3]
def baseStart_2806904 : Nat := 118140960795 + 2806904 * 2 ^ 59
def prefixEnd_2806904 : Nat := 4983230072969 + 3 ^ 40 * 2806904 * 2
def baseEnd_2806904 : Nat := 960860602018527472594193

theorem tailTrace_2806904 : CollatzResearch.WordTrace tailWord_2806904 prefixEnd_2806904 960860602018527472594193 := by
  unfold tailWord_2806904
  simp only [CollatzResearch.WordTrace]
  refine ⟨51188099711536831941417883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68250799615382442588557177 51188099711536831941417883)
  ·
    refine ⟨76782149567305247912126825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51188099711536831941417883 76782149567305247912126825)
    ·
      refine ⟨57586612175478935934095119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76782149567305247912126825 57586612175478935934095119)
      ·
        refine ⟨86379918263218403901142679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57586612175478935934095119 86379918263218403901142679)
        ·
          refine ⟨129569877394827605851714019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86379918263218403901142679 129569877394827605851714019)
          ·
            refine ⟨194354816092241408777571029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129569877394827605851714019 194354816092241408777571029)
            ·
              refine ⟨4555191002161908018224321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 194354816092241408777571029 4555191002161908018224321)
              ·
                refine ⟨3416393251621431013668241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4555191002161908018224321 3416393251621431013668241)
                ·
                  refine ⟨2562294938716073260251181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3416393251621431013668241 2562294938716073260251181)
                  ·
                    refine ⟨960860602018527472594193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2562294938716073260251181 960860602018527472594193)
                    ·
                      rfl

theorem cell22_2806904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_2806904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806904 prefixEnd_2806904 := by exact prefixLift 2806904
  have htrace : WordTrace (prefixWord ++ tailWord_2806904) baseStart_2806904 baseEnd_2806904 := by
    simpa [prefixWord, tailWord_2806904, baseEnd_2806904] using wordTrace_append hprefix tailTrace_2806904
  have hstable : (prefixWord ++ tailWord_2806904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806904).length < 2 ^ (prefixWord ++ tailWord_2806904).sum := by decide
  have hdescent : baseEnd_2806904 < baseStart_2806904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806921 : List Nat := [1, 2, 1, 1, 4, 4, 3, 1, 2, 3]
def baseStart_2806921 : Nat := 118140960795 + 2806921 * 2 ^ 59
def prefixEnd_2806921 : Nat := 4983230072969 + 3 ^ 40 * 2806921 * 2
def baseEnd_2806921 : Nat := 960866421465945094919141

theorem tailTrace_2806921 : CollatzResearch.WordTrace tailWord_2806921 prefixEnd_2806921 960866421465945094919141 := by
  unfold tailWord_2806921
  simp only [CollatzResearch.WordTrace]
  refine ⟨102376819464012075786204617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68251212976008050524136411 102376819464012075786204617)
  ·
    refine ⟨76782614598009056839653463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102376819464012075786204617 76782614598009056839653463)
    ·
      refine ⟨115173921897013585259480195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76782614598009056839653463 115173921897013585259480195)
      ·
        refine ⟨172760882845520377889220293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115173921897013585259480195 172760882845520377889220293)
        ·
          refine ⟨32392665533535070854228805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172760882845520377889220293 32392665533535070854228805)
          ·
            refine ⟨6073624787537825785167901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32392665533535070854228805 6073624787537825785167901)
            ·
              refine ⟨2277609295326684669437963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6073624787537825785167901 2277609295326684669437963)
              ·
                refine ⟨3416413942990027004156945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2277609295326684669437963 3416413942990027004156945)
                ·
                  refine ⟨2562310457242520253117709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3416413942990027004156945 2562310457242520253117709)
                  ·
                    refine ⟨960866421465945094919141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2562310457242520253117709 960866421465945094919141)
                    ·
                      rfl

theorem cell22_2806921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 2, 3].length) (baseStart_2806921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806921 prefixEnd_2806921 := by exact prefixLift 2806921
  have htrace : WordTrace (prefixWord ++ tailWord_2806921) baseStart_2806921 baseEnd_2806921 := by
    simpa [prefixWord, tailWord_2806921, baseEnd_2806921] using wordTrace_append hprefix tailTrace_2806921
  have hstable : (prefixWord ++ tailWord_2806921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806921).length < 2 ^ (prefixWord ++ tailWord_2806921).sum := by decide
  have hdescent : baseEnd_2806921 < baseStart_2806921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806962 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 7]
def baseStart_2806962 : Nat := 118140960795 + 2806962 * 2 ^ 59
def prefixEnd_2806962 : Nat := 4983230072969 + 3 ^ 40 * 2806962 * 2
def baseEnd_2806962 : Nat := 320293485534611551548005

theorem tailTrace_2806962 : CollatzResearch.WordTrace tailWord_2806962 prefixEnd_2806962 320293485534611551548005 := by
  unfold tailWord_2806962
  simp only [CollatzResearch.WordTrace]
  refine ⟨25594578714215884947111785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68252209904575693192298093 25594578714215884947111785)
  ·
    refine ⟨19195934035661913710333839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25594578714215884947111785 19195934035661913710333839)
    ·
      refine ⟨28793901053492870565500759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19195934035661913710333839 28793901053492870565500759)
      ·
        refine ⟨43190851580239305848251139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28793901053492870565500759 43190851580239305848251139)
        ·
          refine ⟨64786277370358958772376709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43190851580239305848251139 64786277370358958772376709)
          ·
            refine ⟨12147427006942304769820633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64786277370358958772376709 12147427006942304769820633)
            ·
              refine ⟨9110570255206728577365475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12147427006942304769820633 9110570255206728577365475)
              ·
                refine ⟨13665855382810092866048213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9110570255206728577365475 13665855382810092866048213)
                ·
                  refine ⟨320293485534611551548005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13665855382810092866048213 320293485534611551548005)
                  ·
                    rfl

theorem cell22_2806962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_2806962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2806962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2806962 prefixEnd_2806962 := by exact prefixLift 2806962
  have htrace : WordTrace (prefixWord ++ tailWord_2806962) baseStart_2806962 baseEnd_2806962 := by
    simpa [prefixWord, tailWord_2806962, baseEnd_2806962] using wordTrace_append hprefix tailTrace_2806962
  have hstable : (prefixWord ++ tailWord_2806962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806962).length < 2 ^ (prefixWord ++ tailWord_2806962).sum := by decide
  have hdescent : baseEnd_2806962 < baseStart_2806962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807039 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 1, 5]
def baseStart_2807039 : Nat := 118140960795 + 2807039 * 2 ^ 59
def prefixEnd_2807039 : Nat := 4983230072969 + 3 ^ 40 * 2807039 * 2
def baseEnd_2807039 : Nat := 960906815277432120468779

theorem tailTrace_2807039 : CollatzResearch.WordTrace tailWord_2807039 prefixEnd_2807039 960906815277432120468779 := by
  unfold tailWord_2807039
  simp only [CollatzResearch.WordTrace]
  refine ⟨102381123277584581939000171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68254082185056387959333447 102381123277584581939000171)
  ·
    refine ⟨153571684916376872908500257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102381123277584581939000171 153571684916376872908500257)
    ·
      refine ⟨115178763687282654681375193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153571684916376872908500257 115178763687282654681375193)
      ·
        refine ⟨86384072765461991011031395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115178763687282654681375193 86384072765461991011031395)
        ·
          refine ⟨129576109148192986516547093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86384072765461991011031395 129576109148192986516547093)
          ·
            refine ⟨6073880116321546242963145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129576109148192986516547093 6073880116321546242963145)
            ·
              refine ⟨4555410087241159682222359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6073880116321546242963145 4555410087241159682222359)
              ·
                refine ⟨6833115130861739523333539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555410087241159682222359 6833115130861739523333539)
                ·
                  refine ⟨10249672696292609285000309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6833115130861739523333539 10249672696292609285000309)
                  ·
                    refine ⟨960906815277432120468779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10249672696292609285000309 960906815277432120468779)
                    ·
                      rfl

theorem cell22_2807039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_2807039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807039 prefixEnd_2807039 := by exact prefixLift 2807039
  have htrace : WordTrace (prefixWord ++ tailWord_2807039) baseStart_2807039 baseEnd_2807039 := by
    simpa [prefixWord, tailWord_2807039, baseEnd_2807039] using wordTrace_append hprefix tailTrace_2807039
  have hstable : (prefixWord ++ tailWord_2807039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807039).length < 2 ^ (prefixWord ++ tailWord_2807039).sum := by decide
  have hdescent : baseEnd_2807039 < baseStart_2807039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807054 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_2807054 : Nat := 118140960795 + 2807054 * 2 ^ 59
def prefixEnd_2807054 : Nat := 4983230072969 + 3 ^ 40 * 2807054 * 2
def baseEnd_2807054 : Nat := 960911950083977081343733

theorem tailTrace_2807054 : CollatzResearch.WordTrace tailWord_2807054 prefixEnd_2807054 960911950083977081343733 := by
  unfold tailWord_2807054
  simp only [CollatzResearch.WordTrace]
  refine ⟨12797708796566279937599527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68254446915020159667197477 12797708796566279937599527)
  ·
    refine ⟨19196563194849419906399291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12797708796566279937599527 19196563194849419906399291)
    ·
      refine ⟨28794844792274129859598937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19196563194849419906399291 28794844792274129859598937)
      ·
        refine ⟨21596133594205597394699203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28794844792274129859598937 21596133594205597394699203)
        ·
          refine ⟨32394200391308396092048805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21596133594205597394699203 32394200391308396092048805)
          ·
            refine ⟨6073912573370324267259151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32394200391308396092048805 6073912573370324267259151)
            ·
              refine ⟨9110868860055486400888727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6073912573370324267259151 9110868860055486400888727)
              ·
                refine ⟨13666303290083229601333091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9110868860055486400888727 13666303290083229601333091)
                ·
                  refine ⟨20499454935124844401999637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13666303290083229601333091 20499454935124844401999637)
                  ·
                    refine ⟨960911950083977081343733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20499454935124844401999637 960911950083977081343733)
                    ·
                      rfl

theorem cell22_2807054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_2807054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807054 prefixEnd_2807054 := by exact prefixLift 2807054
  have htrace : WordTrace (prefixWord ++ tailWord_2807054) baseStart_2807054 baseEnd_2807054 := by
    simpa [prefixWord, tailWord_2807054, baseEnd_2807054] using wordTrace_append hprefix tailTrace_2807054
  have hstable : (prefixWord ++ tailWord_2807054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807054).length < 2 ^ (prefixWord ++ tailWord_2807054).sum := by decide
  have hdescent : baseEnd_2807054 < baseStart_2807054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807069 : List Nat := [1, 4, 2, 3, 1, 2, 9]
def baseStart_2807069 : Nat := 118140960795 + 2807069 * 2 ^ 59
def prefixEnd_2807069 : Nat := 4983230072969 + 3 ^ 40 * 2807069 * 2
def baseEnd_2807069 : Nat := 35589521662611927489581

theorem tailTrace_2807069 : CollatzResearch.WordTrace tailWord_2807069 prefixEnd_2807069 35589521662611927489581 := by
  unfold tailWord_2807069
  simp only [CollatzResearch.WordTrace]
  refine ⟨102382217467475897062592261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68254811644983931375061507 102382217467475897062592261)
  ·
    refine ⟨19196665775151730699236049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102382217467475897062592261 19196665775151730699236049)
    ·
      refine ⟨14397499331363798024427037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19196665775151730699236049 14397499331363798024427037)
      ·
        refine ⟨5399062249261424259160139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14397499331363798024427037 5399062249261424259160139)
        ·
          refine ⟨8098593373892136388740209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5399062249261424259160139 8098593373892136388740209)
          ·
            refine ⟨6073945030419102291555157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8098593373892136388740209 6073945030419102291555157)
            ·
              refine ⟨35589521662611927489581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6073945030419102291555157 35589521662611927489581)
              ·
                rfl

theorem cell22_2807069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 9].length) (baseStart_2807069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807069 prefixEnd_2807069 := by exact prefixLift 2807069
  have htrace : WordTrace (prefixWord ++ tailWord_2807069) baseStart_2807069 baseEnd_2807069 := by
    simpa [prefixWord, tailWord_2807069, baseEnd_2807069] using wordTrace_append hprefix tailTrace_2807069
  have hstable : (prefixWord ++ tailWord_2807069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807069).length < 2 ^ (prefixWord ++ tailWord_2807069).sum := by decide
  have hdescent : baseEnd_2807069 < baseStart_2807069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807148 : List Nat := [2, 2, 1, 1, 5, 3, 2, 1, 5]
def baseStart_2807148 : Nat := 118140960795 + 2807148 * 2 ^ 59
def prefixEnd_2807148 : Nat := 4983230072969 + 3 ^ 40 * 2807148 * 2
def baseEnd_2807148 : Nat := 320314709401664056497815

theorem tailTrace_2807148 : CollatzResearch.WordTrace tailWord_2807148 prefixEnd_2807148 320314709401664056497815 := by
  unfold tailWord_2807148
  simp only [CollatzResearch.WordTrace]
  refine ⟨51192549417094846777359049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68256732556126462369812065 51192549417094846777359049)
  ·
    refine ⟨38394412062821135083019287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51192549417094846777359049 38394412062821135083019287)
    ·
      refine ⟨57591618094231702624528931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38394412062821135083019287 57591618094231702624528931)
      ·
        refine ⟨86387427141347553936793397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57591618094231702624528931 86387427141347553936793397)
        ·
          refine ⟨8098821294501333181574381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86387427141347553936793397 8098821294501333181574381)
          ·
            refine ⟨3037057985437999943090393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8098821294501333181574381 3037057985437999943090393)
            ·
              refine ⟨2277793489078499957317795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3037057985437999943090393 2277793489078499957317795)
              ·
                refine ⟨3416690233617749935976693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2277793489078499957317795 3416690233617749935976693)
                ·
                  refine ⟨320314709401664056497815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3416690233617749935976693 320314709401664056497815)
                  ·
                    rfl

theorem cell22_2807148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_2807148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807148 prefixEnd_2807148 := by exact prefixLift 2807148
  have htrace : WordTrace (prefixWord ++ tailWord_2807148) baseStart_2807148 baseEnd_2807148 := by
    simpa [prefixWord, tailWord_2807148, baseEnd_2807148] using wordTrace_append hprefix tailTrace_2807148
  have hstable : (prefixWord ++ tailWord_2807148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807148).length < 2 ^ (prefixWord ++ tailWord_2807148).sum := by decide
  have hdescent : baseEnd_2807148 < baseStart_2807148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807161 : List Nat := [1, 2, 1, 3, 2, 1, 5, 2, 1, 4]
def baseStart_2807161 : Nat := 118140960795 + 2807161 * 2 ^ 59
def prefixEnd_2807161 : Nat := 4983230072969 + 3 ^ 40 * 2807161 * 2
def baseEnd_2807161 : Nat := 960948578370664468918405

theorem tailTrace_2807161 : CollatzResearch.WordTrace tailWord_2807161 prefixEnd_2807161 960948578370664468918405 := by
  unfold tailWord_2807161
  simp only [CollatzResearch.WordTrace]
  refine ⟨102385572983142596774941337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68257048655428397849960891 102385572983142596774941337)
  ·
    refine ⟨76789179737356947581206003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102385572983142596774941337 76789179737356947581206003)
    ·
      refine ⟨115183769606035421371809005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76789179737356947581206003 115183769606035421371809005)
      ·
        refine ⟨43193913602263283014428377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115183769606035421371809005 43193913602263283014428377)
        ·
          refine ⟨32395435201697462260821283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43193913602263283014428377 32395435201697462260821283)
          ·
            refine ⟨48593152802546193391231925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32395435201697462260821283 48593152802546193391231925)
            ·
              refine ⟨4555608075238705630427993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48593152802546193391231925 4555608075238705630427993)
              ·
                refine ⟨3416706056429029222820995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4555608075238705630427993 3416706056429029222820995)
                ·
                  refine ⟨5125059084643543834231493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3416706056429029222820995 5125059084643543834231493)
                  ·
                    refine ⟨960948578370664468918405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5125059084643543834231493 960948578370664468918405)
                    ·
                      rfl

theorem cell22_2807161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 4].length) (baseStart_2807161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807161 prefixEnd_2807161 := by exact prefixLift 2807161
  have htrace : WordTrace (prefixWord ++ tailWord_2807161) baseStart_2807161 baseEnd_2807161 := by
    simpa [prefixWord, tailWord_2807161, baseEnd_2807161] using wordTrace_append hprefix tailTrace_2807161
  have hstable : (prefixWord ++ tailWord_2807161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807161).length < 2 ^ (prefixWord ++ tailWord_2807161).sum := by decide
  have hdescent : baseEnd_2807161 < baseStart_2807161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807186 : List Nat := [3, 2, 3, 3, 2, 1, 2, 2, 1, 3]
def baseStart_2807186 : Nat := 118140960795 + 2807186 * 2 ^ 59
def prefixEnd_2807186 : Nat := 4983230072969 + 3 ^ 40 * 2807186 * 2
def baseEnd_2807186 : Nat := 960957136381572737043329

theorem tailTrace_2807186 : CollatzResearch.WordTrace tailWord_2807186 prefixEnd_2807186 960957136381572737043329 := by
  unfold tailWord_2807186
  simp only [CollatzResearch.WordTrace]
  refine ⟨25596621202013006511150353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68257656538701350696400941 25596621202013006511150353)
  ·
    refine ⟨19197465901509754883362765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25596621202013006511150353 19197465901509754883362765)
    ·
      refine ⟨7199049713066158081261037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19197465901509754883362765 7199049713066158081261037)
      ·
        refine ⟨2699643642399809280472889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7199049713066158081261037 2699643642399809280472889)
        ·
          refine ⟨2024732731799856960354667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2699643642399809280472889 2024732731799856960354667)
          ·
            refine ⟨3037099097699785440532001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024732731799856960354667 3037099097699785440532001)
            ·
              refine ⟨2277824323274839080399001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3037099097699785440532001 2277824323274839080399001)
              ·
                refine ⟨1708368242456129310299251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2277824323274839080399001 1708368242456129310299251)
                ·
                  refine ⟨2562552363684193965448877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1708368242456129310299251 2562552363684193965448877)
                  ·
                    refine ⟨960957136381572737043329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2562552363684193965448877 960957136381572737043329)
                    ·
                      rfl

theorem cell22_2807186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_2807186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807186 prefixEnd_2807186 := by exact prefixLift 2807186
  have htrace : WordTrace (prefixWord ++ tailWord_2807186) baseStart_2807186 baseEnd_2807186 := by
    simpa [prefixWord, tailWord_2807186, baseEnd_2807186] using wordTrace_append hprefix tailTrace_2807186
  have hstable : (prefixWord ++ tailWord_2807186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807186).length < 2 ^ (prefixWord ++ tailWord_2807186).sum := by decide
  have hdescent : baseEnd_2807186 < baseStart_2807186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807193 : List Nat := [1, 2, 1, 2, 1, 5, 4, 2, 4]
def baseStart_2807193 : Nat := 118140960795 + 2807193 * 2 ^ 59
def prefixEnd_2807193 : Nat := 4983230072969 + 3 ^ 40 * 2807193 * 2
def baseEnd_2807193 : Nat := 320319844208209017372769

theorem tailTrace_2807193 : CollatzResearch.WordTrace tailWord_2807193 prefixEnd_2807193 320319844208209017372769 := by
  unfold tailWord_2807193
  simp only [CollatzResearch.WordTrace]
  refine ⟨102386740119026666240106233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68257826746017777493404155 102386740119026666240106233)
  ·
    refine ⟨76790055089269999680079675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102386740119026666240106233 76790055089269999680079675)
    ·
      refine ⟨115185082633904999520119513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76790055089269999680079675 115185082633904999520119513)
      ·
        refine ⟨86388811975428749640089635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115185082633904999520119513 86388811975428749640089635)
        ·
          refine ⟨129583217963143124460134453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86388811975428749640089635 129583217963143124460134453)
          ·
            refine ⟨12148426684044667918137605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129583217963143124460134453 12148426684044667918137605)
            ·
              refine ⟨2277830003258375234650801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12148426684044667918137605 2277830003258375234650801)
              ·
                refine ⟨1708372502443781425988101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2277830003258375234650801 1708372502443781425988101)
                ·
                  refine ⟨320319844208209017372769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1708372502443781425988101 320319844208209017372769)
                  ·
                    rfl

theorem cell22_2807193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 4].length) (baseStart_2807193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807193 prefixEnd_2807193 := by exact prefixLift 2807193
  have htrace : WordTrace (prefixWord ++ tailWord_2807193) baseStart_2807193 baseEnd_2807193 := by
    simpa [prefixWord, tailWord_2807193, baseEnd_2807193] using wordTrace_append hprefix tailTrace_2807193
  have hstable : (prefixWord ++ tailWord_2807193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807193).length < 2 ^ (prefixWord ++ tailWord_2807193).sum := by decide
  have hdescent : baseEnd_2807193 < baseStart_2807193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807253 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 3, 3]
def baseStart_2807253 : Nat := 118140960795 + 2807253 * 2 ^ 59
def prefixEnd_2807253 : Nat := 4983230072969 + 3 ^ 40 * 2807253 * 2
def baseEnd_2807253 : Nat := 960980071850806895618123

theorem tailTrace_2807253 : CollatzResearch.WordTrace tailWord_2807253 prefixEnd_2807253 960980071850806895618123 := by
  unfold tailWord_2807253
  simp only [CollatzResearch.WordTrace]
  refine ⟨102388928498809296487290413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68259285665872864324860275 102388928498809296487290413)
  ·
    refine ⟨38395848187053486182733905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102388928498809296487290413 38395848187053486182733905)
    ·
      refine ⟨28796886140290114637050429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38395848187053486182733905 28796886140290114637050429)
      ·
        refine ⟨10798832302608792988893911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28796886140290114637050429 10798832302608792988893911)
        ·
          refine ⟨16198248453913189483340867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10798832302608792988893911 16198248453913189483340867)
          ·
            refine ⟨24297372680869784225011301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16198248453913189483340867 24297372680869784225011301)
            ·
              refine ⟨4555757377663084542189619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24297372680869784225011301 4555757377663084542189619)
              ·
                refine ⟨6833636066494626813284429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555757377663084542189619 6833636066494626813284429)
                ·
                  refine ⟨2562613524935485054981661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6833636066494626813284429 2562613524935485054981661)
                  ·
                    refine ⟨960980071850806895618123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2562613524935485054981661 960980071850806895618123)
                    ·
                      rfl

theorem cell22_2807253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_2807253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807253 prefixEnd_2807253 := by exact prefixLift 2807253
  have htrace : WordTrace (prefixWord ++ tailWord_2807253) baseStart_2807253 baseEnd_2807253 := by
    simpa [prefixWord, tailWord_2807253, baseEnd_2807253] using wordTrace_append hprefix tailTrace_2807253
  have hstable : (prefixWord ++ tailWord_2807253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807253).length < 2 ^ (prefixWord ++ tailWord_2807253).sum := by decide
  have hdescent : baseEnd_2807253 < baseStart_2807253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807264 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 1, 7]
def baseStart_2807264 : Nat := 118140960795 + 2807264 * 2 ^ 59
def prefixEnd_2807264 : Nat := 4983230072969 + 3 ^ 40 * 2807264 * 2
def baseEnd_2807264 : Nat := 960983837375606533593089

theorem tailTrace_2807264 : CollatzResearch.WordTrace tailWord_2807264 prefixEnd_2807264 960983837375606533593089 := by
  unfold tailWord_2807264
  simp only [CollatzResearch.WordTrace]
  refine ⟨51194664850884722682970423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68259553134512963577293897 51194664850884722682970423)
  ·
    refine ⟨76791997276327084024455635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51194664850884722682970423 76791997276327084024455635)
    ·
      refine ⟨115187995914490626036683453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76791997276327084024455635 115187995914490626036683453)
      ·
        refine ⟨43195498467933984763756295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115187995914490626036683453 43195498467933984763756295)
        ·
          refine ⟨64793247701900977145634443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43195498467933984763756295 64793247701900977145634443)
          ·
            refine ⟨97189871552851465718451665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64793247701900977145634443 97189871552851465718451665)
            ·
              refine ⟨72892403664638599288838749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97189871552851465718451665 72892403664638599288838749)
              ·
                refine ⟨27334651374239474733314531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72892403664638599288838749 27334651374239474733314531)
                ·
                  refine ⟨41001977061359212099971797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27334651374239474733314531 41001977061359212099971797)
                  ·
                    refine ⟨960983837375606533593089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41001977061359212099971797 960983837375606533593089)
                    ·
                      rfl

theorem cell22_2807264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_2807264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807264 prefixEnd_2807264 := by exact prefixLift 2807264
  have htrace : WordTrace (prefixWord ++ tailWord_2807264) baseStart_2807264 baseEnd_2807264 := by
    simpa [prefixWord, tailWord_2807264, baseEnd_2807264] using wordTrace_append hprefix tailTrace_2807264
  have hstable : (prefixWord ++ tailWord_2807264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807264).length < 2 ^ (prefixWord ++ tailWord_2807264).sum := by decide
  have hdescent : baseEnd_2807264 < baseStart_2807264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807356 : List Nat := [2, 2, 2, 2, 4, 10]
def baseStart_2807356 : Nat := 118140960795 + 2807356 * 2 ^ 59
def prefixEnd_2807356 : Nat := 4983230072969 + 3 ^ 40 * 2807356 * 2
def baseEnd_2807356 : Nat := 11864386800688258769047

theorem tailTrace_2807356 : CollatzResearch.WordTrace tailWord_2807356 prefixEnd_2807356 11864386800688258769047 := by
  unfold tailWord_2807356
  simp only [CollatzResearch.WordTrace]
  refine ⟨51196342608718072539144961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68261790144957430052193281 51196342608718072539144961)
  ·
    refine ⟨38397256956538554404358721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51196342608718072539144961 38397256956538554404358721)
    ·
      refine ⟨28797942717403915803269041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38397256956538554404358721 28797942717403915803269041)
      ·
        refine ⟨21598457038052936852451781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28797942717403915803269041 21598457038052936852451781)
        ·
          refine ⟨4049710694634925659834709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21598457038052936852451781 4049710694634925659834709)
          ·
            refine ⟨11864386800688258769047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4049710694634925659834709 11864386800688258769047)
            ·
              rfl

theorem cell22_2807356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 10].length) (baseStart_2807356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807356 prefixEnd_2807356 := by exact prefixLift 2807356
  have htrace : WordTrace (prefixWord ++ tailWord_2807356) baseStart_2807356 baseEnd_2807356 := by
    simpa [prefixWord, tailWord_2807356, baseEnd_2807356] using wordTrace_append hprefix tailTrace_2807356
  have hstable : (prefixWord ++ tailWord_2807356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807356).length < 2 ^ (prefixWord ++ tailWord_2807356).sum := by decide
  have hdescent : baseEnd_2807356 < baseStart_2807356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807495 : List Nat := [1, 1, 4, 1, 1, 1, 5, 3, 2, 3]
def baseStart_2807495 : Nat := 118140960795 + 2807495 * 2 ^ 59
def prefixEnd_2807495 : Nat := 4983230072969 + 3 ^ 40 * 2807495 * 2
def baseEnd_2807495 : Nat := 961062913396398931067381

theorem tailTrace_2807495 : CollatzResearch.WordTrace tailWord_2807495 prefixEnd_2807495 961062913396398931067381 := by
  unfold tailWord_2807495
  simp only [CollatzResearch.WordTrace]
  refine ⟨102397754963932571817599939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68265169975955047878399959 102397754963932571817599939)
  ·
    refine ⟨153596632445898857726399909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102397754963932571817599939 153596632445898857726399909)
    ·
      refine ⟨28799368583606035823699983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153596632445898857726399909 28799368583606035823699983)
      ·
        refine ⟨43199052875409053735549975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28799368583606035823699983 43199052875409053735549975)
        ·
          refine ⟨64798579313113580603324963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43199052875409053735549975 64798579313113580603324963)
          ·
            refine ⟨97197868969670370904987445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64798579313113580603324963 97197868969670370904987445)
            ·
              refine ⟨9112300215906597272342573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97197868969670370904987445 9112300215906597272342573)
              ·
                refine ⟨3417112580964973977128465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9112300215906597272342573 3417112580964973977128465)
                ·
                  refine ⟨2562834435723730482846349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3417112580964973977128465 2562834435723730482846349)
                  ·
                    refine ⟨961062913396398931067381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2562834435723730482846349 961062913396398931067381)
                    ·
                      rfl

theorem cell22_2807495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_2807495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807495 prefixEnd_2807495 := by exact prefixLift 2807495
  have htrace : WordTrace (prefixWord ++ tailWord_2807495) baseStart_2807495 baseEnd_2807495 := by
    simpa [prefixWord, tailWord_2807495, baseEnd_2807495] using wordTrace_append hprefix tailTrace_2807495
  have hstable : (prefixWord ++ tailWord_2807495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807495).length < 2 ^ (prefixWord ++ tailWord_2807495).sum := by decide
  have hdescent : baseEnd_2807495 < baseStart_2807495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807538 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_2807538 : Nat := 118140960795 + 2807538 * 2 ^ 59
def prefixEnd_2807538 : Nat := 4983230072969 + 3 ^ 40 * 2807538 * 2
def baseEnd_2807538 : Nat := 961077633175161152242249

theorem tailTrace_2807538 : CollatzResearch.WordTrace tailWord_2807538 prefixEnd_2807538 961077633175161152242249 := by
  unfold tailWord_2807538
  simp only [CollatzResearch.WordTrace]
  refine ⟨25599830825694197540353817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68266215535184526774276845 25599830825694197540353817)
  ·
    refine ⟨19199873119270648155265363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25599830825694197540353817 19199873119270648155265363)
    ·
      refine ⟨28799809678905972232898045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19199873119270648155265363 28799809678905972232898045)
      ·
        refine ⟨10799928629589739587336767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28799809678905972232898045 10799928629589739587336767)
        ·
          refine ⟨16199892944384609381005151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10799928629589739587336767 16199892944384609381005151)
          ·
            refine ⟨24299839416576914071507727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16199892944384609381005151 24299839416576914071507727)
            ·
              refine ⟨36449759124865371107261591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24299839416576914071507727 36449759124865371107261591)
              ·
                refine ⟨54674638687298056660892387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36449759124865371107261591 54674638687298056660892387)
                ·
                  refine ⟨82011958030947084991338581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54674638687298056660892387 82011958030947084991338581)
                  ·
                    refine ⟨961077633175161152242249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82011958030947084991338581 961077633175161152242249)
                    ·
                      rfl

theorem cell22_2807538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_2807538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807538 prefixEnd_2807538 := by exact prefixLift 2807538
  have htrace : WordTrace (prefixWord ++ tailWord_2807538) baseStart_2807538 baseEnd_2807538 := by
    simpa [prefixWord, tailWord_2807538, baseEnd_2807538] using wordTrace_append hprefix tailTrace_2807538
  have hstable : (prefixWord ++ tailWord_2807538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807538).length < 2 ^ (prefixWord ++ tailWord_2807538).sum := by decide
  have hdescent : baseEnd_2807538 < baseStart_2807538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807604 : List Nat := [2, 5, 1, 1, 2, 2, 3, 1, 5]
def baseStart_2807604 : Nat := 118140960795 + 2807604 * 2 ^ 59
def prefixEnd_2807604 : Nat := 4983230072969 + 3 ^ 40 * 2807604 * 2
def baseEnd_2807604 : Nat := 320366742107986326697349

theorem tailTrace_2807604 : CollatzResearch.WordTrace tailWord_2807604 prefixEnd_2807604 320366742107986326697349 := by
  unfold tailWord_2807604
  simp only [CollatzResearch.WordTrace]
  refine ⟨51200865260268841716658933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68267820347025122288878577 51200865260268841716658933)
  ·
    refine ⟨4800081118150203910936775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51200865260268841716658933 4800081118150203910936775)
    ·
      refine ⟨7200121677225305866405163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4800081118150203910936775 7200121677225305866405163)
      ·
        refine ⟨10800182515837958799607745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7200121677225305866405163 10800182515837958799607745)
        ·
          refine ⟨8100136886878469099705809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10800182515837958799607745 8100136886878469099705809)
          ·
            refine ⟨6075102665158851824779357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8100136886878469099705809 6075102665158851824779357)
            ·
              refine ⟨2278163499434569434292259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6075102665158851824779357 2278163499434569434292259)
              ·
                refine ⟨3417245249151854151438389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278163499434569434292259 3417245249151854151438389)
                ·
                  refine ⟨320366742107986326697349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3417245249151854151438389 320366742107986326697349)
                  ·
                    rfl

theorem cell22_2807604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_2807604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807604 prefixEnd_2807604 := by exact prefixLift 2807604
  have htrace : WordTrace (prefixWord ++ tailWord_2807604) baseStart_2807604 baseEnd_2807604 := by
    simpa [prefixWord, tailWord_2807604, baseEnd_2807604] using wordTrace_append hprefix tailTrace_2807604
  have hstable : (prefixWord ++ tailWord_2807604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807604).length < 2 ^ (prefixWord ++ tailWord_2807604).sum := by decide
  have hdescent : baseEnd_2807604 < baseStart_2807604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807660 : List Nat := [2, 2, 1, 1, 4, 3, 2, 7]
def baseStart_2807660 : Nat := 118140960795 + 2807660 * 2 ^ 59
def prefixEnd_2807660 : Nat := 4983230072969 + 3 ^ 40 * 2807660 * 2
def baseEnd_2807660 : Nat := 106791044029821500076875

theorem tailTrace_2807660 : CollatzResearch.WordTrace tailWord_2807660 prefixEnd_2807660 106791044029821500076875 := by
  unfold tailWord_2807660
  simp only [CollatzResearch.WordTrace]
  refine ⟨51201886504167402498678217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68269182005556536664904289 51201886504167402498678217)
  ·
    refine ⟨38401414878125551874008663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51201886504167402498678217 38401414878125551874008663)
    ·
      refine ⟨57602122317188327811012995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38401414878125551874008663 57602122317188327811012995)
      ·
        refine ⟨86403183475782491716519493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57602122317188327811012995 86403183475782491716519493)
        ·
          refine ⟨16200596901709217196847405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86403183475782491716519493 16200596901709217196847405)
          ·
            refine ⟨6075223838140956448817777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16200596901709217196847405 6075223838140956448817777)
            ·
              refine ⟨4556417878605717336613333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6075223838140956448817777 4556417878605717336613333)
              ·
                refine ⟨106791044029821500076875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4556417878605717336613333 106791044029821500076875)
                ·
                  rfl

theorem cell22_2807660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 7].length) (baseStart_2807660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807660 prefixEnd_2807660 := by exact prefixLift 2807660
  have htrace : WordTrace (prefixWord ++ tailWord_2807660) baseStart_2807660 baseEnd_2807660 := by
    simpa [prefixWord, tailWord_2807660, baseEnd_2807660] using wordTrace_append hprefix tailTrace_2807660
  have hstable : (prefixWord ++ tailWord_2807660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807660).length < 2 ^ (prefixWord ++ tailWord_2807660).sum := by decide
  have hdescent : baseEnd_2807660 < baseStart_2807660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807675 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 5, 3]
def baseStart_2807675 : Nat := 118140960795 + 2807675 * 2 ^ 59
def prefixEnd_2807675 : Nat := 4983230072969 + 3 ^ 40 * 2807675 * 2
def baseEnd_2807675 : Nat := 961124531074938461566829

theorem tailTrace_2807675 : CollatzResearch.WordTrace tailWord_2807675 prefixEnd_2807675 961124531074938461566829 := by
  unfold tailWord_2807675
  simp only [CollatzResearch.WordTrace]
  refine ⟨102404320103280462559152479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68269546735520308372768319 102404320103280462559152479)
  ·
    refine ⟨153606480154920693838728719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102404320103280462559152479 153606480154920693838728719)
    ·
      refine ⟨230409720232381040758093079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153606480154920693838728719 230409720232381040758093079)
      ·
        refine ⟨345614580348571561137139619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230409720232381040758093079 345614580348571561137139619)
        ·
          refine ⟨518421870522857341705709429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345614580348571561137139619 518421870522857341705709429)
          ·
            refine ⟨48602050361517875784910259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 518421870522857341705709429 48602050361517875784910259)
            ·
              refine ⟨72903075542276813677365389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48602050361517875784910259 72903075542276813677365389)
              ·
                refine ⟨27338653328353805129012021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72903075542276813677365389 27338653328353805129012021)
                ·
                  refine ⟨2562998749533169230844877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27338653328353805129012021 2562998749533169230844877)
                  ·
                    refine ⟨961124531074938461566829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2562998749533169230844877 961124531074938461566829)
                    ·
                      rfl

theorem cell22_2807675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 3].length) (baseStart_2807675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807675 prefixEnd_2807675 := by exact prefixLift 2807675
  have htrace : WordTrace (prefixWord ++ tailWord_2807675) baseStart_2807675 baseEnd_2807675 := by
    simpa [prefixWord, tailWord_2807675, baseEnd_2807675] using wordTrace_append hprefix tailTrace_2807675
  have hstable : (prefixWord ++ tailWord_2807675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807675).length < 2 ^ (prefixWord ++ tailWord_2807675).sum := by decide
  have hdescent : baseEnd_2807675 < baseStart_2807675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807705 : List Nat := [1, 2, 1, 2, 1, 3, 3, 4, 5]
def baseStart_2807705 : Nat := 118140960795 + 2807705 * 2 ^ 59
def prefixEnd_2807705 : Nat := 4983230072969 + 3 ^ 40 * 2807705 * 2
def baseEnd_2807705 : Nat := 320378266896009461105579

theorem tailTrace_2807705 : CollatzResearch.WordTrace tailWord_2807705 prefixEnd_2807705 320378266896009461105579 := by
  unfold tailWord_2807705
  simp only [CollatzResearch.WordTrace]
  refine ⟨102405414293171777682744569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68270276195447851788496379 102405414293171777682744569)
  ·
    refine ⟨76804060719878833262058427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102405414293171777682744569 76804060719878833262058427)
    ·
      refine ⟨115206091079818249893087641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76804060719878833262058427 115206091079818249893087641)
      ·
        refine ⟨86404568309863687419815731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115206091079818249893087641 86404568309863687419815731)
        ·
          refine ⟨129606852464795531129723597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86404568309863687419815731 129606852464795531129723597)
          ·
            refine ⟨48602569674298324173646349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129606852464795531129723597 48602569674298324173646349)
            ·
              refine ⟨18225963627861871565117381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48602569674298324173646349 18225963627861871565117381)
              ·
                refine ⟨3417368180224100918459509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18225963627861871565117381 3417368180224100918459509)
                ·
                  refine ⟨320378266896009461105579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3417368180224100918459509 320378266896009461105579)
                  ·
                    rfl

theorem cell22_2807705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 5].length) (baseStart_2807705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807705 prefixEnd_2807705 := by exact prefixLift 2807705
  have htrace : WordTrace (prefixWord ++ tailWord_2807705) baseStart_2807705 baseEnd_2807705 := by
    simpa [prefixWord, tailWord_2807705, baseEnd_2807705] using wordTrace_append hprefix tailTrace_2807705
  have hstable : (prefixWord ++ tailWord_2807705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807705).length < 2 ^ (prefixWord ++ tailWord_2807705).sum := by decide
  have hdescent : baseEnd_2807705 < baseStart_2807705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807767 : List Nat := [1, 1, 3, 2, 1, 1, 3, 6, 4]
def baseStart_2807767 : Nat := 118140960795 + 2807767 * 2 ^ 59
def prefixEnd_2807767 : Nat := 4983230072969 + 3 ^ 40 * 2807767 * 2
def baseEnd_2807767 : Nat := 320385341518360296088849

theorem tailTrace_2807767 : CollatzResearch.WordTrace tailWord_2807767 prefixEnd_2807767 320385341518360296088849 := by
  unfold tailWord_2807767
  simp only [CollatzResearch.WordTrace]
  refine ⟨102407675618947162271501555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68271783745964774847667703 102407675618947162271501555)
  ·
    refine ⟨153611513428420743407252333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102407675618947162271501555 153611513428420743407252333)
    ·
      refine ⟨57604317535657778777719625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153611513428420743407252333 57604317535657778777719625)
      ·
        refine ⟨43203238151743334083289719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57604317535657778777719625 43203238151743334083289719)
        ·
          refine ⟨64804857227615001124934579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43203238151743334083289719 64804857227615001124934579)
          ·
            refine ⟨97207285841422501687401869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64804857227615001124934579 97207285841422501687401869)
            ·
              refine ⟨36452732190533438132775701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97207285841422501687401869 36452732190533438132775701)
              ·
                refine ⟨1708721821431254912473861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36452732190533438132775701 1708721821431254912473861)
                ·
                  refine ⟨320385341518360296088849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1708721821431254912473861 320385341518360296088849)
                  ·
                    rfl

theorem cell22_2807767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 4].length) (baseStart_2807767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807767 prefixEnd_2807767 := by exact prefixLift 2807767
  have htrace : WordTrace (prefixWord ++ tailWord_2807767) baseStart_2807767 baseEnd_2807767 := by
    simpa [prefixWord, tailWord_2807767, baseEnd_2807767] using wordTrace_append hprefix tailTrace_2807767
  have hstable : (prefixWord ++ tailWord_2807767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807767).length < 2 ^ (prefixWord ++ tailWord_2807767).sum := by decide
  have hdescent : baseEnd_2807767 < baseStart_2807767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807780 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_2807780 : Nat := 118140960795 + 2807780 * 2 ^ 59
def prefixEnd_2807780 : Nat := 4983230072969 + 3 ^ 40 * 2807780 * 2
def baseEnd_2807780 : Nat := 961160474720753187691507

theorem tailTrace_2807780 : CollatzResearch.WordTrace tailWord_2807780 prefixEnd_2807780 961160474720753187691507 := by
  unfold tailWord_2807780
  simp only [CollatzResearch.WordTrace]
  refine ⟨51204074883950032745862397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68272099845266710327816529 51204074883950032745862397)
  ·
    refine ⟨19201528081481262279698399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51204074883950032745862397 19201528081481262279698399)
    ·
      refine ⟨28802292122221893419547599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19201528081481262279698399 28802292122221893419547599)
      ·
        refine ⟨43203438183332840129321399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28802292122221893419547599 43203438183332840129321399)
        ·
          refine ⟨64805157274999260193982099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43203438183332840129321399 64805157274999260193982099)
          ·
            refine ⟨97207735912498890290973149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64805157274999260193982099 97207735912498890290973149)
            ·
              refine ⟨36452900967187083859114931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97207735912498890290973149 36452900967187083859114931)
              ·
                refine ⟨54679351450780625788672397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36452900967187083859114931 54679351450780625788672397)
                ·
                  refine ⟨20504756794042734670752149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54679351450780625788672397 20504756794042734670752149)
                  ·
                    refine ⟨961160474720753187691507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20504756794042734670752149 961160474720753187691507)
                    ·
                      rfl

theorem cell22_2807780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_2807780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807780 prefixEnd_2807780 := by exact prefixLift 2807780
  have htrace : WordTrace (prefixWord ++ tailWord_2807780) baseStart_2807780 baseEnd_2807780 := by
    simpa [prefixWord, tailWord_2807780, baseEnd_2807780] using wordTrace_append hprefix tailTrace_2807780
  have hstable : (prefixWord ++ tailWord_2807780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807780).length < 2 ^ (prefixWord ++ tailWord_2807780).sum := by decide
  have hdescent : baseEnd_2807780 < baseStart_2807780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807855 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 3, 7]
def baseStart_2807855 : Nat := 118140960795 + 2807855 * 2 ^ 59
def prefixEnd_2807855 : Nat := 4983230072969 + 3 ^ 40 * 2807855 * 2
def baseEnd_2807855 : Nat := 961186148753477992066277

theorem tailTrace_2807855 : CollatzResearch.WordTrace tailWord_2807855 prefixEnd_2807855 961186148753477992066277 := by
  unfold tailWord_2807855
  simp only [CollatzResearch.WordTrace]
  refine ⟨102410885242628353300705019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68273923495085568867136679 102410885242628353300705019)
  ·
    refine ⟨153616327863942529951057529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102410885242628353300705019 153616327863942529951057529)
    ·
      refine ⟨115212245897956897463293147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153616327863942529951057529 115212245897956897463293147)
      ·
        refine ⟨172818368846935346194939721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115212245897956897463293147 172818368846935346194939721)
        ·
          refine ⟨129613776635201509646204791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172818368846935346194939721 129613776635201509646204791)
          ·
            refine ⟨194420664952802264469307187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129613776635201509646204791 194420664952802264469307187)
            ·
              refine ⟨291630997429203396703960781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194420664952802264469307187 291630997429203396703960781)
              ·
                refine ⟨109361624035951273763985293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291630997429203396703960781 109361624035951273763985293)
                ·
                  refine ⟨41010609013481727661494485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109361624035951273763985293 41010609013481727661494485)
                  ·
                    refine ⟨961186148753477992066277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41010609013481727661494485 961186148753477992066277)
                    ·
                      rfl

theorem cell22_2807855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_2807855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807855 prefixEnd_2807855 := by exact prefixLift 2807855
  have htrace : WordTrace (prefixWord ++ tailWord_2807855) baseStart_2807855 baseEnd_2807855 := by
    simpa [prefixWord, tailWord_2807855, baseEnd_2807855] using wordTrace_append hprefix tailTrace_2807855
  have hstable : (prefixWord ++ tailWord_2807855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807855).length < 2 ^ (prefixWord ++ tailWord_2807855).sum := by decide
  have hdescent : baseEnd_2807855 < baseStart_2807855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807919 : List Nat := [1, 1, 2, 1, 3, 4, 1, 5, 4]
def baseStart_2807919 : Nat := 118140960795 + 2807919 * 2 ^ 59
def prefixEnd_2807919 : Nat := 4983230072969 + 3 ^ 40 * 2807919 * 2
def baseEnd_2807919 : Nat := 320402685753801052822027

theorem tailTrace_2807919 : CollatzResearch.WordTrace tailWord_2807919 prefixEnd_2807919 320402685753801052822027 := by
  unfold tailWord_2807919
  simp only [CollatzResearch.WordTrace]
  refine ⟨102413219514396492231034811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68275479676264328154023207 102413219514396492231034811)
  ·
    refine ⟨153619829271594738346552217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102413219514396492231034811 153619829271594738346552217)
    ·
      refine ⟨115214871953696053759914163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153619829271594738346552217 115214871953696053759914163)
      ·
        refine ⟨172822307930544080639871245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115214871953696053759914163 172822307930544080639871245)
        ·
          refine ⟨64808365473954030239951717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172822307930544080639871245 64808365473954030239951717)
          ·
            refine ⟨12151568526366380669990947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64808365473954030239951717 12151568526366380669990947)
            ·
              refine ⟨18227352789549571004986421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12151568526366380669990947 18227352789549571004986421)
              ·
                refine ⟨1708814324020272281717477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18227352789549571004986421 1708814324020272281717477)
                ·
                  refine ⟨320402685753801052822027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1708814324020272281717477 320402685753801052822027)
                  ·
                    rfl

theorem cell22_2807919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 4].length) (baseStart_2807919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807919 prefixEnd_2807919 := by exact prefixLift 2807919
  have htrace : WordTrace (prefixWord ++ tailWord_2807919) baseStart_2807919 baseEnd_2807919 := by
    simpa [prefixWord, tailWord_2807919, baseEnd_2807919] using wordTrace_append hprefix tailTrace_2807919
  have hstable : (prefixWord ++ tailWord_2807919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807919).length < 2 ^ (prefixWord ++ tailWord_2807919).sum := by decide
  have hdescent : baseEnd_2807919 < baseStart_2807919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807992 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 7]
def baseStart_2807992 : Nat := 118140960795 + 2807992 * 2 ^ 59
def prefixEnd_2807992 : Nat := 4983230072969 + 3 ^ 40 * 2807992 * 2
def baseEnd_2807992 : Nat := 320411015551085100463619

theorem tailTrace_2807992 : CollatzResearch.WordTrace tailWord_2807992 prefixEnd_2807992 320411015551085100463619 := by
  unfold tailWord_2807992
  simp only [CollatzResearch.WordTrace]
  refine ⟨51207941021566012849221115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68277254695421350465628153 51207941021566012849221115)
  ·
    refine ⟨76811911532349019273831673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51207941021566012849221115 76811911532349019273831673)
    ·
      refine ⟨57608933649261764455373755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76811911532349019273831673 57608933649261764455373755)
      ·
        refine ⟨86413400473892646683060633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57608933649261764455373755 86413400473892646683060633)
        ·
          refine ⟨64810050355419485012295475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86413400473892646683060633 64810050355419485012295475)
          ·
            refine ⟨97215075533129227518443213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64810050355419485012295475 97215075533129227518443213)
            ·
              refine ⟨36455653324923460319416205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97215075533129227518443213 36455653324923460319416205)
              ·
                refine ⟨13670869996846297619781077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36455653324923460319416205 13670869996846297619781077)
                ·
                  refine ⟨320411015551085100463619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13670869996846297619781077 320411015551085100463619)
                  ·
                    rfl

theorem cell22_2807992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 7].length) (baseStart_2807992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2807992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2807992 prefixEnd_2807992 := by exact prefixLift 2807992
  have htrace : WordTrace (prefixWord ++ tailWord_2807992) baseStart_2807992 baseEnd_2807992 := by
    simpa [prefixWord, tailWord_2807992, baseEnd_2807992] using wordTrace_append hprefix tailTrace_2807992
  have hstable : (prefixWord ++ tailWord_2807992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807992).length < 2 ^ (prefixWord ++ tailWord_2807992).sum := by decide
  have hdescent : baseEnd_2807992 < baseStart_2807992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808002 : List Nat := [3, 5, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_2808002 : Nat := 118140960795 + 2808002 * 2 ^ 59
def prefixEnd_2808002 : Nat := 4983230072969 + 3 ^ 40 * 2808002 * 2
def baseEnd_2808002 : Nat := 961236469857618608640827

theorem tailTrace_2808002 : CollatzResearch.WordTrace tailWord_2808002 prefixEnd_2808002 961236469857618608640827 := by
  unfold tailWord_2808002
  simp only [CollatzResearch.WordTrace]
  refine ⟨25604061693273949351576565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68277497848730531604204173 25604061693273949351576565)
  ·
    refine ⟨2400380783744432751710303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25604061693273949351576565 2400380783744432751710303)
    ·
      refine ⟨3600571175616649127565455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2400380783744432751710303 3600571175616649127565455)
      ·
        refine ⟨5400856763424973691348183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3600571175616649127565455 5400856763424973691348183)
        ·
          refine ⟨8101285145137460537022275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5400856763424973691348183 8101285145137460537022275)
          ·
            refine ⟨12151927717706190805533413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8101285145137460537022275 12151927717706190805533413)
            ·
              refine ⟨2278486447069910776037515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12151927717706190805533413 2278486447069910776037515)
              ·
                refine ⟨3417729670604866164056273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278486447069910776037515 3417729670604866164056273)
                ·
                  refine ⟨2563297252953649623042205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3417729670604866164056273 2563297252953649623042205)
                  ·
                    refine ⟨961236469857618608640827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2563297252953649623042205 961236469857618608640827)
                    ·
                      rfl

theorem cell22_2808002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_2808002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808002 prefixEnd_2808002 := by exact prefixLift 2808002
  have htrace : WordTrace (prefixWord ++ tailWord_2808002) baseStart_2808002 baseEnd_2808002 := by
    simpa [prefixWord, tailWord_2808002, baseEnd_2808002] using wordTrace_append hprefix tailTrace_2808002
  have hstable : (prefixWord ++ tailWord_2808002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808002).length < 2 ^ (prefixWord ++ tailWord_2808002).sum := by decide
  have hdescent : baseEnd_2808002 < baseStart_2808002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808090 : List Nat := [3, 1, 1, 3, 4, 2, 2, 1, 1, 4]
def baseStart_2808090 : Nat := 118140960795 + 2808090 * 2 ^ 59
def prefixEnd_2808090 : Nat := 4983230072969 + 3 ^ 40 * 2808090 * 2
def baseEnd_2808090 : Nat := 961266594056015712440557

theorem tailTrace_2808090 : CollatzResearch.WordTrace tailWord_2808090 prefixEnd_2808090 961266594056015712440557 := by
  unfold tailWord_2808090
  simp only [CollatzResearch.WordTrace]
  refine ⟨25604864099194247108877431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68279637597851325623673149 25604864099194247108877431)
  ·
    refine ⟨38407296148791370663316147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25604864099194247108877431 38407296148791370663316147)
    ·
      refine ⟨57610944223187055994974221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38407296148791370663316147 57610944223187055994974221)
      ·
        refine ⟨21604104083695145998115333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57610944223187055994974221 21604104083695145998115333)
        ·
          refine ⟨4050769515692839874646625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21604104083695145998115333 4050769515692839874646625)
          ·
            refine ⟨3038077136769629905984969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4050769515692839874646625 3038077136769629905984969)
            ·
              refine ⟨2278557852577222429488727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3038077136769629905984969 2278557852577222429488727)
              ·
                refine ⟨3417836778865833644233091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278557852577222429488727 3417836778865833644233091)
                ·
                  refine ⟨5126755168298750466349637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3417836778865833644233091 5126755168298750466349637)
                  ·
                    refine ⟨961266594056015712440557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5126755168298750466349637 961266594056015712440557)
                    ·
                      rfl

theorem cell22_2808090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_2808090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808090 prefixEnd_2808090 := by exact prefixLift 2808090
  have htrace : WordTrace (prefixWord ++ tailWord_2808090) baseStart_2808090 baseEnd_2808090 := by
    simpa [prefixWord, tailWord_2808090, baseEnd_2808090] using wordTrace_append hprefix tailTrace_2808090
  have hstable : (prefixWord ++ tailWord_2808090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808090).length < 2 ^ (prefixWord ++ tailWord_2808090).sum := by decide
  have hdescent : baseEnd_2808090 < baseStart_2808090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808131 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 3, 3]
def baseStart_2808131 : Nat := 118140960795 + 2808131 * 2 ^ 59
def prefixEnd_2808131 : Nat := 4983230072969 + 3 ^ 40 * 2808131 * 2
def baseEnd_2808131 : Nat := 961280629193905272165431

theorem tailTrace_2808131 : CollatzResearch.WordTrace tailWord_2808131 prefixEnd_2808131 961280629193905272165431 := by
  unfold tailWord_2808131
  simp only [CollatzResearch.WordTrace]
  refine ⟨102420951789628452437752247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68280634526418968291834831 102420951789628452437752247)
  ·
    refine ⟨153631427684442678656628371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102420951789628452437752247 153631427684442678656628371)
    ·
      refine ⟨230447141526664017984942557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153631427684442678656628371 230447141526664017984942557)
      ·
        refine ⟨86417678072499006744353459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230447141526664017984942557 86417678072499006744353459)
        ·
          refine ⟨129626517108748510116530189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86417678072499006744353459 129626517108748510116530189)
          ·
            refine ⟨48609943915780691293698821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129626517108748510116530189 48609943915780691293698821)
            ·
              refine ⟨9114364484208879617568529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48609943915780691293698821 9114364484208879617568529)
              ·
                refine ⟨6835773363156659713176397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9114364484208879617568529 6835773363156659713176397)
                ·
                  refine ⟨2563415011183747392441149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6835773363156659713176397 2563415011183747392441149)
                  ·
                    refine ⟨961280629193905272165431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2563415011183747392441149 961280629193905272165431)
                    ·
                      rfl

theorem cell22_2808131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 3].length) (baseStart_2808131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808131 prefixEnd_2808131 := by exact prefixLift 2808131
  have htrace : WordTrace (prefixWord ++ tailWord_2808131) baseStart_2808131 baseEnd_2808131 := by
    simpa [prefixWord, tailWord_2808131, baseEnd_2808131] using wordTrace_append hprefix tailTrace_2808131
  have hstable : (prefixWord ++ tailWord_2808131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808131).length < 2 ^ (prefixWord ++ tailWord_2808131).sum := by decide
  have hdescent : baseEnd_2808131 < baseStart_2808131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808144 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 7]
def baseStart_2808144 : Nat := 118140960795 + 2808144 * 2 ^ 59
def prefixEnd_2808144 : Nat := 4983230072969 + 3 ^ 40 * 2808144 * 2
def baseEnd_2808144 : Nat := 320428359786525857196797

theorem tailTrace_2808144 : CollatzResearch.WordTrace tailWord_2808144 prefixEnd_2808144 320428359786525857196797 := by
  unfold tailWord_2808144
  simp only [CollatzResearch.WordTrace]
  refine ⟨51210712969290677828987743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68280950625720903771983657 51210712969290677828987743)
  ·
    refine ⟨76816069453936016743481615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51210712969290677828987743 76816069453936016743481615)
    ·
      refine ⟨115224104180904025115222423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76816069453936016743481615 115224104180904025115222423)
      ·
        refine ⟨172836156271356037672833635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115224104180904025115222423 172836156271356037672833635)
        ·
          refine ⟨259254234407034056509250453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172836156271356037672833635 259254234407034056509250453)
          ·
            refine ⟨12152542237829721398871115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 259254234407034056509250453 12152542237829721398871115)
            ·
              refine ⟨18228813356744582098306673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12152542237829721398871115 18228813356744582098306673)
              ·
                refine ⟨13671610017558436573730005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18228813356744582098306673 13671610017558436573730005)
                ·
                  refine ⟨320428359786525857196797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13671610017558436573730005 320428359786525857196797)
                  ·
                    rfl

theorem cell22_2808144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 7].length) (baseStart_2808144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808144 prefixEnd_2808144 := by exact prefixLift 2808144
  have htrace : WordTrace (prefixWord ++ tailWord_2808144) baseStart_2808144 baseEnd_2808144 := by
    simpa [prefixWord, tailWord_2808144, baseEnd_2808144] using wordTrace_append hprefix tailTrace_2808144
  have hstable : (prefixWord ++ tailWord_2808144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808144).length < 2 ^ (prefixWord ++ tailWord_2808144).sum := by decide
  have hdescent : baseEnd_2808144 < baseStart_2808144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808159 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 4, 5]
def baseStart_2808159 : Nat := 118140960795 + 2808159 * 2 ^ 59
def prefixEnd_2808159 : Nat := 4983230072969 + 3 ^ 40 * 2808159 * 2
def baseEnd_2808159 : Nat := 961290214166122532465345

theorem tailTrace_2808159 : CollatzResearch.WordTrace tailWord_2808159 prefixEnd_2808159 961290214166122532465345 := by
  unfold tailWord_2808159
  simp only [CollatzResearch.WordTrace]
  refine ⟨102421973033527013219771531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68281315355684675479847687 102421973033527013219771531)
  ·
    refine ⟨153632959550290519829657297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102421973033527013219771531 153632959550290519829657297)
    ·
      refine ⟨115224719662717889872242973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153632959550290519829657297 115224719662717889872242973)
      ·
        refine ⟨43209269873519208702091115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115224719662717889872242973 43209269873519208702091115)
        ·
          refine ⟨64813904810278813053136673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43209269873519208702091115 64813904810278813053136673)
          ·
            refine ⟨48610428607709109789852505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64813904810278813053136673 48610428607709109789852505)
            ·
              refine ⟨36457821455781832342389379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48610428607709109789852505 36457821455781832342389379)
              ·
                refine ⟨54686732183672748513584069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36457821455781832342389379 54686732183672748513584069)
                ·
                  refine ⟨10253762284438640346297013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54686732183672748513584069 10253762284438640346297013)
                  ·
                    refine ⟨961290214166122532465345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10253762284438640346297013 961290214166122532465345)
                    ·
                      rfl

theorem cell22_2808159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_2808159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808159 prefixEnd_2808159 := by exact prefixLift 2808159
  have htrace : WordTrace (prefixWord ++ tailWord_2808159) baseStart_2808159 baseEnd_2808159 := by
    simpa [prefixWord, tailWord_2808159, baseEnd_2808159] using wordTrace_append hprefix tailTrace_2808159
  have hstable : (prefixWord ++ tailWord_2808159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808159).length < 2 ^ (prefixWord ++ tailWord_2808159).sum := by decide
  have hdescent : baseEnd_2808159 < baseStart_2808159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808178 : List Nat := [3, 2, 1, 2, 1, 3, 4, 1, 5]
def baseStart_2808178 : Nat := 118140960795 + 2808178 * 2 ^ 59
def prefixEnd_2808178 : Nat := 4983230072969 + 3 ^ 40 * 2808178 * 2
def baseEnd_2808178 : Nat := 320432239418137605413429

theorem tailTrace_2808178 : CollatzResearch.WordTrace tailWord_2808178 prefixEnd_2808178 320432239418137605413429 := by
  unfold tailWord_2808178
  simp only [CollatzResearch.WordTrace]
  refine ⟨25605666505114544866178297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68281777346972119643142125 25605666505114544866178297)
  ·
    refine ⟨19204249878835908649633723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25605666505114544866178297 19204249878835908649633723)
    ·
      refine ⟨28806374818253862974450585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19204249878835908649633723 28806374818253862974450585)
      ·
        refine ⟨21604781113690397230837939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28806374818253862974450585 21604781113690397230837939)
        ·
          refine ⟨32407171670535595846256909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21604781113690397230837939 32407171670535595846256909)
          ·
            refine ⟨12152689376450848442346341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32407171670535595846256909 12152689376450848442346341)
            ·
              refine ⟨2278629258084534082939939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12152689376450848442346341 2278629258084534082939939)
              ·
                refine ⟨3417943887126801124409909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278629258084534082939939 3417943887126801124409909)
                ·
                  refine ⟨320432239418137605413429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3417943887126801124409909 320432239418137605413429)
                  ·
                    rfl

theorem cell22_2808178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_2808178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808178 prefixEnd_2808178 := by exact prefixLift 2808178
  have htrace : WordTrace (prefixWord ++ tailWord_2808178) baseStart_2808178 baseEnd_2808178 := by
    simpa [prefixWord, tailWord_2808178, baseEnd_2808178] using wordTrace_append hprefix tailTrace_2808178
  have hstable : (prefixWord ++ tailWord_2808178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808178).length < 2 ^ (prefixWord ++ tailWord_2808178).sum := by decide
  have hdescent : baseEnd_2808178 < baseStart_2808178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808223 : List Nat := [1, 1, 2, 5, 1, 1, 3, 4, 4]
def baseStart_2808223 : Nat := 118140960795 + 2808223 * 2 ^ 59
def prefixEnd_2808223 : Nat := 4983230072969 + 3 ^ 40 * 2808223 * 2
def baseEnd_2808223 : Nat := 320437374224682566288383

theorem tailTrace_2808223 : CollatzResearch.WordTrace tailWord_2808223 prefixEnd_2808223 320437374224682566288383 := by
  unfold tailWord_2808223
  simp only [CollatzResearch.WordTrace]
  refine ⟨102424307305295152150101323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68282871536863434766734215 102424307305295152150101323)
  ·
    refine ⟨153636460957942728225151985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102424307305295152150101323 153636460957942728225151985)
    ·
      refine ⟨115227345718457046168863989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153636460957942728225151985 115227345718457046168863989)
      ·
        refine ⟨10802563661105348078330999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115227345718457046168863989 10802563661105348078330999)
        ·
          refine ⟨16203845491658022117496499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10802563661105348078330999 16203845491658022117496499)
          ·
            refine ⟨24305768237487033176244749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16203845491658022117496499 24305768237487033176244749)
            ·
              refine ⟨9114663089057637441091781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24305768237487033176244749 9114663089057637441091781)
              ·
                refine ⟨1708999329198307020204709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9114663089057637441091781 1708999329198307020204709)
                ·
                  refine ⟨320437374224682566288383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1708999329198307020204709 320437374224682566288383)
                  ·
                    rfl

theorem cell22_2808223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 4].length) (baseStart_2808223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808223 prefixEnd_2808223 := by exact prefixLift 2808223
  have htrace : WordTrace (prefixWord ++ tailWord_2808223) baseStart_2808223 baseEnd_2808223 := by
    simpa [prefixWord, tailWord_2808223, baseEnd_2808223] using wordTrace_append hprefix tailTrace_2808223
  have hstable : (prefixWord ++ tailWord_2808223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808223).length < 2 ^ (prefixWord ++ tailWord_2808223).sum := by decide
  have hdescent : baseEnd_2808223 < baseStart_2808223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808253 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_2808253 : Nat := 118140960795 + 2808253 * 2 ^ 59
def prefixEnd_2808253 : Nat := 4983230072969 + 3 ^ 40 * 2808253 * 2
def baseEnd_2808253 : Nat := 961322392287137620615057

theorem tailTrace_2808253 : CollatzResearch.WordTrace tailWord_2808253 prefixEnd_2808253 961322392287137620615057 := by
  unfold tailWord_2808253
  simp only [CollatzResearch.WordTrace]
  refine ⟨102425401495186467273693413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68283600996790978182462275 102425401495186467273693413)
  ·
    refine ⟨19204762780347462613817515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102425401495186467273693413 19204762780347462613817515)
    ·
      refine ⟨28807144170521193920726273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19204762780347462613817515 28807144170521193920726273)
      ·
        refine ⟨21605358127890895440544705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28807144170521193920726273 21605358127890895440544705)
        ·
          refine ⟨16204018595918171580408529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21605358127890895440544705 16204018595918171580408529)
          ·
            refine ⟨12153013946938628685306397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16204018595918171580408529 12153013946938628685306397)
            ·
              refine ⟨4557380230101985756989899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12153013946938628685306397 4557380230101985756989899)
              ·
                refine ⟨6836070345152978635484849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4557380230101985756989899 6836070345152978635484849)
                ·
                  refine ⟨5127052758864733976613637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6836070345152978635484849 5127052758864733976613637)
                  ·
                    refine ⟨961322392287137620615057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5127052758864733976613637 961322392287137620615057)
                    ·
                      rfl

theorem cell22_2808253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_2808253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808253 prefixEnd_2808253 := by exact prefixLift 2808253
  have htrace : WordTrace (prefixWord ++ tailWord_2808253) baseStart_2808253 baseEnd_2808253 := by
    simpa [prefixWord, tailWord_2808253, baseEnd_2808253] using wordTrace_append hprefix tailTrace_2808253
  have hstable : (prefixWord ++ tailWord_2808253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808253).length < 2 ^ (prefixWord ++ tailWord_2808253).sum := by decide
  have hdescent : baseEnd_2808253 < baseStart_2808253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808334 : List Nat := [4, 1, 1, 2, 3, 2, 3, 2, 1, 3]
def baseStart_2808334 : Nat := 118140960795 + 2808334 * 2 ^ 59
def prefixEnd_2808334 : Nat := 4983230072969 + 3 ^ 40 * 2808334 * 2
def baseEnd_2808334 : Nat := 961350120242480409339809

theorem tailTrace_2808334 : CollatzResearch.WordTrace tailWord_2808334 prefixEnd_2808334 961350120242480409339809 := by
  unfold tailWord_2808334
  simp only [CollatzResearch.WordTrace]
  refine ⟨12803544475986627263424007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68285570538595345404928037 12803544475986627263424007)
  ·
    refine ⟨19205316713979940895136011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12803544475986627263424007 19205316713979940895136011)
    ·
      refine ⟨28807975070969911342704017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19205316713979940895136011 28807975070969911342704017)
      ·
        refine ⟨21605981303227433507028013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28807975070969911342704017 21605981303227433507028013)
        ·
          refine ⟨8102242988710287565135505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21605981303227433507028013 8102242988710287565135505)
          ·
            refine ⟨6076682241532715673851629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8102242988710287565135505 6076682241532715673851629)
            ·
              refine ⟨2278755840574768377694361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6076682241532715673851629 2278755840574768377694361)
              ·
                refine ⟨1709066880431076283270771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2278755840574768377694361 1709066880431076283270771)
                ·
                  refine ⟨2563600320646614424906157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1709066880431076283270771 2563600320646614424906157)
                  ·
                    refine ⟨961350120242480409339809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2563600320646614424906157 961350120242480409339809)
                    ·
                      rfl

theorem cell22_2808334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_2808334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808334 prefixEnd_2808334 := by exact prefixLift 2808334
  have htrace : WordTrace (prefixWord ++ tailWord_2808334) baseStart_2808334 baseEnd_2808334 := by
    simpa [prefixWord, tailWord_2808334, baseEnd_2808334] using wordTrace_append hprefix tailTrace_2808334
  have hstable : (prefixWord ++ tailWord_2808334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808334).length < 2 ^ (prefixWord ++ tailWord_2808334).sum := by decide
  have hdescent : baseEnd_2808334 < baseStart_2808334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808360 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 3, 4]
def baseStart_2808360 : Nat := 118140960795 + 2808360 * 2 ^ 59
def prefixEnd_2808360 : Nat := 4983230072969 + 3 ^ 40 * 2808360 * 2
def baseEnd_2808360 : Nat := 961359020573825008189729

theorem tailTrace_2808360 : CollatzResearch.WordTrace tailWord_2808360 prefixEnd_2808360 961359020573825008189729 := by
  unfold tailWord_2808360
  simp only [CollatzResearch.WordTrace]
  refine ⟨51214652052899412273919267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68286202737199216365225689 51214652052899412273919267)
  ·
    refine ⟨76821978079349118410878901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51214652052899412273919267 76821978079349118410878901)
    ·
      refine ⟨7202060444938979851019897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76821978079349118410878901 7202060444938979851019897)
      ·
        refine ⟨5401545333704234888264923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7202060444938979851019897 5401545333704234888264923)
        ·
          refine ⟨8102318000556352332397385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5401545333704234888264923 8102318000556352332397385)
          ·
            refine ⟨6076738500417264249298039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8102318000556352332397385 6076738500417264249298039)
            ·
              refine ⟨9115107750625896373947059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6076738500417264249298039 9115107750625896373947059)
              ·
                refine ⟨13672661625938844560920589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9115107750625896373947059 13672661625938844560920589)
                ·
                  refine ⟨5127248109727066710345221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13672661625938844560920589 5127248109727066710345221)
                  ·
                    refine ⟨961359020573825008189729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5127248109727066710345221 961359020573825008189729)
                    ·
                      rfl

theorem cell22_2808360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_2808360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808360 prefixEnd_2808360 := by exact prefixLift 2808360
  have htrace : WordTrace (prefixWord ++ tailWord_2808360) baseStart_2808360 baseEnd_2808360 := by
    simpa [prefixWord, tailWord_2808360, baseEnd_2808360] using wordTrace_append hprefix tailTrace_2808360
  have hstable : (prefixWord ++ tailWord_2808360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808360).length < 2 ^ (prefixWord ++ tailWord_2808360).sum := by decide
  have hdescent : baseEnd_2808360 < baseStart_2808360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808373 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2808373 : Nat := 118140960795 + 2808373 * 2 ^ 59
def prefixEnd_2808373 : Nat := 4983230072969 + 3 ^ 40 * 2808373 * 2
def baseEnd_2808373 : Nat := 961363470739497307614689

theorem tailTrace_2808373 : CollatzResearch.WordTrace tailWord_2808373 prefixEnd_2808373 961363470739497307614689 := by
  unfold tailWord_2808373
  simp only [CollatzResearch.WordTrace]
  refine ⟨102429778254751727768061773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68286518836501151845374515 102429778254751727768061773)
  ·
    refine ⟨38411166845531897913023165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102429778254751727768061773 38411166845531897913023165)
    ·
      refine ⟨14404187567074461717383687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38411166845531897913023165 14404187567074461717383687)
      ·
        refine ⟨21606281350611692576075531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14404187567074461717383687 21606281350611692576075531)
        ·
          refine ⟨32409422025917538864113297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21606281350611692576075531 32409422025917538864113297)
          ·
            refine ⟨24307066519438154148084973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32409422025917538864113297 24307066519438154148084973)
            ·
              refine ⟨9115149944789307805531865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24307066519438154148084973 9115149944789307805531865)
              ·
                refine ⟨6836362458591980854148899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9115149944789307805531865 6836362458591980854148899)
                ·
                  refine ⟨10254543687887971281223349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6836362458591980854148899 10254543687887971281223349)
                  ·
                    refine ⟨961363470739497307614689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10254543687887971281223349 961363470739497307614689)
                    ·
                      rfl

theorem cell22_2808373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2808373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808373 prefixEnd_2808373 := by exact prefixLift 2808373
  have htrace : WordTrace (prefixWord ++ tailWord_2808373) baseStart_2808373 baseEnd_2808373 := by
    simpa [prefixWord, tailWord_2808373, baseEnd_2808373] using wordTrace_append hprefix tailTrace_2808373
  have hstable : (prefixWord ++ tailWord_2808373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808373).length < 2 ^ (prefixWord ++ tailWord_2808373).sum := by decide
  have hdescent : baseEnd_2808373 < baseStart_2808373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808448 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 7]
def baseStart_2808448 : Nat := 118140960795 + 2808448 * 2 ^ 59
def prefixEnd_2808448 : Nat := 4983230072969 + 3 ^ 40 * 2808448 * 2
def baseEnd_2808448 : Nat := 320463048257407370663153

theorem tailTrace_2808448 : CollatzResearch.WordTrace tailWord_2808448 prefixEnd_2808448 320463048257407370663153 := by
  unfold tailWord_2808448
  simp only [CollatzResearch.WordTrace]
  refine ⟨51216256864740007788520999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68288342486320010384694665 51216256864740007788520999)
  ·
    refine ⟨76824385297110011682781499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51216256864740007788520999 76824385297110011682781499)
    ·
      refine ⟨115236577945665017524172249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76824385297110011682781499 115236577945665017524172249)
      ·
        refine ⟨86427433459248763143129187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115236577945665017524172249 86427433459248763143129187)
        ·
          refine ⟨129641150188873144714693781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86427433459248763143129187 129641150188873144714693781)
          ·
            refine ⟨6076928915103428658501271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129641150188873144714693781 6076928915103428658501271)
            ·
              refine ⟨9115393372655142987751907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6076928915103428658501271 9115393372655142987751907)
              ·
                refine ⟨13673090058982714481627861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9115393372655142987751907 13673090058982714481627861)
                ·
                  refine ⟨320463048257407370663153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13673090058982714481627861 320463048257407370663153)
                  ·
                    rfl

theorem cell22_2808448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 7].length) (baseStart_2808448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808448 prefixEnd_2808448 := by exact prefixLift 2808448
  have htrace : WordTrace (prefixWord ++ tailWord_2808448) baseStart_2808448 baseEnd_2808448 := by
    simpa [prefixWord, tailWord_2808448, baseEnd_2808448] using wordTrace_append hprefix tailTrace_2808448
  have hstable : (prefixWord ++ tailWord_2808448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808448).length < 2 ^ (prefixWord ++ tailWord_2808448).sum := by decide
  have hdescent : baseEnd_2808448 < baseStart_2808448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808452 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 3, 3]
def baseStart_2808452 : Nat := 118140960795 + 2808452 * 2 ^ 59
def prefixEnd_2808452 : Nat := 4983230072969 + 3 ^ 40 * 2808452 * 2
def baseEnd_2808452 : Nat := 961390514053967434889447

theorem tailTrace_2808452 : CollatzResearch.WordTrace tailWord_2808452 prefixEnd_2808452 961390514053967434889447 := by
  unfold tailWord_2808452
  simp only [CollatzResearch.WordTrace]
  refine ⟨51216329810732762130093805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68288439747643682840125073 51216329810732762130093805)
  ·
    refine ⟨19206123679024785798785177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51216329810732762130093805 19206123679024785798785177)
    ·
      refine ⟨14404592759268589349088883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19206123679024785798785177 14404592759268589349088883)
      ·
        refine ⟨21606889138902884023633325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14404592759268589349088883 21606889138902884023633325)
        ·
          refine ⟨8102583427088581508862497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21606889138902884023633325 8102583427088581508862497)
          ·
            refine ⟨6076937570316436131646873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8102583427088581508862497 6076937570316436131646873)
            ·
              refine ⟨4557703177737327098735155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6076937570316436131646873 4557703177737327098735155)
              ·
                refine ⟨6836554766605990648102733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4557703177737327098735155 6836554766605990648102733)
                ·
                  refine ⟨2563708037477246493038525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6836554766605990648102733 2563708037477246493038525)
                  ·
                    refine ⟨961390514053967434889447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2563708037477246493038525 961390514053967434889447)
                    ·
                      rfl

theorem cell22_2808452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_2808452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808452 prefixEnd_2808452 := by exact prefixLift 2808452
  have htrace : WordTrace (prefixWord ++ tailWord_2808452) baseStart_2808452 baseEnd_2808452 := by
    simpa [prefixWord, tailWord_2808452, baseEnd_2808452] using wordTrace_append hprefix tailTrace_2808452
  have hstable : (prefixWord ++ tailWord_2808452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808452).length < 2 ^ (prefixWord ++ tailWord_2808452).sum := by decide
  have hdescent : baseEnd_2808452 < baseStart_2808452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808495 : List Nat := [1, 1, 2, 1, 2, 5, 2, 3, 1, 4]
def baseStart_2808495 : Nat := 118140960795 + 2808495 * 2 ^ 59
def prefixEnd_2808495 : Nat := 4983230072969 + 3 ^ 40 * 2808495 * 2
def baseEnd_2808495 : Nat := 961405233832729656064315

theorem tailTrace_2808495 : CollatzResearch.WordTrace tailWord_2808495 prefixEnd_2808495 961405233832729656064315 := by
  unfold tailWord_2808495
  simp only [CollatzResearch.WordTrace]
  refine ⟨102434227960309742604002939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68289485306873161736001959 102434227960309742604002939)
  ·
    refine ⟨153651341940464613906004409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102434227960309742604002939 153651341940464613906004409)
    ·
      refine ⟨115238506455348460429503307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153651341940464613906004409 115238506455348460429503307)
      ·
        refine ⟨172857759683022690644254961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115238506455348460429503307 172857759683022690644254961)
        ·
          refine ⟨129643319762267017983191221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172857759683022690644254961 129643319762267017983191221)
          ·
            refine ⟨12154061227712532935924177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129643319762267017983191221 12154061227712532935924177)
            ·
              refine ⟨9115545920784399701943133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12154061227712532935924177 9115545920784399701943133)
              ·
                refine ⟨3418329720294149888228675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9115545920784399701943133 3418329720294149888228675)
                ·
                  refine ⟨5127494580441224832343013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3418329720294149888228675 5127494580441224832343013)
                  ·
                    refine ⟨961405233832729656064315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5127494580441224832343013 961405233832729656064315)
                    ·
                      rfl

theorem cell22_2808495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 4].length) (baseStart_2808495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808495 prefixEnd_2808495 := by exact prefixLift 2808495
  have htrace : WordTrace (prefixWord ++ tailWord_2808495) baseStart_2808495 baseEnd_2808495 := by
    simpa [prefixWord, tailWord_2808495, baseEnd_2808495] using wordTrace_append hprefix tailTrace_2808495
  have hstable : (prefixWord ++ tailWord_2808495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808495).length < 2 ^ (prefixWord ++ tailWord_2808495).sum := by decide
  have hdescent : baseEnd_2808495 < baseStart_2808495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808538 : List Nat := [3, 1, 1, 2, 2, 2, 1, 10]
def baseStart_2808538 : Nat := 118140960795 + 2808538 * 2 ^ 59
def prefixEnd_2808538 : Nat := 4983230072969 + 3 ^ 40 * 2808538 * 2
def baseEnd_2808538 : Nat := 106824439290165764137687

theorem tailTrace_2808538 : CollatzResearch.WordTrace tailWord_2808538 prefixEnd_2808538 106824439290165764137687 := by
  unfold tailWord_2808538
  simp only [CollatzResearch.WordTrace]
  refine ⟨25608949074788490236954567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68290530866102640631878845 25608949074788490236954567)
  ·
    refine ⟨38413423612182735355431851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25608949074788490236954567 38413423612182735355431851)
    ·
      refine ⟨57620135418274103033147777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38413423612182735355431851 57620135418274103033147777)
      ·
        refine ⟨43215101563705577274860833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57620135418274103033147777 43215101563705577274860833)
        ·
          refine ⟨32411326172779182956145625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43215101563705577274860833 32411326172779182956145625)
          ·
            refine ⟨24308494629584387217109219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32411326172779182956145625 24308494629584387217109219)
            ·
              refine ⟨36462741944376580825663829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24308494629584387217109219 36462741944376580825663829)
              ·
                refine ⟨106824439290165764137687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36462741944376580825663829 106824439290165764137687)
                ·
                  rfl

theorem cell22_2808538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 10].length) (baseStart_2808538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808538 prefixEnd_2808538 := by exact prefixLift 2808538
  have htrace : WordTrace (prefixWord ++ tailWord_2808538) baseStart_2808538 baseEnd_2808538 := by
    simpa [prefixWord, tailWord_2808538, baseEnd_2808538] using wordTrace_append hprefix tailTrace_2808538
  have hstable : (prefixWord ++ tailWord_2808538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808538).length < 2 ^ (prefixWord ++ tailWord_2808538).sum := by decide
  have hdescent : baseEnd_2808538 < baseStart_2808538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808568 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 1, 8]
def baseStart_2808568 : Nat := 118140960795 + 2808568 * 2 ^ 59
def prefixEnd_2808568 : Nat := 4983230072969 + 3 ^ 40 * 2808568 * 2
def baseEnd_2808568 : Nat := 961430223224581798989091

theorem tailTrace_2808568 : CollatzResearch.WordTrace tailWord_2808568 prefixEnd_2808568 961430223224581798989091 := by
  unfold tailWord_2808568
  simp only [CollatzResearch.WordTrace]
  refine ⟨51218445244522638035705179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68291260326030184047606905 51218445244522638035705179)
  ·
    refine ⟨76827667866783957053557769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51218445244522638035705179 76827667866783957053557769)
    ·
      refine ⟨57620750900087967790168327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76827667866783957053557769 57620750900087967790168327)
      ·
        refine ⟨86431126350131951685252491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57620750900087967790168327 86431126350131951685252491)
        ·
          refine ⟨129646689525197927527878737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86431126350131951685252491 129646689525197927527878737)
          ·
            refine ⟨97235017143898445645909053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129646689525197927527878737 97235017143898445645909053)
            ·
              refine ⟨36463131428961917117215895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97235017143898445645909053 36463131428961917117215895)
              ·
                refine ⟨54694697143442875675823843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36463131428961917117215895 54694697143442875675823843)
                ·
                  refine ⟨82042045715164313513735765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54694697143442875675823843 82042045715164313513735765)
                  ·
                    refine ⟨961430223224581798989091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82042045715164313513735765 961430223224581798989091)
                    ·
                      rfl

theorem cell22_2808568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_2808568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808568 prefixEnd_2808568 := by exact prefixLift 2808568
  have htrace : WordTrace (prefixWord ++ tailWord_2808568) baseStart_2808568 baseEnd_2808568 := by
    simpa [prefixWord, tailWord_2808568, baseEnd_2808568] using wordTrace_append hprefix tailTrace_2808568
  have hstable : (prefixWord ++ tailWord_2808568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808568).length < 2 ^ (prefixWord ++ tailWord_2808568).sum := by decide
  have hdescent : baseEnd_2808568 < baseStart_2808568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808604 : List Nat := [2, 2, 3, 1, 1, 3, 1, 5, 1, 3]
def baseStart_2808604 : Nat := 118140960795 + 2808604 * 2 ^ 59
def prefixEnd_2808604 : Nat := 4983230072969 + 3 ^ 40 * 2808604 * 2
def baseEnd_2808604 : Nat := 961442546760289705088981

theorem tailTrace_2808604 : CollatzResearch.WordTrace tailWord_2808604 prefixEnd_2808604 961442546760289705088981 := by
  unfold tailWord_2808604
  simp only [CollatzResearch.WordTrace]
  refine ⟨51219101758457427109860433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68292135677943236146480577 51219101758457427109860433)
  ·
    refine ⟨38414326318843070332395325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51219101758457427109860433 38414326318843070332395325)
    ·
      refine ⟨14405372369566151374648247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38414326318843070332395325 14405372369566151374648247)
      ·
        refine ⟨21608058554349227061972371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14405372369566151374648247 21608058554349227061972371)
        ·
          refine ⟨32412087831523840592958557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21608058554349227061972371 32412087831523840592958557)
          ·
            refine ⟨12154532936821440222359459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32412087831523840592958557 12154532936821440222359459)
            ·
              refine ⟨18231799405232160333539189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12154532936821440222359459 18231799405232160333539189)
              ·
                refine ⟨1709231194240515031269299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18231799405232160333539189 1709231194240515031269299)
                ·
                  refine ⟨2563846791360772546903949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1709231194240515031269299 2563846791360772546903949)
                  ·
                    refine ⟨961442546760289705088981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2563846791360772546903949 961442546760289705088981)
                    ·
                      rfl

theorem cell22_2808604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_2808604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808604 prefixEnd_2808604 := by exact prefixLift 2808604
  have htrace : WordTrace (prefixWord ++ tailWord_2808604) baseStart_2808604 baseEnd_2808604 := by
    simpa [prefixWord, tailWord_2808604, baseEnd_2808604] using wordTrace_append hprefix tailTrace_2808604
  have hstable : (prefixWord ++ tailWord_2808604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808604).length < 2 ^ (prefixWord ++ tailWord_2808604).sum := by decide
  have hdescent : baseEnd_2808604 < baseStart_2808604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808634 : List Nat := [3, 1, 1, 1, 6, 1, 3, 1, 5]
def baseStart_2808634 : Nat := 118140960795 + 2808634 * 2 ^ 59
def prefixEnd_2808634 : Nat := 4983230072969 + 3 ^ 40 * 2808634 * 2
def baseEnd_2808634 : Nat := 320484272124459875612963

theorem tailTrace_2808634 : CollatzResearch.WordTrace tailWord_2808634 prefixEnd_2808634 320484272124459875612963 := by
  unfold tailWord_2808634
  simp only [CollatzResearch.WordTrace]
  refine ⟨25609824426701542335828239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68292865137870779562208637 25609824426701542335828239)
  ·
    refine ⟨38414736640052313503742359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25609824426701542335828239 38414736640052313503742359)
    ·
      refine ⟨57622104960078470255613539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38414736640052313503742359 57622104960078470255613539)
      ·
        refine ⟨86433157440117705383420309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57622104960078470255613539 86433157440117705383420309)
        ·
          refine ⟨4051554255005517439847827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86433157440117705383420309 4051554255005517439847827)
          ·
            refine ⟨6077331382508276159771741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051554255005517439847827 6077331382508276159771741)
            ·
              refine ⟨2278999268440603559914403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6077331382508276159771741 2278999268440603559914403)
              ·
                refine ⟨3418498902660905339871605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278999268440603559914403 3418498902660905339871605)
                ·
                  refine ⟨320484272124459875612963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3418498902660905339871605 320484272124459875612963)
                  ·
                    rfl

theorem cell22_2808634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_2808634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808634 prefixEnd_2808634 := by exact prefixLift 2808634
  have htrace : WordTrace (prefixWord ++ tailWord_2808634) baseStart_2808634 baseEnd_2808634 := by
    simpa [prefixWord, tailWord_2808634, baseEnd_2808634] using wordTrace_append hprefix tailTrace_2808634
  have hstable : (prefixWord ++ tailWord_2808634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808634).length < 2 ^ (prefixWord ++ tailWord_2808634).sum := by decide
  have hdescent : baseEnd_2808634 < baseStart_2808634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808677 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 4, 3]
def baseStart_2808677 : Nat := 118140960795 + 2808677 * 2 ^ 59
def prefixEnd_2808677 : Nat := 4983230072969 + 3 ^ 40 * 2808677 * 2
def baseEnd_2808677 : Nat := 961467536152141848013757

theorem tailTrace_2808677 : CollatzResearch.WordTrace tailWord_2808677 prefixEnd_2808677 961467536152141848013757 := by
  unfold tailWord_2808677
  simp only [CollatzResearch.WordTrace]
  refine ⟨102440866045650387687128285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68293910697100258458085523 102440866045650387687128285)
  ·
    refine ⟨38415324767118895382673107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102440866045650387687128285 38415324767118895382673107)
    ·
      refine ⟨57622987150678343074009661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38415324767118895382673107 57622987150678343074009661)
      ·
        refine ⟨21608620181504378652753623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57622987150678343074009661 21608620181504378652753623)
        ·
          refine ⟨32412930272256567979130435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21608620181504378652753623 32412930272256567979130435)
          ·
            refine ⟨48619395408384851968695653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32412930272256567979130435 48619395408384851968695653)
            ·
              refine ⟨9116136639072159744130435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48619395408384851968695653 9116136639072159744130435)
              ·
                refine ⟨13674204958608239616195653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9116136639072159744130435 13674204958608239616195653)
                ·
                  refine ⟨2563913429739044928036685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13674204958608239616195653 2563913429739044928036685)
                  ·
                    refine ⟨961467536152141848013757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2563913429739044928036685 961467536152141848013757)
                    ·
                      rfl

theorem cell22_2808677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_2808677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808677 prefixEnd_2808677 := by exact prefixLift 2808677
  have htrace : WordTrace (prefixWord ++ tailWord_2808677) baseStart_2808677 baseEnd_2808677 := by
    simpa [prefixWord, tailWord_2808677, baseEnd_2808677] using wordTrace_append hprefix tailTrace_2808677
  have hstable : (prefixWord ++ tailWord_2808677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808677).length < 2 ^ (prefixWord ++ tailWord_2808677).sum := by decide
  have hdescent : baseEnd_2808677 < baseStart_2808677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808690 : List Nat := [3, 2, 1, 2, 1, 1, 3, 9]
def baseStart_2808690 : Nat := 118140960795 + 2808690 * 2 ^ 59
def prefixEnd_2808690 : Nat := 4983230072969 + 3 ^ 40 * 2808690 * 2
def baseEnd_2808690 : Nat := 106830220701979349715413

theorem tailTrace_2808690 : CollatzResearch.WordTrace tailWord_2808690 prefixEnd_2808690 106830220701979349715413 := by
  unfold tailWord_2808690
  simp only [CollatzResearch.WordTrace]
  refine ⟨25610335048650822726837881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68294226796402193938234349 25610335048650822726837881)
  ·
    refine ⟨19207751286488117045128411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25610335048650822726837881 19207751286488117045128411)
    ·
      refine ⟨28811626929732175567692617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19207751286488117045128411 28811626929732175567692617)
      ·
        refine ⟨21608720197299131675769463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28811626929732175567692617 21608720197299131675769463)
        ·
          refine ⟨32413080295948697513654195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21608720197299131675769463 32413080295948697513654195)
          ·
            refine ⟨48619620443923046270481293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32413080295948697513654195 48619620443923046270481293)
            ·
              refine ⟨18232357666471142351430485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48619620443923046270481293 18232357666471142351430485)
              ·
                refine ⟨106830220701979349715413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18232357666471142351430485 106830220701979349715413)
                ·
                  rfl

theorem cell22_2808690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 9].length) (baseStart_2808690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808690 prefixEnd_2808690 := by exact prefixLift 2808690
  have htrace : WordTrace (prefixWord ++ tailWord_2808690) baseStart_2808690 baseEnd_2808690 := by
    simpa [prefixWord, tailWord_2808690, baseEnd_2808690] using wordTrace_append hprefix tailTrace_2808690
  have hstable : (prefixWord ++ tailWord_2808690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808690).length < 2 ^ (prefixWord ++ tailWord_2808690).sum := by decide
  have hdescent : baseEnd_2808690 < baseStart_2808690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808737 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 2, 6]
def baseStart_2808737 : Nat := 118140960795 + 2808737 * 2 ^ 59
def prefixEnd_2808737 : Nat := 4983230072969 + 3 ^ 40 * 2808737 * 2
def baseEnd_2808737 : Nat := 961488075378321691513573

theorem tailTrace_2808737 : CollatzResearch.WordTrace tailWord_2808737 prefixEnd_2808737 961488075378321691513573 := by
  unfold tailWord_2808737
  simp only [CollatzResearch.WordTrace]
  refine ⟨102443054425433017934312465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68295369616955345289541643 102443054425433017934312465)
  ·
    refine ⟨76832290819074763450734349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102443054425433017934312465 76832290819074763450734349)
    ·
      refine ⟨28812109057153036294025381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76832290819074763450734349 28812109057153036294025381)
      ·
        refine ⟨5402270448216194305129759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28812109057153036294025381 5402270448216194305129759)
        ·
          refine ⟨8103405672324291457694639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5402270448216194305129759 8103405672324291457694639)
          ·
            refine ⟨12155108508486437186541959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8103405672324291457694639 12155108508486437186541959)
            ·
              refine ⟨18232662762729655779812939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12155108508486437186541959 18232662762729655779812939)
              ·
                refine ⟨27348994144094483669719409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18232662762729655779812939 27348994144094483669719409)
                ·
                  refine ⟨20511745608070862752289557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27348994144094483669719409 20511745608070862752289557)
                  ·
                    refine ⟨961488075378321691513573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20511745608070862752289557 961488075378321691513573)
                    ·
                      rfl

theorem cell22_2808737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_2808737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808737 prefixEnd_2808737 := by exact prefixLift 2808737
  have htrace : WordTrace (prefixWord ++ tailWord_2808737) baseStart_2808737 baseEnd_2808737 := by
    simpa [prefixWord, tailWord_2808737, baseEnd_2808737] using wordTrace_append hprefix tailTrace_2808737
  have hstable : (prefixWord ++ tailWord_2808737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808737).length < 2 ^ (prefixWord ++ tailWord_2808737).sum := by decide
  have hdescent : baseEnd_2808737 < baseStart_2808737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808756 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_2808756 : Nat := 118140960795 + 2808756 * 2 ^ 59
def prefixEnd_2808756 : Nat := 4983230072969 + 3 ^ 40 * 2808756 * 2
def baseEnd_2808756 : Nat := 961494579466611975288515

theorem tailTrace_2808756 : CollatzResearch.WordTrace tailWord_2808756 prefixEnd_2808756 961494579466611975288515 := by
  unfold tailWord_2808756
  simp only [CollatzResearch.WordTrace]
  refine ⟨51221873706182092089627061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68295831608242789452836081 51221873706182092089627061)
  ·
    refine ⟨4802050659954571133402537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51221873706182092089627061 4802050659954571133402537)
    ·
      refine ⟨3601537994965928350051903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4802050659954571133402537 3601537994965928350051903)
      ·
        refine ⟨5402306992448892525077855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3601537994965928350051903 5402306992448892525077855)
        ·
          refine ⟨8103460488673338787616783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5402306992448892525077855 8103460488673338787616783)
          ·
            refine ⟨12155190733010008181425175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8103460488673338787616783 12155190733010008181425175)
            ·
              refine ⟨18232786099515012272137763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12155190733010008181425175 18232786099515012272137763)
              ·
                refine ⟨27349179149272518408206645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18232786099515012272137763 27349179149272518408206645)
                ·
                  refine ⟨2563985545244298600769373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27349179149272518408206645 2563985545244298600769373)
                  ·
                    refine ⟨961494579466611975288515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2563985545244298600769373 961494579466611975288515)
                    ·
                      rfl

theorem cell22_2808756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_2808756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808756 prefixEnd_2808756 := by exact prefixLift 2808756
  have htrace : WordTrace (prefixWord ++ tailWord_2808756) baseStart_2808756 baseEnd_2808756 := by
    simpa [prefixWord, tailWord_2808756, baseEnd_2808756] using wordTrace_append hprefix tailTrace_2808756
  have hstable : (prefixWord ++ tailWord_2808756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808756).length < 2 ^ (prefixWord ++ tailWord_2808756).sum := by decide
  have hdescent : baseEnd_2808756 < baseStart_2808756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808786 : List Nat := [3, 2, 2, 3, 1, 3, 1, 2, 5]
def baseStart_2808786 : Nat := 118140960795 + 2808786 * 2 ^ 59
def prefixEnd_2808786 : Nat := 4983230072969 + 3 ^ 40 * 2808786 * 2
def baseEnd_2808786 : Nat := 320501616359900632346141

theorem tailTrace_2808786 : CollatzResearch.WordTrace tailWord_2808786 prefixEnd_2808786 320501616359900632346141 := by
  unfold tailWord_2808786
  simp only [CollatzResearch.WordTrace]
  refine ⟨25611210400563874825711553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68296561068170332868564141 25611210400563874825711553)
  ·
    refine ⟨19208407800422906119283665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25611210400563874825711553 19208407800422906119283665)
    ·
      refine ⟨14406305850317179589462749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19208407800422906119283665 14406305850317179589462749)
      ·
        refine ⟨5402364693868942346048531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14406305850317179589462749 5402364693868942346048531)
        ·
          refine ⟨8103547040803413519072797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5402364693868942346048531 8103547040803413519072797)
          ·
            refine ⟨3038830140301280069652299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8103547040803413519072797 3038830140301280069652299)
            ·
              refine ⟨4558245210451920104478449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3038830140301280069652299 4558245210451920104478449)
              ·
                refine ⟨3418683907838940078358837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4558245210451920104478449 3418683907838940078358837)
                ·
                  refine ⟨320501616359900632346141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3418683907838940078358837 320501616359900632346141)
                  ·
                    rfl

theorem cell22_2808786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_2808786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808786 prefixEnd_2808786 := by exact prefixLift 2808786
  have htrace : WordTrace (prefixWord ++ tailWord_2808786) baseStart_2808786 baseEnd_2808786 := by
    simpa [prefixWord, tailWord_2808786, baseEnd_2808786] using wordTrace_append hprefix tailTrace_2808786
  have hstable : (prefixWord ++ tailWord_2808786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808786).length < 2 ^ (prefixWord ++ tailWord_2808786).sum := by decide
  have hdescent : baseEnd_2808786 < baseStart_2808786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808827 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 2, 4]
def baseStart_2808827 : Nat := 118140960795 + 2808827 * 2 ^ 59
def prefixEnd_2808827 : Nat := 4983230072969 + 3 ^ 40 * 2808827 * 2
def baseEnd_2808827 : Nat := 961518884217591456763297

theorem tailTrace_2808827 : CollatzResearch.WordTrace tailWord_2808827 prefixEnd_2808827 961518884217591456763297 := by
  unfold tailWord_2808827
  simp only [CollatzResearch.WordTrace]
  refine ⟨102446336995106963305088735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68297557996737975536725823 102446336995106963305088735)
  ·
    refine ⟨153669505492660444957633103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102446336995106963305088735 153669505492660444957633103)
    ·
      refine ⟨230504258238990667436449655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153669505492660444957633103 230504258238990667436449655)
      ·
        refine ⟨345756387358486001154674483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230504258238990667436449655 345756387358486001154674483)
        ·
          refine ⟨518634581037729001732011725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345756387358486001154674483 518634581037729001732011725)
          ·
            refine ⟨194487967889148375649504397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 518634581037729001732011725 194487967889148375649504397)
            ·
              refine ⟨72932987958430640868564149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194487967889148375649504397 72932987958430640868564149)
              ·
                refine ⟨6837467621102872581427889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72932987958430640868564149 6837467621102872581427889)
                ·
                  refine ⟨5128100715827154436070917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6837467621102872581427889 5128100715827154436070917)
                  ·
                    refine ⟨961518884217591456763297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5128100715827154436070917 961518884217591456763297)
                    ·
                      rfl

theorem cell22_2808827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 4].length) (baseStart_2808827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808827 prefixEnd_2808827 := by exact prefixLift 2808827
  have htrace : WordTrace (prefixWord ++ tailWord_2808827) baseStart_2808827 baseEnd_2808827 := by
    simpa [prefixWord, tailWord_2808827, baseEnd_2808827] using wordTrace_append hprefix tailTrace_2808827
  have hstable : (prefixWord ++ tailWord_2808827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808827).length < 2 ^ (prefixWord ++ tailWord_2808827).sum := by decide
  have hdescent : baseEnd_2808827 < baseStart_2808827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808842 : List Nat := [3, 1, 2, 2, 3, 1, 10]
def baseStart_2808842 : Nat := 118140960795 + 2808842 * 2 ^ 59
def prefixEnd_2808842 : Nat := 4983230072969 + 3 ^ 40 * 2808842 * 2
def baseEnd_2808842 : Nat := 35612000704597645097713

theorem tailTrace_2808842 : CollatzResearch.WordTrace tailWord_2808842 prefixEnd_2808842 35612000704597645097713 := by
  unfold tailWord_2808842
  simp only [CollatzResearch.WordTrace]
  refine ⟨25611721022513155216721195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68297922726701747244589853 25611721022513155216721195)
  ·
    refine ⟨38417581533769732825081793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25611721022513155216721195 38417581533769732825081793)
    ·
      refine ⟨28813186150327299618811345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38417581533769732825081793 28813186150327299618811345)
      ·
        refine ⟨21609889612745474714108509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28813186150327299618811345 21609889612745474714108509)
        ·
          refine ⟨8103708604779553017790691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21609889612745474714108509 8103708604779553017790691)
          ·
            refine ⟨12155562907169329526686037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8103708604779553017790691 12155562907169329526686037)
            ·
              refine ⟨35612000704597645097713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12155562907169329526686037 35612000704597645097713)
              ·
                rfl

theorem cell22_2808842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 10].length) (baseStart_2808842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808842 prefixEnd_2808842 := by exact prefixLift 2808842
  have htrace : WordTrace (prefixWord ++ tailWord_2808842) baseStart_2808842 baseEnd_2808842 := by
    simpa [prefixWord, tailWord_2808842, baseEnd_2808842] using wordTrace_append hprefix tailTrace_2808842
  have hstable : (prefixWord ++ tailWord_2808842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808842).length < 2 ^ (prefixWord ++ tailWord_2808842).sum := by decide
  have hdescent : baseEnd_2808842 < baseStart_2808842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808844 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 2, 4]
def baseStart_2808844 : Nat := 118140960795 + 2808844 * 2 ^ 59
def prefixEnd_2808844 : Nat := 4983230072969 + 3 ^ 40 * 2808844 * 2
def baseEnd_2808844 : Nat := 961524703665009079088245

theorem tailTrace_2808844 : CollatzResearch.WordTrace tailWord_2808844 prefixEnd_2808844 961524703665009079088245 := by
  unfold tailWord_2808844
  simp only [CollatzResearch.WordTrace]
  refine ⟨51223478518022687604228793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68297971357363583472305057 51223478518022687604228793)
  ·
    refine ⟨38417608888517015703171595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51223478518022687604228793 38417608888517015703171595)
    ·
      refine ⟨57626413332775523554757393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38417608888517015703171595 57626413332775523554757393)
      ·
        refine ⟨43219809999581642666068045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57626413332775523554757393 43219809999581642666068045)
        ·
          refine ⟨16207428749843115999775517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43219809999581642666068045 16207428749843115999775517)
          ·
            refine ⟨6077785781191168499915819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16207428749843115999775517 6077785781191168499915819)
            ·
              refine ⟨9116678671786752749873729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6077785781191168499915819 9116678671786752749873729)
              ·
                refine ⟨6837509003840064562405297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9116678671786752749873729 6837509003840064562405297)
                ·
                  refine ⟨5128131752880048421803973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6837509003840064562405297 5128131752880048421803973)
                  ·
                    refine ⟨961524703665009079088245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5128131752880048421803973 961524703665009079088245)
                    ·
                      rfl

theorem cell22_2808844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_2808844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808844 prefixEnd_2808844 := by exact prefixLift 2808844
  have htrace : WordTrace (prefixWord ++ tailWord_2808844) baseStart_2808844 baseEnd_2808844 := by
    simpa [prefixWord, tailWord_2808844, baseEnd_2808844] using wordTrace_append hprefix tailTrace_2808844
  have hstable : (prefixWord ++ tailWord_2808844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808844).length < 2 ^ (prefixWord ++ tailWord_2808844).sum := by decide
  have hdescent : baseEnd_2808844 < baseStart_2808844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808863 : List Nat := [1, 1, 2, 4, 1, 5, 2, 1, 2, 3]
def baseStart_2808863 : Nat := 118140960795 + 2808863 * 2 ^ 59
def prefixEnd_2808863 : Nat := 4983230072969 + 3 ^ 40 * 2808863 * 2
def baseEnd_2808863 : Nat := 961531207753299362863187

theorem tailTrace_2808863 : CollatzResearch.WordTrace tailWord_2808863 prefixEnd_2808863 961531207753299362863187 := by
  unfold tailWord_2808863
  simp only [CollatzResearch.WordTrace]
  refine ⟨102447650022976541453399243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68298433348651027635599495 102447650022976541453399243)
  ·
    refine ⟨153671475034464812180098865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102447650022976541453399243 153671475034464812180098865)
    ·
      refine ⟨115253606275848609135074149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153671475034464812180098865 115253606275848609135074149)
      ·
        refine ⟨21610051176721614212826403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115253606275848609135074149 21610051176721614212826403)
        ·
          refine ⟨32415076765082421319239605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21610051176721614212826403 32415076765082421319239605)
          ·
            refine ⟨3038913446726476998678713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32415076765082421319239605 3038913446726476998678713)
            ·
              refine ⟨2279185085044857749009035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3038913446726476998678713 2279185085044857749009035)
              ·
                refine ⟨3418777627567286623513553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279185085044857749009035 3418777627567286623513553)
                ·
                  refine ⟨2564083220675464967635165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3418777627567286623513553 2564083220675464967635165)
                  ·
                    refine ⟨961531207753299362863187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2564083220675464967635165 961531207753299362863187)
                    ·
                      rfl

theorem cell22_2808863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 2, 3].length) (baseStart_2808863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808863 prefixEnd_2808863 := by exact prefixLift 2808863
  have htrace : WordTrace (prefixWord ++ tailWord_2808863) baseStart_2808863 baseEnd_2808863 := by
    simpa [prefixWord, tailWord_2808863, baseEnd_2808863] using wordTrace_append hprefix tailTrace_2808863
  have hstable : (prefixWord ++ tailWord_2808863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808863).length < 2 ^ (prefixWord ++ tailWord_2808863).sum := by decide
  have hdescent : baseEnd_2808863 < baseStart_2808863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808904 : List Nat := [2, 1, 3, 1, 1, 1, 6, 2, 5]
def baseStart_2808904 : Nat := 118140960795 + 2808904 * 2 ^ 59
def prefixEnd_2808904 : Nat := 4983230072969 + 3 ^ 40 * 2808904 * 2
def baseEnd_2808904 : Nat := 320515080963729640862687

theorem tailTrace_2808904 : CollatzResearch.WordTrace tailWord_2808904 prefixEnd_2808904 320515080963729640862687 := by
  unfold tailWord_2808904
  simp only [CollatzResearch.WordTrace]
  refine ⟨51224572707914002727820883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68299430277218670303761177 51224572707914002727820883)
  ·
    refine ⟨76836859061871004091731325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51224572707914002727820883 76836859061871004091731325)
    ·
      refine ⟨28813822148201626534399247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76836859061871004091731325 28813822148201626534399247)
      ·
        refine ⟨43220733222302439801598871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28813822148201626534399247 43220733222302439801598871)
        ·
          refine ⟨64831099833453659702398307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43220733222302439801598871 64831099833453659702398307)
          ·
            refine ⟨97246649750180489553597461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64831099833453659702398307 97246649750180489553597461)
            ·
              refine ⟨4558436707039710447824881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97246649750180489553597461 4558436707039710447824881)
              ·
                refine ⟨3418827530279782835868661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4558436707039710447824881 3418827530279782835868661)
                ·
                  refine ⟨320515080963729640862687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3418827530279782835868661 320515080963729640862687)
                  ·
                    rfl

theorem cell22_2808904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 5].length) (baseStart_2808904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2808904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2808904 prefixEnd_2808904 := by exact prefixLift 2808904
  have htrace : WordTrace (prefixWord ++ tailWord_2808904) baseStart_2808904 baseEnd_2808904 := by
    simpa [prefixWord, tailWord_2808904, baseEnd_2808904] using wordTrace_append hprefix tailTrace_2808904
  have hstable : (prefixWord ++ tailWord_2808904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808904).length < 2 ^ (prefixWord ++ tailWord_2808904).sum := by decide
  have hdescent : baseEnd_2808904 < baseStart_2808904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809116 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 1, 5]
def baseStart_2809116 : Nat := 118140960795 + 2809116 * 2 ^ 59
def prefixEnd_2809116 : Nat := 4983230072969 + 3 ^ 40 * 2809116 * 2
def baseEnd_2809116 : Nat := 961617814823691036287411

theorem tailTrace_2809116 : CollatzResearch.WordTrace tailWord_2809116 prefixEnd_2809116 961617814823691036287411 := by
  unfold tailWord_2809116
  simp only [CollatzResearch.WordTrace]
  refine ⟨51228438845529982831179601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68304585127373310441572801 51228438845529982831179601)
  ·
    refine ⟨38421329134147487123384701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51228438845529982831179601 38421329134147487123384701)
    ·
      refine ⟨14407998425305307671269263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38421329134147487123384701 14407998425305307671269263)
      ·
        refine ⟨21611997637957961506903895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14407998425305307671269263 21611997637957961506903895)
        ·
          refine ⟨32417996456936942260355843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21611997637957961506903895 32417996456936942260355843)
          ·
            refine ⟨48626994685405413390533765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32417996456936942260355843 48626994685405413390533765)
            ·
              refine ⟨9117561503513515010725081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48626994685405413390533765 9117561503513515010725081)
              ·
                refine ⟨6838171127635136258043811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9117561503513515010725081 6838171127635136258043811)
                ·
                  refine ⟨10257256691452704387065717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6838171127635136258043811 10257256691452704387065717)
                  ·
                    refine ⟨961617814823691036287411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10257256691452704387065717 961617814823691036287411)
                    ·
                      rfl

theorem cell22_2809116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_2809116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2809116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2809116 prefixEnd_2809116 := by exact prefixLift 2809116
  have htrace : WordTrace (prefixWord ++ tailWord_2809116) baseStart_2809116 baseEnd_2809116 := by
    simpa [prefixWord, tailWord_2809116, baseEnd_2809116] using wordTrace_append hprefix tailTrace_2809116
  have hstable : (prefixWord ++ tailWord_2809116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809116).length < 2 ^ (prefixWord ++ tailWord_2809116).sum := by decide
  have hdescent : baseEnd_2809116 < baseStart_2809116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809251 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 3, 5]
def baseStart_2809251 : Nat := 118140960795 + 2809251 * 2 ^ 59
def prefixEnd_2809251 : Nat := 4983230072969 + 3 ^ 40 * 2809251 * 2
def baseEnd_2809251 : Nat := 961664028082595684161997

theorem tailTrace_2809251 : CollatzResearch.WordTrace tailWord_2809251 prefixEnd_2809251 961664028082595684161997 := by
  unfold tailWord_2809251
  simp only [CollatzResearch.WordTrace]
  refine ⟨102461801545570883718523607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68307867697047255812349071 102461801545570883718523607)
  ·
    refine ⟨153692702318356325577785411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102461801545570883718523607 153692702318356325577785411)
    ·
      refine ⟨230539053477534488366678117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153692702318356325577785411 230539053477534488366678117)
      ·
        refine ⟨43226072527037716568752147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230539053477534488366678117 43226072527037716568752147)
        ·
          refine ⟨64839108790556574853128221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43226072527037716568752147 64839108790556574853128221)
          ·
            refine ⟨24314665796458715569923083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64839108790556574853128221 24314665796458715569923083)
            ·
              refine ⟨36471998694688073354884625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24314665796458715569923083 36471998694688073354884625)
              ·
                refine ⟨27353999021016055016163469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36471998694688073354884625 27353999021016055016163469)
                ·
                  refine ⟨10257749632881020631061301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27353999021016055016163469 10257749632881020631061301)
                  ·
                    refine ⟨961664028082595684161997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10257749632881020631061301 961664028082595684161997)
                    ·
                      rfl

theorem cell22_2809251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 5].length) (baseStart_2809251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2809251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2809251 prefixEnd_2809251 := by exact prefixLift 2809251
  have htrace : WordTrace (prefixWord ++ tailWord_2809251) baseStart_2809251 baseEnd_2809251 := by
    simpa [prefixWord, tailWord_2809251, baseEnd_2809251] using wordTrace_append hprefix tailTrace_2809251
  have hstable : (prefixWord ++ tailWord_2809251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809251).length < 2 ^ (prefixWord ++ tailWord_2809251).sum := by decide
  have hdescent : baseEnd_2809251 < baseStart_2809251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809283 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 2, 4]
def baseStart_2809283 : Nat := 118140960795 + 2809283 * 2 ^ 59
def prefixEnd_2809283 : Nat := 4983230072969 + 3 ^ 40 * 2809283 * 2
def baseEnd_2809283 : Nat := 961674982336558267361899

theorem tailTrace_2809283 : CollatzResearch.WordTrace tailWord_2809283 prefixEnd_2809283 961674982336558267361899 := by
  unfold tailWord_2809283
  simp only [CollatzResearch.WordTrace]
  refine ⟨102462968681454953183688503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68308645787636635455792335 102462968681454953183688503)
  ·
    refine ⟨153694453022182429775532755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102462968681454953183688503 153694453022182429775532755)
    ·
      refine ⟨230541679533273644663299133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153694453022182429775532755 230541679533273644663299133)
      ·
        refine ⟨86453129824977616748737175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230541679533273644663299133 86453129824977616748737175)
        ·
          refine ⟨129679694737466425123105763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86453129824977616748737175 129679694737466425123105763)
          ·
            refine ⟨194519542106199637684658645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129679694737466425123105763 194519542106199637684658645)
            ·
              refine ⟨4559051768114054008234187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 194519542106199637684658645 4559051768114054008234187)
              ·
                refine ⟨6838577652171081012351281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4559051768114054008234187 6838577652171081012351281)
                ·
                  refine ⟨5128933239128310759263461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6838577652171081012351281 5128933239128310759263461)
                  ·
                    refine ⟨961674982336558267361899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5128933239128310759263461 961674982336558267361899)
                    ·
                      rfl

theorem cell22_2809283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 4].length) (baseStart_2809283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2809283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2809283 prefixEnd_2809283 := by exact prefixLift 2809283
  have htrace : WordTrace (prefixWord ++ tailWord_2809283) baseStart_2809283 baseEnd_2809283 := by
    simpa [prefixWord, tailWord_2809283, baseEnd_2809283] using wordTrace_append hprefix tailTrace_2809283
  have hstable : (prefixWord ++ tailWord_2809283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809283).length < 2 ^ (prefixWord ++ tailWord_2809283).sum := by decide
  have hdescent : baseEnd_2809283 < baseStart_2809283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809302 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_2809302 : Nat := 118140960795 + 2809302 * 2 ^ 59
def prefixEnd_2809302 : Nat := 4983230072969 + 3 ^ 40 * 2809302 * 2
def baseEnd_2809302 : Nat := 961681486424848551136841

theorem tailTrace_2809302 : CollatzResearch.WordTrace tailWord_2809302 prefixEnd_2809302 961681486424848551136841 := by
  unfold tailWord_2809302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6403978854274132464289385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68309107778924079619086773 6403978854274132464289385)
  ·
    refine ⟨4802984140705599348217039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6403978854274132464289385 4802984140705599348217039)
    ·
      refine ⟨7204476211058399022325559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4802984140705599348217039 7204476211058399022325559)
      ·
        refine ⟨10806714316587598533488339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7204476211058399022325559 10806714316587598533488339)
        ·
          refine ⟨16210071474881397800232509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10806714316587598533488339 16210071474881397800232509)
          ·
            refine ⟨6078776803080524175087191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16210071474881397800232509 6078776803080524175087191)
            ·
              refine ⟨9118165204620786262630787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6078776803080524175087191 9118165204620786262630787)
              ·
                refine ⟨13677247806931179393946181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9118165204620786262630787 13677247806931179393946181)
                ·
                  refine ⟨2564483963799596136364909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13677247806931179393946181 2564483963799596136364909)
                  ·
                    refine ⟨961681486424848551136841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2564483963799596136364909 961681486424848551136841)
                    ·
                      rfl

theorem cell22_2809302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_2809302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2809302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2809302 prefixEnd_2809302 := by exact prefixLift 2809302
  have htrace : WordTrace (prefixWord ++ tailWord_2809302) baseStart_2809302 baseEnd_2809302 := by
    simpa [prefixWord, tailWord_2809302, baseEnd_2809302] using wordTrace_append hprefix tailTrace_2809302
  have hstable : (prefixWord ++ tailWord_2809302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809302).length < 2 ^ (prefixWord ++ tailWord_2809302).sum := by decide
  have hdescent : baseEnd_2809302 < baseStart_2809302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809377 : List Nat := [1, 2, 3, 2, 2, 4, 2, 1, 5]
def baseStart_2809377 : Nat := 118140960795 + 2809377 * 2 ^ 59
def prefixEnd_2809377 : Nat := 4983230072969 + 3 ^ 40 * 2809377 * 2
def baseEnd_2809377 : Nat := 320569053485857785170537

theorem tailTrace_2809377 : CollatzResearch.WordTrace tailWord_2809377 prefixEnd_2809377 320569053485857785170537 := by
  unfold tailWord_2809377
  simp only [CollatzResearch.WordTrace]
  refine ⟨102466397143114407237610385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68310931428742938158406923 102466397143114407237610385)
  ·
    refine ⟨76849797857335805428207789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102466397143114407237610385 76849797857335805428207789)
    ·
      refine ⟨28818674196500927035577921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76849797857335805428207789 28818674196500927035577921)
      ·
        refine ⟨21614005647375695276683441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28818674196500927035577921 21614005647375695276683441)
        ·
          refine ⟨16210504235531771457512581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21614005647375695276683441 16210504235531771457512581)
          ·
            refine ⟨3039469544162207148283609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16210504235531771457512581 3039469544162207148283609)
            ·
              refine ⟨2279602158121655361212707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3039469544162207148283609 2279602158121655361212707)
              ·
                refine ⟨3419403237182483041819061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279602158121655361212707 3419403237182483041819061)
                ·
                  refine ⟨320569053485857785170537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3419403237182483041819061 320569053485857785170537)
                  ·
                    rfl

theorem cell22_2809377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 5].length) (baseStart_2809377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2809377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2809377 prefixEnd_2809377 := by exact prefixLift 2809377
  have htrace : WordTrace (prefixWord ++ tailWord_2809377) baseStart_2809377 baseEnd_2809377 := by
    simpa [prefixWord, tailWord_2809377, baseEnd_2809377] using wordTrace_append hprefix tailTrace_2809377
  have hstable : (prefixWord ++ tailWord_2809377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809377).length < 2 ^ (prefixWord ++ tailWord_2809377).sum := by decide
  have hdescent : baseEnd_2809377 < baseStart_2809377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809407 : List Nat := [1, 1, 2, 2, 3, 4, 3, 1, 1, 4]
def baseStart_2809407 : Nat := 118140960795 + 2809407 * 2 ^ 59
def prefixEnd_2809407 : Nat := 4983230072969 + 3 ^ 40 * 2809407 * 2
def baseEnd_2809407 : Nat := 961717430070663277261519

theorem tailTrace_2809407 : CollatzResearch.WordTrace tailWord_2809407 prefixEnd_2809407 961717430070663277261519 := by
  unfold tailWord_2809407
  simp only [CollatzResearch.WordTrace]
  refine ⟨102467491333005722361202475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68311660888670481574134983 102467491333005722361202475)
  ·
    refine ⟨153701236999508583541803713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102467491333005722361202475 153701236999508583541803713)
    ·
      refine ⟨115275927749631437656352785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153701236999508583541803713 115275927749631437656352785)
      ·
        refine ⟨86456945812223578242264589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115275927749631437656352785 86456945812223578242264589)
        ·
          refine ⟨32421354679583841840849221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86456945812223578242264589 32421354679583841840849221)
          ·
            refine ⟨6079004002421970345159229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32421354679583841840849221 6079004002421970345159229)
            ·
              refine ⟨2279626500908238879434711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6079004002421970345159229 2279626500908238879434711)
              ·
                refine ⟨3419439751362358319152067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279626500908238879434711 3419439751362358319152067)
                ·
                  refine ⟨5129159627043537478728101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3419439751362358319152067 5129159627043537478728101)
                  ·
                    refine ⟨961717430070663277261519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5129159627043537478728101 961717430070663277261519)
                    ·
                      rfl

theorem cell22_2809407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 1, 4].length) (baseStart_2809407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2809407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2809407 prefixEnd_2809407 := by exact prefixLift 2809407
  have htrace : WordTrace (prefixWord ++ tailWord_2809407) baseStart_2809407 baseEnd_2809407 := by
    simpa [prefixWord, tailWord_2809407, baseEnd_2809407] using wordTrace_append hprefix tailTrace_2809407
  have hstable : (prefixWord ++ tailWord_2809407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809407).length < 2 ^ (prefixWord ++ tailWord_2809407).sum := by decide
  have hdescent : baseEnd_2809407 < baseStart_2809407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809465 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 5, 3]
def baseStart_2809465 : Nat := 118140960795 + 2809465 * 2 ^ 59
def prefixEnd_2809465 : Nat := 4983230072969 + 3 ^ 40 * 2809465 * 2
def baseEnd_2809465 : Nat := 961737284655970459311341

theorem tailTrace_2809465 : CollatzResearch.WordTrace tailWord_2809465 prefixEnd_2809465 961737284655970459311341 := by
  unfold tailWord_2809465
  simp only [CollatzResearch.WordTrace]
  refine ⟨102469606766795598266813849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68313071177863732177875899 102469606766795598266813849)
  ·
    refine ⟨76852205075096698700110387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102469606766795598266813849 76852205075096698700110387)
    ·
      refine ⟨115278307612645048050165581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76852205075096698700110387 115278307612645048050165581)
      ·
        refine ⟨43229365354741893018812093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115278307612645048050165581 43229365354741893018812093)
        ·
          refine ⟨16211012008028209882054535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43229365354741893018812093 16211012008028209882054535)
          ·
            refine ⟨24316518012042314823081803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16211012008028209882054535 24316518012042314823081803)
            ·
              refine ⟨36474777018063472234622705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24316518012042314823081803 36474777018063472234622705)
              ·
                refine ⟨27356082763547604175967029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36474777018063472234622705 27356082763547604175967029)
                ·
                  refine ⟨2564632759082587891496909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27356082763547604175967029 2564632759082587891496909)
                  ·
                    refine ⟨961737284655970459311341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2564632759082587891496909 961737284655970459311341)
                    ·
                      rfl

theorem cell22_2809465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 3].length) (baseStart_2809465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2809465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2809465 prefixEnd_2809465 := by exact prefixLift 2809465
  have htrace : WordTrace (prefixWord ++ tailWord_2809465) baseStart_2809465 baseEnd_2809465 := by
    simpa [prefixWord, tailWord_2809465, baseEnd_2809465] using wordTrace_append hprefix tailTrace_2809465
  have hstable : (prefixWord ++ tailWord_2809465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809465).length < 2 ^ (prefixWord ++ tailWord_2809465).sum := by decide
  have hdescent : baseEnd_2809465 < baseStart_2809465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809482 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 3, 3]
def baseStart_2809482 : Nat := 118140960795 + 2809482 * 2 ^ 59
def prefixEnd_2809482 : Nat := 4983230072969 + 3 ^ 40 * 2809482 * 2
def baseEnd_2809482 : Nat := 961743104103388081636289

theorem tailTrace_2809482 : CollatzResearch.WordTrace tailWord_2809482 prefixEnd_2809482 961743104103388081636289 := by
  unfold tailWord_2809482
  simp only [CollatzResearch.WordTrace]
  refine ⟨25617556701933502542545675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68313484538489340113455133 25617556701933502542545675)
  ·
    refine ⟨38426335052900253813818513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25617556701933502542545675 38426335052900253813818513)
    ·
      refine ⟨28819751289675190360363885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38426335052900253813818513 28819751289675190360363885)
      ·
        refine ⟨10807406733628196385136457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28819751289675190360363885 10807406733628196385136457)
        ·
          refine ⟨8105555050221147288852343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10807406733628196385136457 8105555050221147288852343)
          ·
            refine ⟨12158332575331720933278515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8105555050221147288852343 12158332575331720933278515)
            ·
              refine ⟨18237498862997581399917773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12158332575331720933278515 18237498862997581399917773)
              ·
                refine ⟨6839062073624093024969165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18237498862997581399917773 6839062073624093024969165)
                ·
                  refine ⟨2564648277609034884363437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6839062073624093024969165 2564648277609034884363437)
                  ·
                    refine ⟨961743104103388081636289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2564648277609034884363437 961743104103388081636289)
                    ·
                      rfl

theorem cell22_2809482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_2809482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2809482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2809482 prefixEnd_2809482 := by exact prefixLift 2809482
  have htrace : WordTrace (prefixWord ++ tailWord_2809482) baseStart_2809482 baseEnd_2809482 := by
    simpa [prefixWord, tailWord_2809482, baseEnd_2809482] using wordTrace_append hprefix tailTrace_2809482
  have hstable : (prefixWord ++ tailWord_2809482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809482).length < 2 ^ (prefixWord ++ tailWord_2809482).sum := by decide
  have hdescent : baseEnd_2809482 < baseStart_2809482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809546 : List Nat := [3, 1, 2, 1, 6, 1, 2, 1, 5]
def baseStart_2809546 : Nat := 118140960795 + 2809546 * 2 ^ 59
def prefixEnd_2809546 : Nat := 4983230072969 + 3 ^ 40 * 2809546 * 2
def baseEnd_2809546 : Nat := 320588337537104416012031

theorem tailTrace_2809546 : CollatzResearch.WordTrace tailWord_2809546 prefixEnd_2809546 320588337537104416012031 := by
  unfold tailWord_2809546
  simp only [CollatzResearch.WordTrace]
  refine ⟨25618140269875537275128123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68315040719668099400341661 25618140269875537275128123)
  ·
    refine ⟨38427210404813305912692185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25618140269875537275128123 38427210404813305912692185)
    ·
      refine ⟨28820407803609979434519139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38427210404813305912692185 28820407803609979434519139)
      ·
        refine ⟨43230611705414969151778709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28820407803609979434519139 43230611705414969151778709)
        ·
          refine ⟨2026434923691326678989627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43230611705414969151778709 2026434923691326678989627)
          ·
            refine ⟨3039652385536990018484441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026434923691326678989627 3039652385536990018484441)
            ·
              refine ⟨2279739289152742513863331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3039652385536990018484441 2279739289152742513863331)
              ·
                refine ⟨3419608933729113770794997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279739289152742513863331 3419608933729113770794997)
                ·
                  refine ⟨320588337537104416012031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3419608933729113770794997 320588337537104416012031)
                  ·
                    rfl

theorem cell22_2809546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_2809546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2809546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2809546 prefixEnd_2809546 := by exact prefixLift 2809546
  have htrace : WordTrace (prefixWord ++ tailWord_2809546) baseStart_2809546 baseEnd_2809546 := by
    simpa [prefixWord, tailWord_2809546, baseEnd_2809546] using wordTrace_append hprefix tailTrace_2809546
  have hstable : (prefixWord ++ tailWord_2809546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809546).length < 2 ^ (prefixWord ++ tailWord_2809546).sum := by decide
  have hdescent : baseEnd_2809546 < baseStart_2809546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809709 : List Nat := [1, 5, 1, 1, 1, 1, 2, 6, 4]
def baseStart_2809709 : Nat := 118140960795 + 2809709 * 2 ^ 59
def prefixEnd_2809709 : Nat := 4983230072969 + 3 ^ 40 * 2809709 * 2
def baseEnd_2809709 : Nat := 320606936947478385403531

theorem tailTrace_2809709 : CollatzResearch.WordTrace tailWord_2809709 prefixEnd_2809709 320606936947478385403531 := by
  unfold tailWord_2809709
  simp only [CollatzResearch.WordTrace]
  refine ⟨102478506177911627938696181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68319004118607751959130787 102478506177911627938696181)
  ·
    refine ⟨9607359954179215119252767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102478506177911627938696181 9607359954179215119252767)
    ·
      refine ⟨14411039931268822678879151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9607359954179215119252767 14411039931268822678879151)
      ·
        refine ⟨21616559896903234018318727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14411039931268822678879151 21616559896903234018318727)
        ·
          refine ⟨32424839845354851027478091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21616559896903234018318727 32424839845354851027478091)
          ·
            refine ⟨48637259768032276541217137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32424839845354851027478091 48637259768032276541217137)
            ·
              refine ⟨36477944826024207405912853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48637259768032276541217137 36477944826024207405912853)
              ·
                refine ⟨1709903663719884722152165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36477944826024207405912853 1709903663719884722152165)
                ·
                  refine ⟨320606936947478385403531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1709903663719884722152165 320606936947478385403531)
                  ·
                    rfl

theorem cell22_2809709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_2809709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2809709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2809709 prefixEnd_2809709 := by exact prefixLift 2809709
  have htrace : WordTrace (prefixWord ++ tailWord_2809709) baseStart_2809709 baseEnd_2809709 := by
    simpa [prefixWord, tailWord_2809709, baseEnd_2809709] using wordTrace_append hprefix tailTrace_2809709
  have hstable : (prefixWord ++ tailWord_2809709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809709).length < 2 ^ (prefixWord ++ tailWord_2809709).sum := by decide
  have hdescent : baseEnd_2809709 < baseStart_2809709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809861 : List Nat := [1, 3, 1, 1, 2, 4, 3, 3, 4]
def baseStart_2809861 : Nat := 118140960795 + 2809861 * 2 ^ 59
def prefixEnd_2809861 : Nat := 4983230072969 + 3 ^ 40 * 2809861 * 2
def baseEnd_2809861 : Nat := 320624281182919142136709

theorem tailTrace_2809861 : CollatzResearch.WordTrace tailWord_2809861 prefixEnd_2809861 320624281182919142136709 := by
  unfold tailWord_2809861
  simp only [CollatzResearch.WordTrace]
  refine ⟨102484050073360957898229437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68322700048907305265486291 102484050073360957898229437)
  ·
    refine ⟨38431518777510359211836039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102484050073360957898229437 38431518777510359211836039)
    ·
      refine ⟨57647278166265538817754059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38431518777510359211836039 57647278166265538817754059)
      ·
        refine ⟨86470917249398308226631089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57647278166265538817754059 86470917249398308226631089)
        ·
          refine ⟨64853187937048731169973317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86470917249398308226631089 64853187937048731169973317)
          ·
            refine ⟨12159972738196637094369997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64853187937048731169973317 12159972738196637094369997)
            ·
              refine ⟨4559989776823738910388749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12159972738196637094369997 4559989776823738910388749)
              ·
                refine ⟨1709996166308902091395781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4559989776823738910388749 1709996166308902091395781)
                ·
                  refine ⟨320624281182919142136709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1709996166308902091395781 320624281182919142136709)
                  ·
                    rfl

theorem cell22_2809861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_2809861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2809861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2809861 prefixEnd_2809861 := by exact prefixLift 2809861
  have htrace : WordTrace (prefixWord ++ tailWord_2809861) baseStart_2809861 baseEnd_2809861 := by
    simpa [prefixWord, tailWord_2809861, baseEnd_2809861] using wordTrace_append hprefix tailTrace_2809861
  have hstable : (prefixWord ++ tailWord_2809861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809861).length < 2 ^ (prefixWord ++ tailWord_2809861).sum := by decide
  have hdescent : baseEnd_2809861 < baseStart_2809861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809893 : List Nat := [1, 3, 1, 2, 2, 3, 4, 1, 2, 3]
def baseStart_2809893 : Nat := 118140960795 + 2809893 * 2 ^ 59
def prefixEnd_2809893 : Nat := 4983230072969 + 3 ^ 40 * 2809893 * 2
def baseEnd_2809893 : Nat := 961883797802720009610029

theorem tailTrace_2809893 : CollatzResearch.WordTrace tailWord_2809893 prefixEnd_2809893 961883797802720009610029 := by
  unfold tailWord_2809893
  simp only [CollatzResearch.WordTrace]
  refine ⟨102485217209245027363394333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68323478139496684908929555 102485217209245027363394333)
  ·
    refine ⟨38431956453466885261272875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102485217209245027363394333 38431956453466885261272875)
    ·
      refine ⟨57647934680200327891909313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38431956453466885261272875 57647934680200327891909313)
      ·
        refine ⟨43235951010150245918931985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57647934680200327891909313 43235951010150245918931985)
        ·
          refine ⟨32426963257612684439198989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43235951010150245918931985 32426963257612684439198989)
          ·
            refine ⟨12160111221604756664699621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32426963257612684439198989 12160111221604756664699621)
            ·
              refine ⟨2280020854050891874631179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12160111221604756664699621 2280020854050891874631179)
              ·
                refine ⟨3420031281076337811946769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2280020854050891874631179 3420031281076337811946769)
                ·
                  refine ⟨2565023460807253358960077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3420031281076337811946769 2565023460807253358960077)
                  ·
                    refine ⟨961883797802720009610029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2565023460807253358960077 961883797802720009610029)
                    ·
                      rfl

theorem cell22_2809893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_2809893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2809893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2809893 prefixEnd_2809893 := by exact prefixLift 2809893
  have htrace : WordTrace (prefixWord ++ tailWord_2809893) baseStart_2809893 baseEnd_2809893 := by
    simpa [prefixWord, tailWord_2809893, baseEnd_2809893] using wordTrace_append hprefix tailTrace_2809893
  have hstable : (prefixWord ++ tailWord_2809893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809893).length < 2 ^ (prefixWord ++ tailWord_2809893).sum := by decide
  have hdescent : baseEnd_2809893 < baseStart_2809893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809985 : List Nat := [1, 2, 4, 2, 4, 1, 1, 2, 5]
def baseStart_2809985 : Nat := 118140960795 + 2809985 * 2 ^ 59
def prefixEnd_2809985 : Nat := 4983230072969 + 3 ^ 40 * 2809985 * 2
def baseEnd_2809985 : Nat := 320638430427620812103249

theorem tailTrace_2809985 : CollatzResearch.WordTrace tailWord_2809985 prefixEnd_2809985 320638430427620812103249 := by
  unfold tailWord_2809985
  simp only [CollatzResearch.WordTrace]
  refine ⟨102488572724911727075743409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68325715149941151383828939 102488572724911727075743409)
  ·
    refine ⟨76866429543683795306807557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102488572724911727075743409 76866429543683795306807557)
    ·
      refine ⟨14412455539440711620026417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76866429543683795306807557 14412455539440711620026417)
      ·
        refine ⟨10809341654580533715019813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14412455539440711620026417 10809341654580533715019813)
        ·
          refine ⟨2026751560233850071566215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10809341654580533715019813 2026751560233850071566215)
          ·
            refine ⟨3040127340350775107349323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026751560233850071566215 3040127340350775107349323)
            ·
              refine ⟨4560191010526162661023985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3040127340350775107349323 4560191010526162661023985)
              ·
                refine ⟨3420143257894621995767989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4560191010526162661023985 3420143257894621995767989)
                ·
                  refine ⟨320638430427620812103249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3420143257894621995767989 320638430427620812103249)
                  ·
                    rfl

theorem cell22_2809985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 5].length) (baseStart_2809985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2809985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2809985 prefixEnd_2809985 := by exact prefixLift 2809985
  have htrace : WordTrace (prefixWord ++ tailWord_2809985) baseStart_2809985 baseEnd_2809985 := by
    simpa [prefixWord, tailWord_2809985, baseEnd_2809985] using wordTrace_append hprefix tailTrace_2809985
  have hstable : (prefixWord ++ tailWord_2809985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809985).length < 2 ^ (prefixWord ++ tailWord_2809985).sum := by decide
  have hdescent : baseEnd_2809985 < baseStart_2809985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810062 : List Nat := [4, 1, 1, 1, 4, 3, 2, 1, 2, 3]
def baseStart_2810062 : Nat := 118140960795 + 2810062 * 2 ^ 59
def prefixEnd_2810062 : Nat := 4983230072969 + 3 ^ 40 * 2810062 * 2
def baseEnd_2810062 : Nat := 961941649956459902134511

theorem tailTrace_2810062 : CollatzResearch.WordTrace tailWord_2810062 prefixEnd_2810062 961941649956459902134511 := by
  unfold tailWord_2810062
  simp only [CollatzResearch.WordTrace]
  refine ⟨12811422643204096153287055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68327587430421846150864293 12811422643204096153287055)
  ·
    refine ⟨19217133964806144229930583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12811422643204096153287055 19217133964806144229930583)
    ·
      refine ⟨28825700947209216344895875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19217133964806144229930583 28825700947209216344895875)
      ·
        refine ⟨43238551420813824517343813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28825700947209216344895875 43238551420813824517343813)
        ·
          refine ⟨8107228391402592097001965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43238551420813824517343813 8107228391402592097001965)
          ·
            refine ⟨3040210646775972036375737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8107228391402592097001965 3040210646775972036375737)
            ·
              refine ⟨2280157985081979027281803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3040210646775972036375737 2280157985081979027281803)
              ·
                refine ⟨3420236977622968540922705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2280157985081979027281803 3420236977622968540922705)
                ·
                  refine ⟨2565177733217226405692029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3420236977622968540922705 2565177733217226405692029)
                  ·
                    refine ⟨961941649956459902134511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2565177733217226405692029 961941649956459902134511)
                    ·
                      rfl

theorem cell22_2810062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_2810062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810062 prefixEnd_2810062 := by exact prefixLift 2810062
  have htrace : WordTrace (prefixWord ++ tailWord_2810062) baseStart_2810062 baseEnd_2810062 := by
    simpa [prefixWord, tailWord_2810062, baseEnd_2810062] using wordTrace_append hprefix tailTrace_2810062
  have hstable : (prefixWord ++ tailWord_2810062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810062).length < 2 ^ (prefixWord ++ tailWord_2810062).sum := by decide
  have hdescent : baseEnd_2810062 < baseStart_2810062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810090 : List Nat := [3, 1, 3, 1, 1, 2, 2, 5, 1, 3]
def baseStart_2810090 : Nat := 118140960795 + 2810090 * 2 ^ 59
def prefixEnd_2810090 : Nat := 4983230072969 + 3 ^ 40 * 2810090 * 2
def baseEnd_2810090 : Nat := 961951234928677162434425

theorem tailTrace_2810090 : CollatzResearch.WordTrace tailWord_2810090 prefixEnd_2810090 961951234928677162434425 := by
  unfold tailWord_2810090
  simp only [CollatzResearch.WordTrace]
  refine ⟨25623100597382832502078931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68328268259687553338877149 25623100597382832502078931)
  ·
    refine ⟨38434650896074248753118397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25623100597382832502078931 38434650896074248753118397)
    ·
      refine ⟨14412994086027843282419399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38434650896074248753118397 14412994086027843282419399)
      ·
        refine ⟨21619491129041764923629099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14412994086027843282419399 21619491129041764923629099)
        ·
          refine ⟨32429236693562647385443649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21619491129041764923629099 32429236693562647385443649)
          ·
            refine ⟨24321927520171985539082737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32429236693562647385443649 24321927520171985539082737)
            ·
              refine ⟨18241445640128989154312053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24321927520171985539082737 18241445640128989154312053)
              ·
                refine ⟨1710135528762092733216755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18241445640128989154312053 1710135528762092733216755)
                ·
                  refine ⟨2565203293143139099825133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710135528762092733216755 2565203293143139099825133)
                  ·
                    refine ⟨961951234928677162434425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2565203293143139099825133 961951234928677162434425)
                    ·
                      rfl

theorem cell22_2810090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_2810090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810090 prefixEnd_2810090 := by exact prefixLift 2810090
  have htrace : WordTrace (prefixWord ++ tailWord_2810090) baseStart_2810090 baseEnd_2810090 := by
    simpa [prefixWord, tailWord_2810090, baseEnd_2810090] using wordTrace_append hprefix tailTrace_2810090
  have hstable : (prefixWord ++ tailWord_2810090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810090).length < 2 ^ (prefixWord ++ tailWord_2810090).sum := by decide
  have hdescent : baseEnd_2810090 < baseStart_2810090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810163 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 4, 3]
def baseStart_2810163 : Nat := 118140960795 + 2810163 * 2 ^ 59
def prefixEnd_2810163 : Nat := 4983230072969 + 3 ^ 40 * 2810163 * 2
def baseEnd_2810163 : Nat := 961976224320529305359201

theorem tailTrace_2810163 : CollatzResearch.WordTrace tailWord_2810163 prefixEnd_2810163 961976224320529305359201 := by
  unfold tailWord_2810163
  simp only [CollatzResearch.WordTrace]
  refine ⟨102495064918266863475723143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68330043278844575650482095 102495064918266863475723143)
  ·
    refine ⟨153742597377400295213584715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102495064918266863475723143 153742597377400295213584715)
    ·
      refine ⟨230613896066100442820377073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153742597377400295213584715 230613896066100442820377073)
      ·
        refine ⟨172960422049575332115282805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230613896066100442820377073 172960422049575332115282805)
        ·
          refine ⟨16215039567147687385807763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172960422049575332115282805 16215039567147687385807763)
          ·
            refine ⟨24322559350721531078711645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16215039567147687385807763 24322559350721531078711645)
            ·
              refine ⟨9120959756520574154516867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24322559350721531078711645 9120959756520574154516867)
              ·
                refine ⟨13681439634780861231775301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9120959756520574154516867 13681439634780861231775301)
                ·
                  refine ⟨2565269931521411480957869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13681439634780861231775301 2565269931521411480957869)
                  ·
                    refine ⟨961976224320529305359201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2565269931521411480957869 961976224320529305359201)
                    ·
                      rfl

theorem cell22_2810163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 3].length) (baseStart_2810163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810163 prefixEnd_2810163 := by exact prefixLift 2810163
  have htrace : WordTrace (prefixWord ++ tailWord_2810163) baseStart_2810163 baseEnd_2810163 := by
    simpa [prefixWord, tailWord_2810163, baseEnd_2810163] using wordTrace_append hprefix tailTrace_2810163
  have hstable : (prefixWord ++ tailWord_2810163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810163).length < 2 ^ (prefixWord ++ tailWord_2810163).sum := by decide
  have hdescent : baseEnd_2810163 < baseStart_2810163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810193 : List Nat := [1, 2, 2, 1, 4, 2, 4, 6]
def baseStart_2810193 : Nat := 118140960795 + 2810193 * 2 ^ 59
def prefixEnd_2810193 : Nat := 4983230072969 + 3 ^ 40 * 2810193 * 2
def baseEnd_2810193 : Nat := 106887388214846580789901

theorem tailTrace_2810193 : CollatzResearch.WordTrace tailWord_2810193 prefixEnd_2810193 106887388214846580789901 := by
  unfold tailWord_2810193
  simp only [CollatzResearch.WordTrace]
  refine ⟨102496159108158178599315233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68330772738772119066210155 102496159108158178599315233)
  ·
    refine ⟨76872119331118633949486425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102496159108158178599315233 76872119331118633949486425)
    ·
      refine ⟨57654089498338975462114819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76872119331118633949486425 57654089498338975462114819)
      ·
        refine ⟨86481134247508463193172229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57654089498338975462114819 86481134247508463193172229)
        ·
          refine ⟨16215212671407836848719793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86481134247508463193172229 16215212671407836848719793)
          ·
            refine ⟨12161409503555877636539845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16215212671407836848719793 12161409503555877636539845)
            ·
              refine ⟨2280264281916727056851221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12161409503555877636539845 2280264281916727056851221)
              ·
                refine ⟨106887388214846580789901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2280264281916727056851221 106887388214846580789901)
                ·
                  rfl

theorem cell22_2810193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 6].length) (baseStart_2810193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810193 prefixEnd_2810193 := by exact prefixLift 2810193
  have htrace : WordTrace (prefixWord ++ tailWord_2810193) baseStart_2810193 baseEnd_2810193 := by
    simpa [prefixWord, tailWord_2810193, baseEnd_2810193] using wordTrace_append hprefix tailTrace_2810193
  have hstable : (prefixWord ++ tailWord_2810193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810193).length < 2 ^ (prefixWord ++ tailWord_2810193).sum := by decide
  have hdescent : baseEnd_2810193 < baseStart_2810193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810300 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 6]
def baseStart_2810300 : Nat := 118140960795 + 2810300 * 2 ^ 59
def prefixEnd_2810300 : Nat := 4983230072969 + 3 ^ 40 * 2810300 * 2
def baseEnd_2810300 : Nat := 320674374073435538227927

theorem tailTrace_2810300 : CollatzResearch.WordTrace tailWord_2810300 prefixEnd_2810300 320674374073435538227927 := by
  unfold tailWord_2810300
  simp only [CollatzResearch.WordTrace]
  refine ⟨51250030859385267936730177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68333374479180357248973569 51250030859385267936730177)
  ·
    refine ⟨38437523144538950952547633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51250030859385267936730177 38437523144538950952547633)
    ·
      refine ⟨28828142358404213214410725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38437523144538950952547633 28828142358404213214410725)
      ·
        refine ⟨5405276692200789977702011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28828142358404213214410725 5405276692200789977702011)
        ·
          refine ⟨8107915038301184966553017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5405276692200789977702011 8107915038301184966553017)
          ·
            refine ⟨6080936278725888724914763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8107915038301184966553017 6080936278725888724914763)
            ·
              refine ⟨9121404418088833087372145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6080936278725888724914763 9121404418088833087372145)
              ·
                refine ⟨6841053313566624815529109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9121404418088833087372145 6841053313566624815529109)
                ·
                  refine ⟨320674374073435538227927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6841053313566624815529109 320674374073435538227927)
                  ·
                    rfl

theorem cell22_2810300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_2810300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810300 prefixEnd_2810300 := by exact prefixLift 2810300
  have htrace : WordTrace (prefixWord ++ tailWord_2810300) baseStart_2810300 baseEnd_2810300 := by
    simpa [prefixWord, tailWord_2810300, baseEnd_2810300] using wordTrace_append hprefix tailTrace_2810300
  have hstable : (prefixWord ++ tailWord_2810300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810300).length < 2 ^ (prefixWord ++ tailWord_2810300).sum := by decide
  have hdescent : baseEnd_2810300 < baseStart_2810300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810360 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 3, 3]
def baseStart_2810360 : Nat := 118140960795 + 2810360 * 2 ^ 59
def prefixEnd_2810360 : Nat := 4983230072969 + 3 ^ 40 * 2810360 * 2
def baseEnd_2810360 : Nat := 962043661446486458183597

theorem tailTrace_2810360 : CollatzResearch.WordTrace tailWord_2810360 prefixEnd_2810360 962043661446486458183597 := by
  unfold tailWord_2810360
  simp only [CollatzResearch.WordTrace]
  refine ⟨51251125049276583060322267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68334833399035444080429689 51251125049276583060322267)
  ·
    refine ⟨76876687573914874590483401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51251125049276583060322267 76876687573914874590483401)
    ·
      refine ⟨57657515680436155942862551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76876687573914874590483401 57657515680436155942862551)
      ·
        refine ⟨86486273520654233914293827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57657515680436155942862551 86486273520654233914293827)
        ·
          refine ⟨129729410280981350871440741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86486273520654233914293827 129729410280981350871440741)
          ·
            refine ⟨24324264427684003288395139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129729410280981350871440741 24324264427684003288395139)
            ·
              refine ⟨36486396641526004932592709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24324264427684003288395139 36486396641526004932592709)
              ·
                refine ⟨6841199370286125924861133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36486396641526004932592709 6841199370286125924861133)
                ·
                  refine ⟨2565449763857297221822925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6841199370286125924861133 2565449763857297221822925)
                  ·
                    refine ⟨962043661446486458183597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2565449763857297221822925 962043661446486458183597)
                    ·
                      rfl

theorem cell22_2810360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_2810360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810360 prefixEnd_2810360 := by exact prefixLift 2810360
  have htrace : WordTrace (prefixWord ++ tailWord_2810360) baseStart_2810360 baseEnd_2810360 := by
    simpa [prefixWord, tailWord_2810360, baseEnd_2810360] using wordTrace_append hprefix tailTrace_2810360
  have hstable : (prefixWord ++ tailWord_2810360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810360).length < 2 ^ (prefixWord ++ tailWord_2810360).sum := by decide
  have hdescent : baseEnd_2810360 < baseStart_2810360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810373 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 7]
def baseStart_2810373 : Nat := 118140960795 + 2810373 * 2 ^ 59
def prefixEnd_2810373 : Nat := 4983230072969 + 3 ^ 40 * 2810373 * 2
def baseEnd_2810373 : Nat := 320682703870719585869519

theorem tailTrace_2810373 : CollatzResearch.WordTrace tailWord_2810373 prefixEnd_2810373 320682703870719585869519 := by
  unfold tailWord_2810373
  simp only [CollatzResearch.WordTrace]
  refine ⟨102502724247506069340867773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68335149498337379560578515 102502724247506069340867773)
  ·
    refine ⟨38438521592814776002825415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102502724247506069340867773 38438521592814776002825415)
    ·
      refine ⟨57657782389222164004238123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38438521592814776002825415 57657782389222164004238123)
      ·
        refine ⟨86486673583833246006357185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57657782389222164004238123 86486673583833246006357185)
        ·
          refine ⟨64865005187874934504767889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86486673583833246006357185 64865005187874934504767889)
          ·
            refine ⟨48648753890906200878575917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64865005187874934504767889 48648753890906200878575917)
            ·
              refine ⟨18243282709089825329465969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48648753890906200878575917 18243282709089825329465969)
              ·
                refine ⟨13682462031817368997099477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18243282709089825329465969 13682462031817368997099477)
                ·
                  refine ⟨320682703870719585869519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13682462031817368997099477 320682703870719585869519)
                  ·
                    rfl

theorem cell22_2810373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_2810373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810373 prefixEnd_2810373 := by exact prefixLift 2810373
  have htrace : WordTrace (prefixWord ++ tailWord_2810373) baseStart_2810373 baseEnd_2810373 := by
    simpa [prefixWord, tailWord_2810373, baseEnd_2810373] using wordTrace_append hprefix tailTrace_2810373
  have hstable : (prefixWord ++ tailWord_2810373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810373).length < 2 ^ (prefixWord ++ tailWord_2810373).sum := by decide
  have hdescent : baseEnd_2810373 < baseStart_2810373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810377 : List Nat := [1, 2, 1, 1, 3, 1, 2, 7, 1, 3]
def baseStart_2810377 : Nat := 118140960795 + 2810377 * 2 ^ 59
def prefixEnd_2810377 : Nat := 4983230072969 + 3 ^ 40 * 2810377 * 2
def baseEnd_2810377 : Nat := 962049480893904080508545

theorem tailTrace_2810377 : CollatzResearch.WordTrace tailWord_2810377 prefixEnd_2810377 962049480893904080508545 := by
  unfold tailWord_2810377
  simp only [CollatzResearch.WordTrace]
  refine ⟨102502870139491578024013385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68335246759661052016008923 102502870139491578024013385)
  ·
    refine ⟨76877152604618683518010039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102502870139491578024013385 76877152604618683518010039)
    ·
      refine ⟨115315728906928025277015059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76877152604618683518010039 115315728906928025277015059)
      ·
        refine ⟨172973593360392037915522589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115315728906928025277015059 172973593360392037915522589)
        ·
          refine ⟨64865097510147014218320971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172973593360392037915522589 64865097510147014218320971)
          ·
            refine ⟨97297646265220521327481457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64865097510147014218320971 97297646265220521327481457)
            ·
              refine ⟨72973234698915390995611093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97297646265220521327481457 72973234698915390995611093)
              ·
                refine ⟨1710310188255829476459635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 72973234698915390995611093 1710310188255829476459635)
                ·
                  refine ⟨2565465282383744214689453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710310188255829476459635 2565465282383744214689453)
                  ·
                    refine ⟨962049480893904080508545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2565465282383744214689453 962049480893904080508545)
                    ·
                      rfl

theorem cell22_2810377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 1, 3].length) (baseStart_2810377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810377 prefixEnd_2810377 := by exact prefixLift 2810377
  have htrace : WordTrace (prefixWord ++ tailWord_2810377) baseStart_2810377 baseEnd_2810377 := by
    simpa [prefixWord, tailWord_2810377, baseEnd_2810377] using wordTrace_append hprefix tailTrace_2810377
  have hstable : (prefixWord ++ tailWord_2810377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810377).length < 2 ^ (prefixWord ++ tailWord_2810377).sum := by decide
  have hdescent : baseEnd_2810377 < baseStart_2810377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810450 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_2810450 : Nat := 118140960795 + 2810450 * 2 ^ 59
def prefixEnd_2810450 : Nat := 4983230072969 + 3 ^ 40 * 2810450 * 2
def baseEnd_2810450 : Nat := 962074470285756223433321

theorem tailTrace_2810450 : CollatzResearch.WordTrace tailWord_2810450 prefixEnd_2810450 962074470285756223433321 := by
  unfold tailWord_2810450
  simp only [CollatzResearch.WordTrace]
  refine ⟨25626383167056777872855201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68337021778818074327613869 25626383167056777872855201)
  ·
    refine ⟨19219787375292583404641401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25626383167056777872855201 19219787375292583404641401)
    ·
      refine ⟨14414840531469437553481051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19219787375292583404641401 14414840531469437553481051)
      ·
        refine ⟨21622260797204156330221577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14414840531469437553481051 21622260797204156330221577)
        ·
          refine ⟨16216695597903117247666183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21622260797204156330221577 16216695597903117247666183)
          ·
            refine ⟨24325043396854675871499275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16216695597903117247666183 24325043396854675871499275)
            ·
              refine ⟨36487565095282013807248913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24325043396854675871499275 36487565095282013807248913)
              ·
                refine ⟨27365673821461510355436685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36487565095282013807248913 27365673821461510355436685)
                ·
                  refine ⟨10262127683048066383288757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27365673821461510355436685 10262127683048066383288757)
                  ·
                    refine ⟨962074470285756223433321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10262127683048066383288757 962074470285756223433321)
                    ·
                      rfl

theorem cell22_2810450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_2810450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810450 prefixEnd_2810450 := by exact prefixLift 2810450
  have htrace : WordTrace (prefixWord ++ tailWord_2810450) baseStart_2810450 baseEnd_2810450 := by
    simpa [prefixWord, tailWord_2810450, baseEnd_2810450] using wordTrace_append hprefix tailTrace_2810450
  have hstable : (prefixWord ++ tailWord_2810450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810450).length < 2 ^ (prefixWord ++ tailWord_2810450).sum := by decide
  have hdescent : baseEnd_2810450 < baseStart_2810450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
