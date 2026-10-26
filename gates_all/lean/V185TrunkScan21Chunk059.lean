import V185TrunkScan21Chunk058

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_714706 : List Nat := [3, 2, 2, 3, 2, 1, 2, 3, 3]
def baseStart_714706 : Nat := 118140960795 + 714706 * 2 ^ 59
def prefixEnd_714706 : Nat := 4983230072969 + 3 ^ 40 * 714706 * 2
def baseEnd_714706 : Nat := 163105646512171530305837

theorem tailTrace_714706 : CollatzResearch.WordTrace tailWord_714706 prefixEnd_714706 163105646512171530305837 := by
  unfold tailWord_714706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6516867337187424728012993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17378312899166465941367981 6516867337187424728012993)
  ·
    refine ⟨4887650502890568546009745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6516867337187424728012993 4887650502890568546009745)
    ·
      refine ⟨3665737877167926409507309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4887650502890568546009745 3665737877167926409507309)
      ·
        refine ⟨1374651703937972403565241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3665737877167926409507309 1374651703937972403565241)
        ·
          refine ⟨1030988777953479302673931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1374651703937972403565241 1030988777953479302673931)
          ·
            refine ⟨1546483166930218954010897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030988777953479302673931 1546483166930218954010897)
            ·
              refine ⟨1159862375197664215508173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1546483166930218954010897 1159862375197664215508173)
              ·
                refine ⟨434948390699124080815565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1159862375197664215508173 434948390699124080815565)
                ·
                  refine ⟨163105646512171530305837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 434948390699124080815565 163105646512171530305837)
                  ·
                    rfl

theorem cell21_714706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_714706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714706 prefixEnd_714706 := by exact prefixLift 714706
  have htrace : WordTrace (prefixWord ++ tailWord_714706) baseStart_714706 baseEnd_714706 := by
    simpa [prefixWord, tailWord_714706, baseEnd_714706] using wordTrace_append hprefix tailTrace_714706
  have hstable : (prefixWord ++ tailWord_714706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714706).length < 2 ^ (prefixWord ++ tailWord_714706).sum := by decide
  have hdescent : baseEnd_714706 < baseStart_714706 := by decide
  rcases family_descends (prefixWord ++ tailWord_714706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714717 : List Nat := [1, 4, 3, 1, 3, 1, 8]
def baseStart_714717 : Nat := 118140960795 + 714717 * 2 ^ 59
def prefixEnd_714717 : Nat := 4983230072969 + 3 ^ 40 * 714717 * 2
def baseEnd_714717 : Nat := 18123128540226439513609

theorem tailTrace_714717 : CollatzResearch.WordTrace tailWord_714717 prefixEnd_714717 18123128540226439513609 := by
  unfold tailWord_714717
  simp only [CollatzResearch.WordTrace]
  refine ⟨26067870551709847790702405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17378580367806565193801603 26067870551709847790702405)
  ·
    refine ⟨4887725728445596460756701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26067870551709847790702405 4887725728445596460756701)
    ·
      refine ⟨1832897148167098672783763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4887725728445596460756701 1832897148167098672783763)
      ·
        refine ⟨2749345722250648009175645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1832897148167098672783763 2749345722250648009175645)
        ·
          refine ⟨1031004645843993003440867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2749345722250648009175645 1031004645843993003440867)
          ·
            refine ⟨1546506968765989505161301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031004645843993003440867 1546506968765989505161301)
            ·
              refine ⟨18123128540226439513609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1546506968765989505161301 18123128540226439513609)
              ·
                rfl

theorem cell21_714717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 8].length) (baseStart_714717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714717 prefixEnd_714717 := by exact prefixLift 714717
  have htrace : WordTrace (prefixWord ++ tailWord_714717) baseStart_714717 baseEnd_714717 := by
    simpa [prefixWord, tailWord_714717, baseEnd_714717] using wordTrace_append hprefix tailTrace_714717
  have hstable : (prefixWord ++ tailWord_714717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714717).length < 2 ^ (prefixWord ++ tailWord_714717).sum := by decide
  have hdescent : baseEnd_714717 < baseStart_714717 := by decide
  rcases family_descends (prefixWord ++ tailWord_714717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714852 : List Nat := [2, 3, 1, 1, 2, 1, 5, 6]
def baseStart_714852 : Nat := 118140960795 + 714852 * 2 ^ 59
def prefixEnd_714852 : Nat := 4983230072969 + 3 ^ 40 * 714852 * 2
def baseEnd_714852 : Nat := 54379655233769240290735

theorem tailTrace_714852 : CollatzResearch.WordTrace tailWord_714852 prefixEnd_714852 54379655233769240290735 := by
  unfold tailWord_714852
  simp only [CollatzResearch.WordTrace]
  refine ⟨13036397203110382923433405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17381862937480510564577873 13036397203110382923433405)
  ·
    refine ⟨4888648951166393596287527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13036397203110382923433405 4888648951166393596287527)
    ·
      refine ⟨7332973426749590394431291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4888648951166393596287527 7332973426749590394431291)
      ·
        refine ⟨10999460140124385591646937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7332973426749590394431291 10999460140124385591646937)
        ·
          refine ⟨8249595105093289193735203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10999460140124385591646937 8249595105093289193735203)
          ·
            refine ⟨12374392657639933790602805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8249595105093289193735203 12374392657639933790602805)
            ·
              refine ⟨1160099311653743792869013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12374392657639933790602805 1160099311653743792869013)
              ·
                refine ⟨54379655233769240290735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1160099311653743792869013 54379655233769240290735)
                ·
                  rfl

theorem cell21_714852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 6].length) (baseStart_714852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714852 prefixEnd_714852 := by exact prefixLift 714852
  have htrace : WordTrace (prefixWord ++ tailWord_714852) baseStart_714852 baseEnd_714852 := by
    simpa [prefixWord, tailWord_714852, baseEnd_714852] using wordTrace_append hprefix tailTrace_714852
  have hstable : (prefixWord ++ tailWord_714852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714852).length < 2 ^ (prefixWord ++ tailWord_714852).sum := by decide
  have hdescent : baseEnd_714852 < baseStart_714852 := by decide
  rcases family_descends (prefixWord ++ tailWord_714852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714965 : List Nat := [1, 3, 2, 4, 3, 1, 2, 1, 4]
def baseStart_714965 : Nat := 118140960795 + 714965 * 2 ^ 59
def prefixEnd_714965 : Nat := 4983230072969 + 3 ^ 40 * 714965 * 2
def baseEnd_714965 : Nat := 163164753840844635488641

theorem tailTrace_714965 : CollatzResearch.WordTrace tailWord_714965 prefixEnd_714965 163164753840844635488641 := by
  unfold tailWord_714965
  simp only [CollatzResearch.WordTrace]
  refine ⟨26076915854811386145730349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17384610569874257430486899 26076915854811386145730349)
  ·
    refine ⟨9778843445554269804648881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26076915854811386145730349 9778843445554269804648881)
    ·
      refine ⟨7334132584165702353486661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9778843445554269804648881 7334132584165702353486661)
      ·
        refine ⟨1375149859531069191278749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7334132584165702353486661 1375149859531069191278749)
        ·
          refine ⟨515681197324150946729531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1375149859531069191278749 515681197324150946729531)
          ·
            refine ⟨773521795986226420094297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515681197324150946729531 773521795986226420094297)
            ·
              refine ⟨580141346989669815070723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 773521795986226420094297 580141346989669815070723)
              ·
                refine ⟨870212020484504722606085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580141346989669815070723 870212020484504722606085)
                ·
                  refine ⟨163164753840844635488641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 870212020484504722606085 163164753840844635488641)
                  ·
                    rfl

theorem cell21_714965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_714965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714965 prefixEnd_714965 := by exact prefixLift 714965
  have htrace : WordTrace (prefixWord ++ tailWord_714965) baseStart_714965 baseEnd_714965 := by
    simpa [prefixWord, tailWord_714965, baseEnd_714965] using wordTrace_append hprefix tailTrace_714965
  have hstable : (prefixWord ++ tailWord_714965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714965).length < 2 ^ (prefixWord ++ tailWord_714965).sum := by decide
  have hdescent : baseEnd_714965 < baseStart_714965 := by decide
  rcases family_descends (prefixWord ++ tailWord_714965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714987 : List Nat := [1, 1, 1, 1, 2, 5, 1, 9]
def baseStart_714987 : Nat := 118140960795 + 714987 * 2 ^ 59
def prefixEnd_714987 : Nat := 4983230072969 + 3 ^ 40 * 714987 * 2
def baseEnd_714987 : Nat := 54389924846859162040643

theorem tailTrace_714987 : CollatzResearch.WordTrace tailWord_714987 prefixEnd_714987 54389924846859162040643 := by
  unfold tailWord_714987
  simp only [CollatzResearch.WordTrace]
  refine ⟨26077718260731683903031215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17385145507154455935354143 26077718260731683903031215)
  ·
    refine ⟨39116577391097525854546823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26077718260731683903031215 39116577391097525854546823)
    ·
      refine ⟨58674866086646288781820235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39116577391097525854546823 58674866086646288781820235)
      ·
        refine ⟨88012299129969433172730353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58674866086646288781820235 88012299129969433172730353)
        ·
          refine ⟨66009224347477074879547765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88012299129969433172730353 66009224347477074879547765)
          ·
            refine ⟨6188364782575975769957603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66009224347477074879547765 6188364782575975769957603)
            ·
              refine ⟨9282547173863963654936405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6188364782575975769957603 9282547173863963654936405)
              ·
                refine ⟨54389924846859162040643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9282547173863963654936405 54389924846859162040643)
                ·
                  rfl

theorem cell21_714987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 9].length) (baseStart_714987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714987 prefixEnd_714987 := by exact prefixLift 714987
  have htrace : WordTrace (prefixWord ++ tailWord_714987) baseStart_714987 baseEnd_714987 := by
    simpa [prefixWord, tailWord_714987, baseEnd_714987] using wordTrace_append hprefix tailTrace_714987
  have hstable : (prefixWord ++ tailWord_714987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714987).length < 2 ^ (prefixWord ++ tailWord_714987).sum := by decide
  have hdescent : baseEnd_714987 < baseStart_714987 := by decide
  rcases family_descends (prefixWord ++ tailWord_714987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715010 : List Nat := [3, 4, 1, 1, 2, 1, 4, 2, 3]
def baseStart_715010 : Nat := 118140960795 + 715010 * 2 ^ 59
def prefixEnd_715010 : Nat := 4983230072969 + 3 ^ 40 * 715010 * 2
def baseEnd_715010 : Nat := 163175023453934557238549

theorem tailTrace_715010 : CollatzResearch.WordTrace tailWord_715010 prefixEnd_715010 163175023453934557238549 := by
  unfold tailWord_715010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6519639284912089707779621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17385704759765572554078989 6519639284912089707779621)
  ·
    refine ⟨1222432365921016820208679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6519639284912089707779621 1222432365921016820208679)
    ·
      refine ⟨1833648548881525230313019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1222432365921016820208679 1833648548881525230313019)
      ·
        refine ⟨2750472823322287845469529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1833648548881525230313019 2750472823322287845469529)
        ·
          refine ⟨2062854617491715884102147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2750472823322287845469529 2062854617491715884102147)
          ·
            refine ⟨3094281926237573826153221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2062854617491715884102147 3094281926237573826153221)
            ·
              refine ⟨580177861169545092403729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3094281926237573826153221 580177861169545092403729)
              ·
                refine ⟨435133395877158819302797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 580177861169545092403729 435133395877158819302797)
                ·
                  refine ⟨163175023453934557238549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 435133395877158819302797 163175023453934557238549)
                  ·
                    rfl

theorem cell21_715010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_715010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715010 prefixEnd_715010 := by exact prefixLift 715010
  have htrace : WordTrace (prefixWord ++ tailWord_715010) baseStart_715010 baseEnd_715010 := by
    simpa [prefixWord, tailWord_715010, baseEnd_715010] using wordTrace_append hprefix tailTrace_715010
  have hstable : (prefixWord ++ tailWord_715010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715010).length < 2 ^ (prefixWord ++ tailWord_715010).sum := by decide
  have hdescent : baseEnd_715010 < baseStart_715010 := by decide
  rcases family_descends (prefixWord ++ tailWord_715010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715066 : List Nat := [3, 1, 1, 1, 4, 2, 3, 2, 4]
def baseStart_715066 : Nat := 118140960795 + 715066 * 2 ^ 59
def prefixEnd_715066 : Nat := 4983230072969 + 3 ^ 40 * 715066 * 2
def baseEnd_715066 : Nat := 163187803416890904305101

theorem tailTrace_715066 : CollatzResearch.WordTrace tailWord_715066 prefixEnd_715066 163187803416890904305101 := by
  unfold tailWord_715066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6520149906861370098789263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17387066418296986930104701 6520149906861370098789263)
  ·
    refine ⟨9780224860292055148183895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6520149906861370098789263 9780224860292055148183895)
    ·
      refine ⟨14670337290438082722275843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9780224860292055148183895 14670337290438082722275843)
      ·
        refine ⟨22005505935657124083413765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14670337290438082722275843 22005505935657124083413765)
        ·
          refine ⟨4126032362935710765640081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22005505935657124083413765 4126032362935710765640081)
          ·
            refine ⟨3094524272201783074230061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4126032362935710765640081 3094524272201783074230061)
            ·
              refine ⟨1160446602075668652836273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3094524272201783074230061 1160446602075668652836273)
              ·
                refine ⟨870334951556751489627205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1160446602075668652836273 870334951556751489627205)
                ·
                  refine ⟨163187803416890904305101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 870334951556751489627205 163187803416890904305101)
                  ·
                    rfl

theorem cell21_715066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_715066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715066 prefixEnd_715066 := by exact prefixLift 715066
  have htrace : WordTrace (prefixWord ++ tailWord_715066) baseStart_715066 baseEnd_715066 := by
    simpa [prefixWord, tailWord_715066, baseEnd_715066] using wordTrace_append hprefix tailTrace_715066
  have hstable : (prefixWord ++ tailWord_715066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715066).length < 2 ^ (prefixWord ++ tailWord_715066).sum := by decide
  have hdescent : baseEnd_715066 < baseStart_715066 := by decide
  rcases family_descends (prefixWord ++ tailWord_715066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715184 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 10]
def baseStart_715184 : Nat := 118140960795 + 715184 * 2 ^ 59
def prefixEnd_715184 : Nat := 4983230072969 + 3 ^ 40 * 715184 * 2
def baseEnd_715184 : Nat := 163214732624548921338193

theorem tailTrace_715184 : CollatzResearch.WordTrace tailWord_715184 prefixEnd_715184 163214732624548921338193 := by
  unfold tailWord_715184
  simp only [CollatzResearch.WordTrace]
  refine ⟨13042451720508993273976303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17389935627345324365301737 13042451720508993273976303)
  ·
    refine ⟨19563677580763489910964455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13042451720508993273976303 19563677580763489910964455)
    ·
      refine ⟨29345516371145234866446683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19563677580763489910964455 29345516371145234866446683)
      ·
        refine ⟨44018274556717852299670025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29345516371145234866446683 44018274556717852299670025)
        ·
          refine ⟨33013705917538389224752519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44018274556717852299670025 33013705917538389224752519)
          ·
            refine ⟨49520558876307583837128779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33013705917538389224752519 49520558876307583837128779)
            ·
              refine ⟨74280838314461375755693169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49520558876307583837128779 74280838314461375755693169)
              ·
                refine ⟨55710628735846031816769877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74280838314461375755693169 55710628735846031816769877)
                ·
                  refine ⟨163214732624548921338193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 55710628735846031816769877 163214732624548921338193)
                  ·
                    rfl

theorem cell21_715184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_715184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715184 prefixEnd_715184 := by exact prefixLift 715184
  have htrace : WordTrace (prefixWord ++ tailWord_715184) baseStart_715184 baseEnd_715184 := by
    simpa [prefixWord, tailWord_715184, baseEnd_715184] using wordTrace_append hprefix tailTrace_715184
  have hstable : (prefixWord ++ tailWord_715184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715184).length < 2 ^ (prefixWord ++ tailWord_715184).sum := by decide
  have hdescent : baseEnd_715184 < baseStart_715184 := by decide
  rcases family_descends (prefixWord ++ tailWord_715184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715204 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 5]
def baseStart_715204 : Nat := 118140960795 + 715204 * 2 ^ 59
def prefixEnd_715204 : Nat := 4983230072969 + 3 ^ 40 * 715204 * 2
def baseEnd_715204 : Nat := 163219296897033331004819

theorem tailTrace_715204 : CollatzResearch.WordTrace tailWord_715204 prefixEnd_715204 163219296897033331004819 := by
  unfold tailWord_715204
  simp only [CollatzResearch.WordTrace]
  refine ⟨13042816450472764981840333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17390421933963686642453777 13042816450472764981840333)
  ·
    refine ⟨4891056168927286868190125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13042816450472764981840333 4891056168927286868190125)
    ·
      refine ⟨1834146063347732575571297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4891056168927286868190125 1834146063347732575571297)
      ·
        refine ⟨1375609547510799431678473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1834146063347732575571297 1375609547510799431678473)
        ·
          refine ⟨1031707160633099573758855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1375609547510799431678473 1031707160633099573758855)
          ·
            refine ⟨1547560740949649360638283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031707160633099573758855 1547560740949649360638283)
            ·
              refine ⟨2321341111424474040957425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547560740949649360638283 2321341111424474040957425)
              ·
                refine ⟨1741005833568355530718069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2321341111424474040957425 1741005833568355530718069)
                ·
                  refine ⟨163219296897033331004819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1741005833568355530718069 163219296897033331004819)
                  ·
                    rfl

theorem cell21_715204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_715204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715204 prefixEnd_715204 := by exact prefixLift 715204
  have htrace : WordTrace (prefixWord ++ tailWord_715204) baseStart_715204 baseEnd_715204 := by
    simpa [prefixWord, tailWord_715204, baseEnd_715204] using wordTrace_append hprefix tailTrace_715204
  have hstable : (prefixWord ++ tailWord_715204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715204).length < 2 ^ (prefixWord ++ tailWord_715204).sum := by decide
  have hdescent : baseEnd_715204 < baseStart_715204 := by decide
  rcases family_descends (prefixWord ++ tailWord_715204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715235 : List Nat := [1, 1, 1, 6, 3, 2, 1, 2, 4]
def baseStart_715235 : Nat := 118140960795 + 715235 * 2 ^ 59
def prefixEnd_715235 : Nat := 4983230072969 + 3 ^ 40 * 715235 * 2
def baseEnd_715235 : Nat := 163226371519384165988089

theorem tailTrace_715235 : CollatzResearch.WordTrace tailWord_715235 prefixEnd_715235 163226371519384165988089 := by
  unfold tailWord_715235
  simp only [CollatzResearch.WordTrace]
  refine ⟨26086763563833222258059159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17391175709222148172039439 26086763563833222258059159)
  ·
    refine ⟨39130145345749833387088739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26086763563833222258059159 39130145345749833387088739)
    ·
      refine ⟨58695218018624750080633109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39130145345749833387088739 58695218018624750080633109)
      ·
        refine ⟨2751338344623035160029677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58695218018624750080633109 2751338344623035160029677)
        ·
          refine ⟨1031751879233638185011129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2751338344623035160029677 1031751879233638185011129)
          ·
            refine ⟨773813909425228638758347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1031751879233638185011129 773813909425228638758347)
            ·
              refine ⟨1160720864137842958137521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773813909425228638758347 1160720864137842958137521)
              ·
                refine ⟨870540648103382218603141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1160720864137842958137521 870540648103382218603141)
                ·
                  refine ⟨163226371519384165988089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 870540648103382218603141 163226371519384165988089)
                  ·
                    rfl

theorem cell21_715235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 4].length) (baseStart_715235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715235 prefixEnd_715235 := by exact prefixLift 715235
  have htrace : WordTrace (prefixWord ++ tailWord_715235) baseStart_715235 baseEnd_715235 := by
    simpa [prefixWord, tailWord_715235, baseEnd_715235] using wordTrace_append hprefix tailTrace_715235
  have hstable : (prefixWord ++ tailWord_715235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715235).length < 2 ^ (prefixWord ++ tailWord_715235).sum := by decide
  have hdescent : baseEnd_715235 < baseStart_715235 := by decide
  rcases family_descends (prefixWord ++ tailWord_715235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715336 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 8]
def baseStart_715336 : Nat := 118140960795 + 715336 * 2 ^ 59
def prefixEnd_715336 : Nat := 4983230072969 + 3 ^ 40 * 715336 * 2
def baseEnd_715336 : Nat := 163249421095430434804549

theorem tailTrace_715336 : CollatzResearch.WordTrace tailWord_715336 prefixEnd_715336 163249421095430434804549 := by
  unfold tailWord_715336
  simp only [CollatzResearch.WordTrace]
  refine ⟨13045223668233658253742931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17393631557644877671657241 13045223668233658253742931)
  ·
    refine ⟨19567835502350487380614397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13045223668233658253742931 19567835502350487380614397)
    ·
      refine ⟨7337938313381432767730399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19567835502350487380614397 7337938313381432767730399)
      ·
        refine ⟨11006907470072149151595599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7337938313381432767730399 11006907470072149151595599)
        ·
          refine ⟨16510361205108223727393399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11006907470072149151595599 16510361205108223727393399)
          ·
            refine ⟨24765541807662335591090099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16510361205108223727393399 24765541807662335591090099)
            ·
              refine ⟨37148312711493503386635149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24765541807662335591090099 37148312711493503386635149)
              ·
                refine ⟨13930617266810063769988181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37148312711493503386635149 13930617266810063769988181)
                ·
                  refine ⟨163249421095430434804549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13930617266810063769988181 163249421095430434804549)
                  ·
                    rfl

theorem cell21_715336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_715336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715336 prefixEnd_715336 := by exact prefixLift 715336
  have htrace : WordTrace (prefixWord ++ tailWord_715336) baseStart_715336 baseEnd_715336 := by
    simpa [prefixWord, tailWord_715336, baseEnd_715336] using wordTrace_append hprefix tailTrace_715336
  have hstable : (prefixWord ++ tailWord_715336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715336).length < 2 ^ (prefixWord ++ tailWord_715336).sum := by decide
  have hdescent : baseEnd_715336 < baseStart_715336 := by decide
  rcases family_descends (prefixWord ++ tailWord_715336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715415 : List Nat := [1, 1, 3, 3, 2, 1, 1, 6, 3]
def baseStart_715415 : Nat := 118140960795 + 715415 * 2 ^ 59
def prefixEnd_715415 : Nat := 4983230072969 + 3 ^ 40 * 715415 * 2
def baseEnd_715415 : Nat := 163267449971743852987721

theorem tailTrace_715415 : CollatzResearch.WordTrace tailWord_715415 prefixEnd_715415 163267449971743852987721 := by
  unfold tailWord_715415
  simp only [CollatzResearch.WordTrace]
  refine ⟨26093328703181112999611699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17395552468787408666407799 26093328703181112999611699)
  ·
    refine ⟨39139993054771669499417549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26093328703181112999611699 39139993054771669499417549)
    ·
      refine ⟨14677497395539376062281581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39139993054771669499417549 14677497395539376062281581)
      ·
        refine ⟨5504061523327266023355593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14677497395539376062281581 5504061523327266023355593)
        ·
          refine ⟨4128046142495449517516695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5504061523327266023355593 4128046142495449517516695)
          ·
            refine ⟨6192069213743174276275043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4128046142495449517516695 6192069213743174276275043)
            ·
              refine ⟨9288103820614761414412565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6192069213743174276275043 9288103820614761414412565)
              ·
                refine ⟨435379866591316941300589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9288103820614761414412565 435379866591316941300589)
                ·
                  refine ⟨163267449971743852987721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 435379866591316941300589 163267449971743852987721)
                  ·
                    rfl

theorem cell21_715415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 3].length) (baseStart_715415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715415 prefixEnd_715415 := by exact prefixLift 715415
  have htrace : WordTrace (prefixWord ++ tailWord_715415) baseStart_715415 baseEnd_715415 := by
    simpa [prefixWord, tailWord_715415, baseEnd_715415] using wordTrace_append hprefix tailTrace_715415
  have hstable : (prefixWord ++ tailWord_715415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715415).length < 2 ^ (prefixWord ++ tailWord_715415).sum := by decide
  have hdescent : baseEnd_715415 < baseStart_715415 := by decide
  rcases family_descends (prefixWord ++ tailWord_715415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715443 : List Nat := [1, 1, 1, 2, 3, 5, 1, 7]
def baseStart_715443 : Nat := 118140960795 + 715443 * 2 ^ 59
def prefixEnd_715443 : Nat := 4983230072969 + 3 ^ 40 * 715443 * 2
def baseEnd_715443 : Nat := 54424613317740675506999

theorem tailTrace_715443 : CollatzResearch.WordTrace tailWord_715443 prefixEnd_715443 54424613317740675506999 := by
  unfold tailWord_715443
  simp only [CollatzResearch.WordTrace]
  refine ⟨26094349947079673781630983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17396233298053115854420655 26094349947079673781630983)
  ·
    refine ⟨39141524920619510672446475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26094349947079673781630983 39141524920619510672446475)
    ·
      refine ⟨58712287380929266008669713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39141524920619510672446475 58712287380929266008669713)
      ·
        refine ⟨44034215535696949506502285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58712287380929266008669713 44034215535696949506502285)
        ·
          refine ⟨16512830825886356064938357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44034215535696949506502285 16512830825886356064938357)
          ·
            refine ⟨1548077889926845881087971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16512830825886356064938357 1548077889926845881087971)
            ·
              refine ⟨2322116834890268821631957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548077889926845881087971 2322116834890268821631957)
              ·
                refine ⟨54424613317740675506999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2322116834890268821631957 54424613317740675506999)
                ·
                  rfl

theorem cell21_715443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 7].length) (baseStart_715443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715443 prefixEnd_715443 := by exact prefixLift 715443
  have htrace : WordTrace (prefixWord ++ tailWord_715443) baseStart_715443 baseEnd_715443 := by
    simpa [prefixWord, tailWord_715443, baseEnd_715443] using wordTrace_append hprefix tailTrace_715443
  have hstable : (prefixWord ++ tailWord_715443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715443).length < 2 ^ (prefixWord ++ tailWord_715443).sum := by decide
  have hdescent : baseEnd_715443 < baseStart_715443 := by decide
  rcases family_descends (prefixWord ++ tailWord_715443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715460 : List Nat := [2, 3, 3, 1, 1, 4, 7]
def baseStart_715460 : Nat := 118140960795 + 715460 * 2 ^ 59
def prefixEnd_715460 : Nat := 4983230072969 + 3 ^ 40 * 715460 * 2
def baseEnd_715460 : Nat := 18141968842759308304181

theorem tailTrace_715460 : CollatzResearch.WordTrace tailWord_715460 prefixEnd_715460 18141968842759308304181 := by
  unfold tailWord_715460
  simp only [CollatzResearch.WordTrace]
  refine ⟨13047484994009042842499917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17396646658678723789999889 13047484994009042842499917)
  ·
    refine ⟨4892806872753391065937469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13047484994009042842499917 4892806872753391065937469)
    ·
      refine ⟨1834802577282521649726551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4892806872753391065937469 1834802577282521649726551)
      ·
        refine ⟨2752203865923782474589827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1834802577282521649726551 2752203865923782474589827)
        ·
          refine ⟨4128305798885673711884741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2752203865923782474589827 4128305798885673711884741)
          ·
            refine ⟨774057337291063820978389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4128305798885673711884741 774057337291063820978389)
            ·
              refine ⟨18141968842759308304181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 774057337291063820978389 18141968842759308304181)
              ·
                rfl

theorem cell21_715460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 7].length) (baseStart_715460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715460 prefixEnd_715460 := by exact prefixLift 715460
  have htrace : WordTrace (prefixWord ++ tailWord_715460) baseStart_715460 baseEnd_715460 := by
    simpa [prefixWord, tailWord_715460, baseEnd_715460] using wordTrace_append hprefix tailTrace_715460
  have hstable : (prefixWord ++ tailWord_715460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715460).length < 2 ^ (prefixWord ++ tailWord_715460).sum := by decide
  have hdescent : baseEnd_715460 < baseStart_715460 := by decide
  rcases family_descends (prefixWord ++ tailWord_715460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715477 : List Nat := [1, 3, 2, 5, 1, 1, 2, 6]
def baseStart_715477 : Nat := 118140960795 + 715477 * 2 ^ 59
def prefixEnd_715477 : Nat := 4983230072969 + 3 ^ 40 * 715477 * 2
def baseEnd_715477 : Nat := 54427199738815174318087

theorem tailTrace_715477 : CollatzResearch.WordTrace tailWord_715477 prefixEnd_715477 54427199738815174318087 := by
  unfold tailWord_715477
  simp only [CollatzResearch.WordTrace]
  refine ⟨26095590028956497588368685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17397060019304331725579123 26095590028956497588368685)
  ·
    refine ⟨9785846260858686595638257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26095590028956497588368685 9785846260858686595638257)
    ·
      refine ⟨7339384695644014946728693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9785846260858686595638257 7339384695644014946728693)
      ·
        refine ⟨688067315216626401255815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7339384695644014946728693 688067315216626401255815)
        ·
          refine ⟨1032100972824939601883723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688067315216626401255815 1032100972824939601883723)
          ·
            refine ⟨1548151459237409402825585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032100972824939601883723 1548151459237409402825585)
            ·
              refine ⟨1161113594428057052119189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1548151459237409402825585 1161113594428057052119189)
              ·
                refine ⟨54427199738815174318087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1161113594428057052119189 54427199738815174318087)
                ·
                  rfl

theorem cell21_715477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 6].length) (baseStart_715477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715477 prefixEnd_715477 := by exact prefixLift 715477
  have htrace : WordTrace (prefixWord ++ tailWord_715477) baseStart_715477 baseEnd_715477 := by
    simpa [prefixWord, tailWord_715477, baseEnd_715477] using wordTrace_append hprefix tailTrace_715477
  have hstable : (prefixWord ++ tailWord_715477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715477).length < 2 ^ (prefixWord ++ tailWord_715477).sum := by decide
  have hdescent : baseEnd_715477 < baseStart_715477 := by decide
  rcases family_descends (prefixWord ++ tailWord_715477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715522 : List Nat := [3, 4, 1, 1, 1, 2, 1, 4, 4]
def baseStart_715522 : Nat := 118140960795 + 715522 * 2 ^ 59
def prefixEnd_715522 : Nat := 4983230072969 + 3 ^ 40 * 715522 * 2
def baseEnd_715522 : Nat := 163291868829535444704169

theorem tailTrace_715522 : CollatzResearch.WordTrace tailWord_715522 prefixEnd_715522 163291868829535444704169 := by
  unfold tailWord_715522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6524307828448367568439205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17398154209195646849171213 6524307828448367568439205)
  ·
    refine ⟨1223307717834068919082351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6524307828448367568439205 1223307717834068919082351)
    ·
      refine ⟨1834961576751103378623527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1223307717834068919082351 1834961576751103378623527)
      ·
        refine ⟨2752442365126655067935291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1834961576751103378623527 2752442365126655067935291)
        ·
          refine ⟨4128663547689982601902937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2752442365126655067935291 4128663547689982601902937)
          ·
            refine ⟨3096497660767486951427203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4128663547689982601902937 3096497660767486951427203)
            ·
              refine ⟨4644746491151230427140805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3096497660767486951427203 4644746491151230427140805)
              ·
                refine ⟨870889967090855705088901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4644746491151230427140805 870889967090855705088901)
                ·
                  refine ⟨163291868829535444704169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 870889967090855705088901 163291868829535444704169)
                  ·
                    rfl

theorem cell21_715522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_715522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715522 prefixEnd_715522 := by exact prefixLift 715522
  have htrace : WordTrace (prefixWord ++ tailWord_715522) baseStart_715522 baseEnd_715522 := by
    simpa [prefixWord, tailWord_715522, baseEnd_715522] using wordTrace_append hprefix tailTrace_715522
  have hstable : (prefixWord ++ tailWord_715522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715522).length < 2 ^ (prefixWord ++ tailWord_715522).sum := by decide
  have hdescent : baseEnd_715522 < baseStart_715522 := by decide
  rcases family_descends (prefixWord ++ tailWord_715522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715564 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 6]
def baseStart_715564 : Nat := 118140960795 + 715564 * 2 ^ 59
def prefixEnd_715564 : Nat := 4983230072969 + 3 ^ 40 * 715564 * 2
def baseEnd_715564 : Nat := 163301453801752705004083

theorem tailTrace_715564 : CollatzResearch.WordTrace tailWord_715564 prefixEnd_715564 163301453801752705004083 := by
  unfold tailWord_715564
  simp only [CollatzResearch.WordTrace]
  refine ⟨13049381589820655723392873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17399175453094207631190497 13049381589820655723392873)
  ·
    refine ⟨9787036192365491792544655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13049381589820655723392873 9787036192365491792544655)
    ·
      refine ⟨14680554288548237688816983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9787036192365491792544655 14680554288548237688816983)
      ·
        refine ⟨22020831432822356533225475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14680554288548237688816983 22020831432822356533225475)
        ·
          refine ⟨33031247149233534799838213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22020831432822356533225475 33031247149233534799838213)
          ·
            refine ⟨6193358840481287774969665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33031247149233534799838213 6193358840481287774969665)
            ·
              refine ⟨4645019130360965831227249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6193358840481287774969665 4645019130360965831227249)
              ·
                refine ⟨3483764347770724373420437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4645019130360965831227249 3483764347770724373420437)
                ·
                  refine ⟨163301453801752705004083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3483764347770724373420437 163301453801752705004083)
                  ·
                    rfl

theorem cell21_715564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_715564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715564 prefixEnd_715564 := by exact prefixLift 715564
  have htrace : WordTrace (prefixWord ++ tailWord_715564) baseStart_715564 baseEnd_715564 := by
    simpa [prefixWord, tailWord_715564, baseEnd_715564] using wordTrace_append hprefix tailTrace_715564
  have hstable : (prefixWord ++ tailWord_715564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715564).length < 2 ^ (prefixWord ++ tailWord_715564).sum := by decide
  have hdescent : baseEnd_715564 < baseStart_715564 := by decide
  rcases family_descends (prefixWord ++ tailWord_715564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715612 : List Nat := [2, 2, 4, 2, 1, 2, 1, 7]
def baseStart_715612 : Nat := 118140960795 + 715612 * 2 ^ 59
def prefixEnd_715612 : Nat := 4983230072969 + 3 ^ 40 * 715612 * 2
def baseEnd_715612 : Nat := 54437469351905096067995

theorem tailTrace_715612 : CollatzResearch.WordTrace tailWord_715612 prefixEnd_715612 54437469351905096067995 := by
  unfold tailWord_715612
  simp only [CollatzResearch.WordTrace]
  refine ⟨13050256941733707822266545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17400342588978277096355393 13050256941733707822266545)
  ·
    refine ⟨9787692706300280866699909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13050256941733707822266545 9787692706300280866699909)
    ·
      refine ⟨1835192382431302662506233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9787692706300280866699909 1835192382431302662506233)
      ·
        refine ⟨1376394286823476996879675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1835192382431302662506233 1376394286823476996879675)
        ·
          refine ⟨2064591430235215495319513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1376394286823476996879675 2064591430235215495319513)
          ·
            refine ⟨1548443572676411621489635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2064591430235215495319513 1548443572676411621489635)
            ·
              refine ⟨2322665359014617432234453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548443572676411621489635 2322665359014617432234453)
              ·
                refine ⟨54437469351905096067995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2322665359014617432234453 54437469351905096067995)
                ·
                  rfl

theorem cell21_715612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 7].length) (baseStart_715612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715612 prefixEnd_715612 := by exact prefixLift 715612
  have htrace : WordTrace (prefixWord ++ tailWord_715612) baseStart_715612 baseEnd_715612 := by
    simpa [prefixWord, tailWord_715612, baseEnd_715612] using wordTrace_append hprefix tailTrace_715612
  have hstable : (prefixWord ++ tailWord_715612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715612).length < 2 ^ (prefixWord ++ tailWord_715612).sum := by decide
  have hdescent : baseEnd_715612 < baseStart_715612 := by decide
  rcases family_descends (prefixWord ++ tailWord_715612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715618 : List Nat := [3, 3, 2, 1, 4, 1, 1, 3, 3]
def baseStart_715618 : Nat := 118140960795 + 715618 * 2 ^ 59
def prefixEnd_715618 : Nat := 4983230072969 + 3 ^ 40 * 715618 * 2
def baseEnd_715618 : Nat := 163313777337460611103973

theorem tailTrace_715618 : CollatzResearch.WordTrace tailWord_715618 prefixEnd_715618 163313777337460611103973 := by
  unfold tailWord_715618
  simp only [CollatzResearch.WordTrace]
  refine ⟨6525183180361419667312877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17400488480963785779501005 6525183180361419667312877)
  ·
    refine ⟨2446943692635532375242329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6525183180361419667312877 2446943692635532375242329)
    ·
      refine ⟨1835207769476649281431747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2446943692635532375242329 1835207769476649281431747)
      ·
        refine ⟨2752811654214973922147621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1835207769476649281431747 2752811654214973922147621)
        ·
          refine ⟨516152185165307610402679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2752811654214973922147621 516152185165307610402679)
          ·
            refine ⟨774228277747961415604019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516152185165307610402679 774228277747961415604019)
            ·
              refine ⟨1161342416621942123406029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774228277747961415604019 1161342416621942123406029)
              ·
                refine ⟨435503406233228296277261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1161342416621942123406029 435503406233228296277261)
                ·
                  refine ⟨163313777337460611103973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 435503406233228296277261 163313777337460611103973)
                  ·
                    rfl

theorem cell21_715618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_715618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715618 prefixEnd_715618 := by exact prefixLift 715618
  have htrace : WordTrace (prefixWord ++ tailWord_715618) baseStart_715618 baseEnd_715618 := by
    simpa [prefixWord, tailWord_715618, baseEnd_715618] using wordTrace_append hprefix tailTrace_715618
  have hstable : (prefixWord ++ tailWord_715618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715618).length < 2 ^ (prefixWord ++ tailWord_715618).sum := by decide
  have hdescent : baseEnd_715618 < baseStart_715618 := by decide
  rcases family_descends (prefixWord ++ tailWord_715618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715657 : List Nat := [1, 2, 1, 1, 5, 3, 1, 3, 4]
def baseStart_715657 : Nat := 118140960795 + 715657 * 2 ^ 59
def prefixEnd_715657 : Nat := 4983230072969 + 3 ^ 40 * 715657 * 2
def baseEnd_715657 : Nat := 163322677668805209953893

theorem tailTrace_715657 : CollatzResearch.WordTrace tailWord_715657 prefixEnd_715657 163322677668805209953893 := by
  unfold tailWord_715657
  simp only [CollatzResearch.WordTrace]
  refine ⟨26102155168304388329921225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17401436778869592219947483 26102155168304388329921225)
  ·
    refine ⟨19576616376228291247440919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26102155168304388329921225 19576616376228291247440919)
    ·
      refine ⟨29364924564342436871161379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19576616376228291247440919 29364924564342436871161379)
      ·
        refine ⟨44047386846513655306742069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29364924564342436871161379 44047386846513655306742069)
        ·
          refine ⟨4129442516860655185007069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44047386846513655306742069 4129442516860655185007069)
          ·
            refine ⟨1548540943822745694377651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4129442516860655185007069 1548540943822745694377651)
            ·
              refine ⟨2322811415734118541566477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548540943822745694377651 2322811415734118541566477)
              ·
                refine ⟨871054280900294453087429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2322811415734118541566477 871054280900294453087429)
                ·
                  refine ⟨163322677668805209953893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 871054280900294453087429 163322677668805209953893)
                  ·
                    rfl

theorem cell21_715657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_715657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715657 prefixEnd_715657 := by exact prefixLift 715657
  have htrace : WordTrace (prefixWord ++ tailWord_715657) baseStart_715657 baseEnd_715657 := by
    simpa [prefixWord, tailWord_715657, baseEnd_715657] using wordTrace_append hprefix tailTrace_715657
  have hstable : (prefixWord ++ tailWord_715657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715657).length < 2 ^ (prefixWord ++ tailWord_715657).sum := by decide
  have hdescent : baseEnd_715657 < baseStart_715657 := by decide
  rcases family_descends (prefixWord ++ tailWord_715657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715885 : List Nat := [1, 5, 1, 1, 2, 2, 2, 3, 4]
def baseStart_715885 : Nat := 118140960795 + 715885 * 2 ^ 59
def prefixEnd_715885 : Nat := 4983230072969 + 3 ^ 40 * 715885 * 2
def baseEnd_715885 : Nat := 163374710375127480153427

theorem tailTrace_715885 : CollatzResearch.WordTrace tailWord_715885 prefixEnd_715885 163374710375127480153427 := by
  unfold tailWord_715885
  simp only [CollatzResearch.WordTrace]
  refine ⟨26110471011478383269221109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17406980674318922179480739 26110471011478383269221109)
  ·
    refine ⟨2447856657326098431489479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26110471011478383269221109 2447856657326098431489479)
    ·
      refine ⟨3671784985989147647234219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2447856657326098431489479 3671784985989147647234219)
      ·
        refine ⟨5507677478983721470851329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3671784985989147647234219 5507677478983721470851329)
        ·
          refine ⟨4130758109237791103138497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5507677478983721470851329 4130758109237791103138497)
          ·
            refine ⟨3098068581928343327353873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4130758109237791103138497 3098068581928343327353873)
            ·
              refine ⟨2323551436446257495515405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3098068581928343327353873 2323551436446257495515405)
              ·
                refine ⟨871331788667346560818277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2323551436446257495515405 871331788667346560818277)
                ·
                  refine ⟨163374710375127480153427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 871331788667346560818277 163374710375127480153427)
                  ·
                    rfl

theorem cell21_715885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_715885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715885 prefixEnd_715885 := by exact prefixLift 715885
  have htrace : WordTrace (prefixWord ++ tailWord_715885) baseStart_715885 baseEnd_715885 := by
    simpa [prefixWord, tailWord_715885, baseEnd_715885] using wordTrace_append hprefix tailTrace_715885
  have hstable : (prefixWord ++ tailWord_715885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715885).length < 2 ^ (prefixWord ++ tailWord_715885).sum := by decide
  have hdescent : baseEnd_715885 < baseStart_715885 := by decide
  rcases family_descends (prefixWord ++ tailWord_715885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715930 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 5]
def baseStart_715930 : Nat := 118140960795 + 715930 * 2 ^ 59
def prefixEnd_715930 : Nat := 4983230072969 + 3 ^ 40 * 715930 * 2
def baseEnd_715930 : Nat := 163384979988217401903335

theorem tailTrace_715930 : CollatzResearch.WordTrace tailWord_715930 prefixEnd_715930 163384979988217401903335 := by
  unfold tailWord_715930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6528028074078838988652311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17408074864210237303072829 6528028074078838988652311)
  ·
    refine ⟨9792042111118258482978467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6528028074078838988652311 9792042111118258482978467)
    ·
      refine ⟨14688063166677387724467701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9792042111118258482978467 14688063166677387724467701)
      ·
        refine ⟨1377005921876005099168847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14688063166677387724467701 1377005921876005099168847)
        ·
          refine ⟨2065508882814007648753271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1377005921876005099168847 2065508882814007648753271)
          ·
            refine ⟨3098263324221011473129907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2065508882814007648753271 3098263324221011473129907)
            ·
              refine ⟨4647394986331517209694861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3098263324221011473129907 4647394986331517209694861)
              ·
                refine ⟨1742773119874318953635573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4647394986331517209694861 1742773119874318953635573)
                ·
                  refine ⟨163384979988217401903335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1742773119874318953635573 163384979988217401903335)
                  ·
                    rfl

theorem cell21_715930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_715930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715930 prefixEnd_715930 := by exact prefixLift 715930
  have htrace : WordTrace (prefixWord ++ tailWord_715930) baseStart_715930 baseEnd_715930 := by
    simpa [prefixWord, tailWord_715930, baseEnd_715930] using wordTrace_append hprefix tailTrace_715930
  have hstable : (prefixWord ++ tailWord_715930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715930).length < 2 ^ (prefixWord ++ tailWord_715930).sum := by decide
  have hdescent : baseEnd_715930 < baseStart_715930 := by decide
  rcases family_descends (prefixWord ++ tailWord_715930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715964 : List Nat := [2, 2, 2, 3, 2, 3, 1, 3, 3]
def baseStart_715964 : Nat := 118140960795 + 715964 * 2 ^ 59
def prefixEnd_715964 : Nat := 4983230072969 + 3 ^ 40 * 715964 * 2
def baseEnd_715964 : Nat := 163392739251440898336599

theorem tailTrace_715964 : CollatzResearch.WordTrace tailWord_715964 prefixEnd_715964 163392739251440898336599 := by
  unfold tailWord_715964
  simp only [CollatzResearch.WordTrace]
  refine ⟨13056676189096089880673473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17408901585461453174231297 13056676189096089880673473)
  ·
    refine ⟨9792507141822067410505105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13056676189096089880673473 9792507141822067410505105)
    ·
      refine ⟨7344380356366550557878829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9792507141822067410505105 7344380356366550557878829)
      ·
        refine ⟨2754142633637456459204561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7344380356366550557878829 2754142633637456459204561)
        ·
          refine ⟨2065606975228092344403421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2754142633637456459204561 2065606975228092344403421)
          ·
            refine ⟨774602615710534629151283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2065606975228092344403421 774602615710534629151283)
            ·
              refine ⟨1161903923565801943726925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774602615710534629151283 1161903923565801943726925)
              ·
                refine ⟨435713971337175728897597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1161903923565801943726925 435713971337175728897597)
                ·
                  refine ⟨163392739251440898336599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 435713971337175728897597 163392739251440898336599)
                  ·
                    rfl

theorem cell21_715964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_715964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715964 prefixEnd_715964 := by exact prefixLift 715964
  have htrace : WordTrace (prefixWord ++ tailWord_715964) baseStart_715964 baseEnd_715964 := by
    simpa [prefixWord, tailWord_715964, baseEnd_715964] using wordTrace_append hprefix tailTrace_715964
  have hstable : (prefixWord ++ tailWord_715964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715964).length < 2 ^ (prefixWord ++ tailWord_715964).sum := by decide
  have hdescent : baseEnd_715964 < baseStart_715964 := by decide
  rcases family_descends (prefixWord ++ tailWord_715964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715981 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 5]
def baseStart_715981 : Nat := 118140960795 + 715981 * 2 ^ 59
def prefixEnd_715981 : Nat := 4983230072969 + 3 ^ 40 * 715981 * 2
def baseEnd_715981 : Nat := 163396618883052646553231

theorem tailTrace_715981 : CollatzResearch.WordTrace tailWord_715981 prefixEnd_715981 163396618883052646553231 := by
  unfold tailWord_715981
  simp only [CollatzResearch.WordTrace]
  refine ⟨26113972419130591664715797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17409314946087061109810531 26113972419130591664715797)
  ·
    refine ⟨1224092457146746484283553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26113972419130591664715797 1224092457146746484283553)
    ·
      refine ⟨918069342860059863212665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1224092457146746484283553 918069342860059863212665)
      ·
        refine ⟨688552007145044897409499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 918069342860059863212665 688552007145044897409499)
        ·
          refine ⟨1032828010717567346114249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688552007145044897409499 1032828010717567346114249)
          ·
            refine ⟨774621008038175509585687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1032828010717567346114249 774621008038175509585687)
            ·
              refine ⟨1161931512057263264378531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774621008038175509585687 1161931512057263264378531)
              ·
                refine ⟨1742897268085894896567797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161931512057263264378531 1742897268085894896567797)
                ·
                  refine ⟨163396618883052646553231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1742897268085894896567797 163396618883052646553231)
                  ·
                    rfl

theorem cell21_715981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_715981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_715981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_715981 prefixEnd_715981 := by exact prefixLift 715981
  have htrace : WordTrace (prefixWord ++ tailWord_715981) baseStart_715981 baseEnd_715981 := by
    simpa [prefixWord, tailWord_715981, baseEnd_715981] using wordTrace_append hprefix tailTrace_715981
  have hstable : (prefixWord ++ tailWord_715981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715981).length < 2 ^ (prefixWord ++ tailWord_715981).sum := by decide
  have hdescent : baseEnd_715981 < baseStart_715981 := by decide
  rcases family_descends (prefixWord ++ tailWord_715981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716079 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 6]
def baseStart_716079 : Nat := 118140960795 + 716079 * 2 ^ 59
def prefixEnd_716079 : Nat := 4983230072969 + 3 ^ 40 * 716079 * 2
def baseEnd_716079 : Nat := 163418983818226253919697

theorem tailTrace_716079 : CollatzResearch.WordTrace tailWord_716079 prefixEnd_716079 163418983818226253919697 := by
  unfold tailWord_716079
  simp only [CollatzResearch.WordTrace]
  refine ⟨26117546772775554401783291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17411697848517036267855527 26117546772775554401783291)
  ·
    refine ⟨39176320159163331602674937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26117546772775554401783291 39176320159163331602674937)
    ·
      refine ⟨29382240119372498702006203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39176320159163331602674937 29382240119372498702006203)
      ·
        refine ⟨44073360179058748053009305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29382240119372498702006203 44073360179058748053009305)
        ·
          refine ⟨33055020134294061039756979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44073360179058748053009305 33055020134294061039756979)
          ·
            refine ⟨49582530201441091559635469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33055020134294061039756979 49582530201441091559635469)
            ·
              refine ⟨18593448825540409334863301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49582530201441091559635469 18593448825540409334863301)
              ·
                refine ⟨3486271654788826750286869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18593448825540409334863301 3486271654788826750286869)
                ·
                  refine ⟨163418983818226253919697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3486271654788826750286869 163418983818226253919697)
                  ·
                    rfl

theorem cell21_716079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 6].length) (baseStart_716079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716079 prefixEnd_716079 := by exact prefixLift 716079
  have htrace : WordTrace (prefixWord ++ tailWord_716079) baseStart_716079 baseEnd_716079 := by
    simpa [prefixWord, tailWord_716079, baseEnd_716079] using wordTrace_append hprefix tailTrace_716079
  have hstable : (prefixWord ++ tailWord_716079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716079).length < 2 ^ (prefixWord ++ tailWord_716079).sum := by decide
  have hdescent : baseEnd_716079 < baseStart_716079 := by decide
  rcases family_descends (prefixWord ++ tailWord_716079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716110 : List Nat := [4, 1, 1, 1, 1, 1, 4, 8]
def baseStart_716110 : Nat := 118140960795 + 716110 * 2 ^ 59
def prefixEnd_716110 : Nat := 4983230072969 + 3 ^ 40 * 716110 * 2
def baseEnd_716110 : Nat := 54475352813525696300989

theorem tailTrace_716110 : CollatzResearch.WordTrace tailWord_716110 prefixEnd_716110 54475352813525696300989 := by
  unfold tailWord_716110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3264834679457905837020223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17412451623775497797441189 3264834679457905837020223)
  ·
    refine ⟨4897252019186858755530335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3264834679457905837020223 4897252019186858755530335)
    ·
      refine ⟨7345878028780288133295503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4897252019186858755530335 7345878028780288133295503)
      ·
        refine ⟨11018817043170432199943255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7345878028780288133295503 11018817043170432199943255)
        ·
          refine ⟨16528225564755648299914883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11018817043170432199943255 16528225564755648299914883)
          ·
            refine ⟨24792338347133472449872325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16528225564755648299914883 24792338347133472449872325)
            ·
              refine ⟨4648563440087526084351061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24792338347133472449872325 4648563440087526084351061)
              ·
                refine ⟨54475352813525696300989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4648563440087526084351061 54475352813525696300989)
                ·
                  rfl

theorem cell21_716110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_716110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716110 prefixEnd_716110 := by exact prefixLift 716110
  have htrace : WordTrace (prefixWord ++ tailWord_716110) baseStart_716110 baseEnd_716110 := by
    simpa [prefixWord, tailWord_716110, baseEnd_716110] using wordTrace_append hprefix tailTrace_716110
  have hstable : (prefixWord ++ tailWord_716110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716110).length < 2 ^ (prefixWord ++ tailWord_716110).sum := by decide
  have hdescent : baseEnd_716110 < baseStart_716110 := by decide
  rcases family_descends (prefixWord ++ tailWord_716110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716113 : List Nat := [1, 2, 2, 1, 4, 1, 5, 1, 4]
def baseStart_716113 : Nat := 118140960795 + 716113 * 2 ^ 59
def prefixEnd_716113 : Nat := 4983230072969 + 3 ^ 40 * 716113 * 2
def baseEnd_716113 : Nat := 163426743081449750352961

theorem tailTrace_716113 : CollatzResearch.WordTrace tailWord_716113 prefixEnd_716113 163426743081449750352961 := by
  unfold tailWord_716113
  simp only [CollatzResearch.WordTrace]
  refine ⟨26118786854652378208520993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17412524569768252139013995 26118786854652378208520993)
  ·
    refine ⟨19589090140989283656390745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26118786854652378208520993 19589090140989283656390745)
    ·
      refine ⟨14691817605741962742293059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19589090140989283656390745 14691817605741962742293059)
      ·
        refine ⟨22037726408612944113439589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14691817605741962742293059 22037726408612944113439589)
        ·
          refine ⟨4132073701614927021269923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22037726408612944113439589 4132073701614927021269923)
          ·
            refine ⟨6198110552422390531904885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4132073701614927021269923 6198110552422390531904885)
            ·
              refine ⟨581072864289599112366083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6198110552422390531904885 581072864289599112366083)
              ·
                refine ⟨871609296434398668549125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581072864289599112366083 871609296434398668549125)
                ·
                  refine ⟨163426743081449750352961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 871609296434398668549125 163426743081449750352961)
                  ·
                    rfl

theorem cell21_716113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 4].length) (baseStart_716113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716113 prefixEnd_716113 := by exact prefixLift 716113
  have htrace : WordTrace (prefixWord ++ tailWord_716113) baseStart_716113 baseEnd_716113 := by
    simpa [prefixWord, tailWord_716113, baseEnd_716113] using wordTrace_append hprefix tailTrace_716113
  have hstable : (prefixWord ++ tailWord_716113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716113).length < 2 ^ (prefixWord ++ tailWord_716113).sum := by decide
  have hdescent : baseEnd_716113 < baseStart_716113 := by decide
  rcases family_descends (prefixWord ++ tailWord_716113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716155 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 6]
def baseStart_716155 : Nat := 118140960795 + 716155 * 2 ^ 59
def prefixEnd_716155 : Nat := 4983230072969 + 3 ^ 40 * 716155 * 2
def baseEnd_716155 : Nat := 163436328053667010652875

theorem tailTrace_716155 : CollatzResearch.WordTrace tailWord_716155 prefixEnd_716155 163436328053667010652875 := by
  unfold tailWord_716155
  simp only [CollatzResearch.WordTrace]
  refine ⟨26120318720500219381549919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17413545813666812921033279 26120318720500219381549919)
  ·
    refine ⟨39180478080750329072324879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26120318720500219381549919 39180478080750329072324879)
    ·
      refine ⟨58770717121125493608487319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39180478080750329072324879 58770717121125493608487319)
      ·
        refine ⟨88156075681688240412730979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58770717121125493608487319 88156075681688240412730979)
        ·
          refine ⟨132234113522532360619096469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88156075681688240412730979 132234113522532360619096469)
          ·
            refine ⟨6198474071368704404020147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132234113522532360619096469 6198474071368704404020147)
            ·
              refine ⟨9297711107053056606030221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6198474071368704404020147 9297711107053056606030221)
              ·
                refine ⟨3486641665144896227261333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9297711107053056606030221 3486641665144896227261333)
                ·
                  refine ⟨163436328053667010652875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3486641665144896227261333 163436328053667010652875)
                  ·
                    rfl

theorem cell21_716155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 6].length) (baseStart_716155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716155 prefixEnd_716155 := by exact prefixLift 716155
  have htrace : WordTrace (prefixWord ++ tailWord_716155) baseStart_716155 baseEnd_716155 := by
    simpa [prefixWord, tailWord_716155, baseEnd_716155] using wordTrace_append hprefix tailTrace_716155
  have hstable : (prefixWord ++ tailWord_716155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716155).length < 2 ^ (prefixWord ++ tailWord_716155).sum := by decide
  have hdescent : baseEnd_716155 < baseStart_716155 := by decide
  rcases family_descends (prefixWord ++ tailWord_716155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716172 : List Nat := [2, 2, 1, 2, 1, 3, 3, 3, 4]
def baseStart_716172 : Nat := 118140960795 + 716172 * 2 ^ 59
def prefixEnd_716172 : Nat := 4983230072969 + 3 ^ 40 * 716172 * 2
def baseEnd_716172 : Nat := 163440207685278758869507

theorem tailTrace_716172 : CollatzResearch.WordTrace tailWord_716172 prefixEnd_716172 163440207685278758869507 := by
  unfold tailWord_716172
  simp only [CollatzResearch.WordTrace]
  refine ⟨13060469380719315642459385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17413959174292420856612513 13060469380719315642459385)
  ·
    refine ⟨9795352035539486731844539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13060469380719315642459385 9795352035539486731844539)
    ·
      refine ⟨14693028053309230097766809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9795352035539486731844539 14693028053309230097766809)
      ·
        refine ⟨11019771039981922573325107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14693028053309230097766809 11019771039981922573325107)
        ·
          refine ⟨16529656559972883859987661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11019771039981922573325107 16529656559972883859987661)
          ·
            refine ⟨6198621209989831447495373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16529656559972883859987661 6198621209989831447495373)
            ·
              refine ⟨2324482953746186792810765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6198621209989831447495373 2324482953746186792810765)
              ·
                refine ⟨871681107654820047304037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2324482953746186792810765 871681107654820047304037)
                ·
                  refine ⟨163440207685278758869507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 871681107654820047304037 163440207685278758869507)
                  ·
                    rfl

theorem cell21_716172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_716172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716172 prefixEnd_716172 := by exact prefixLift 716172
  have htrace : WordTrace (prefixWord ++ tailWord_716172) baseStart_716172 baseEnd_716172 := by
    simpa [prefixWord, tailWord_716172, baseEnd_716172] using wordTrace_append hprefix tailTrace_716172
  have hstable : (prefixWord ++ tailWord_716172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716172).length < 2 ^ (prefixWord ++ tailWord_716172).sum := by decide
  have hdescent : baseEnd_716172 < baseStart_716172 := by decide
  rcases family_descends (prefixWord ++ tailWord_716172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716186 : List Nat := [3, 1, 1, 4, 1, 1, 1, 9]
def baseStart_716186 : Nat := 118140960795 + 716186 * 2 ^ 59
def prefixEnd_716186 : Nat := 4983230072969 + 3 ^ 40 * 716186 * 2
def baseEnd_716186 : Nat := 54481134225339281878715

theorem tailTrace_716186 : CollatzResearch.WordTrace tailWord_716186 prefixEnd_716186 54481134225339281878715 := by
  unfold tailWord_716186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6530362345846977918982103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17414299588925274450618941 6530362345846977918982103)
  ·
    refine ⟨9795543518770466878473155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6530362345846977918982103 9795543518770466878473155)
    ·
      refine ⟨14693315278155700317709733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9795543518770466878473155 14693315278155700317709733)
      ·
        refine ⟨2754996614654193809570575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14693315278155700317709733 2754996614654193809570575)
        ·
          refine ⟨4132494921981290714355863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2754996614654193809570575 4132494921981290714355863)
          ·
            refine ⟨6198742382971936071533795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4132494921981290714355863 6198742382971936071533795)
            ·
              refine ⟨9298113574457904107300693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6198742382971936071533795 9298113574457904107300693)
              ·
                refine ⟨54481134225339281878715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9298113574457904107300693 54481134225339281878715)
                ·
                  rfl

theorem cell21_716186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_716186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716186 prefixEnd_716186 := by exact prefixLift 716186
  have htrace : WordTrace (prefixWord ++ tailWord_716186) baseStart_716186 baseEnd_716186 := by
    simpa [prefixWord, tailWord_716186, baseEnd_716186] using wordTrace_append hprefix tailTrace_716186
  have hstable : (prefixWord ++ tailWord_716186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716186).length < 2 ^ (prefixWord ++ tailWord_716186).sum := by decide
  have hdescent : baseEnd_716186 < baseStart_716186 := by decide
  rcases family_descends (prefixWord ++ tailWord_716186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716220 : List Nat := [2, 2, 2, 4, 2, 2, 1, 6]
def baseStart_716220 : Nat := 118140960795 + 716220 * 2 ^ 59
def prefixEnd_716220 : Nat := 4983230072969 + 3 ^ 40 * 716220 * 2
def baseEnd_716220 : Nat := 54483720646413780689803

theorem tailTrace_716220 : CollatzResearch.WordTrace tailWord_716220 prefixEnd_716220 54483720646413780689803 := by
  unfold tailWord_716220
  simp only [CollatzResearch.WordTrace]
  refine ⟨13061344732632367741333057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17415126310176490321777409 13061344732632367741333057)
  ·
    refine ⟨9796008549474275805999793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13061344732632367741333057 9796008549474275805999793)
    ·
      refine ⟨7347006412105706854499845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9796008549474275805999793 7347006412105706854499845)
      ·
        refine ⟨1377563702269820035218721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7347006412105706854499845 1377563702269820035218721)
        ·
          refine ⟨1033172776702365026414041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1377563702269820035218721 1033172776702365026414041)
          ·
            refine ⟨774879582526773769810531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1033172776702365026414041 774879582526773769810531)
            ·
              refine ⟨1162319373790160654715797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774879582526773769810531 1162319373790160654715797)
              ·
                refine ⟨54483720646413780689803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1162319373790160654715797 54483720646413780689803)
                ·
                  rfl

theorem cell21_716220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 6].length) (baseStart_716220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716220 prefixEnd_716220 := by exact prefixLift 716220
  have htrace : WordTrace (prefixWord ++ tailWord_716220) baseStart_716220 baseEnd_716220 := by
    simpa [prefixWord, tailWord_716220, baseEnd_716220] using wordTrace_append hprefix tailTrace_716220
  have hstable : (prefixWord ++ tailWord_716220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716220).length < 2 ^ (prefixWord ++ tailWord_716220).sum := by decide
  have hdescent : baseEnd_716220 < baseStart_716220 := by decide
  rcases family_descends (prefixWord ++ tailWord_716220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716307 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 6]
def baseStart_716307 : Nat := 118140960795 + 716307 * 2 ^ 59
def prefixEnd_716307 : Nat := 4983230072969 + 3 ^ 40 * 716307 * 2
def baseEnd_716307 : Nat := 163471016524548524119231

theorem tailTrace_716307 : CollatzResearch.WordTrace tailWord_716307 prefixEnd_716307 163471016524548524119231 := by
  unfold tailWord_716307
  simp only [CollatzResearch.WordTrace]
  refine ⟨26125862615949549341083175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17417241743966366227388783 26125862615949549341083175)
  ·
    refine ⟨39188793923924324011624763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26125862615949549341083175 39188793923924324011624763)
    ·
      refine ⟨58783190885886486017437145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39188793923924324011624763 58783190885886486017437145)
      ·
        refine ⟨44087393164414864513077859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58783190885886486017437145 44087393164414864513077859)
        ·
          refine ⟨66131089746622296769616789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44087393164414864513077859 66131089746622296769616789)
          ·
            refine ⟨3099894831872920161075787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66131089746622296769616789 3099894831872920161075787)
            ·
              refine ⟨4649842247809380241613681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3099894831872920161075787 4649842247809380241613681)
              ·
                refine ⟨3487381685857035181210261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4649842247809380241613681 3487381685857035181210261)
                ·
                  refine ⟨163471016524548524119231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3487381685857035181210261 163471016524548524119231)
                  ·
                    rfl

theorem cell21_716307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 6].length) (baseStart_716307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716307 prefixEnd_716307 := by exact prefixLift 716307
  have htrace : WordTrace (prefixWord ++ tailWord_716307) baseStart_716307 baseEnd_716307 := by
    simpa [prefixWord, tailWord_716307, baseEnd_716307] using wordTrace_append hprefix tailTrace_716307
  have hstable : (prefixWord ++ tailWord_716307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716307).length < 2 ^ (prefixWord ++ tailWord_716307).sum := by decide
  have hdescent : baseEnd_716307 < baseStart_716307 := by decide
  rcases family_descends (prefixWord ++ tailWord_716307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716341 : List Nat := [1, 3, 3, 1, 1, 3, 4, 1, 4]
def baseStart_716341 : Nat := 118140960795 + 716341 * 2 ^ 59
def prefixEnd_716341 : Nat := 4983230072969 + 3 ^ 40 * 716341 * 2
def baseEnd_716341 : Nat := 163478775787772020552495

theorem tailTrace_716341 : CollatzResearch.WordTrace tailWord_716341 prefixEnd_716341 163478775787772020552495 := by
  unfold tailWord_716341
  simp only [CollatzResearch.WordTrace]
  refine ⟨26127102697826373147820877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17418068465217582098547251 26127102697826373147820877)
  ·
    refine ⟨9797663511684889930432829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26127102697826373147820877 9797663511684889930432829)
    ·
      refine ⟨3674123816881833723912311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9797663511684889930432829 3674123816881833723912311)
      ·
        refine ⟨5511185725322750585868467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3674123816881833723912311 5511185725322750585868467)
        ·
          refine ⟨8266778587984125878802701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5511185725322750585868467 8266778587984125878802701)
          ·
            refine ⟨3100041970494047204551013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8266778587984125878802701 3100041970494047204551013)
            ·
              refine ⟨581257869467633850853315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3100041970494047204551013 581257869467633850853315)
              ·
                refine ⟨871886804201450776279973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581257869467633850853315 871886804201450776279973)
                ·
                  refine ⟨163478775787772020552495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 871886804201450776279973 163478775787772020552495)
                  ·
                    rfl

theorem cell21_716341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_716341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716341 prefixEnd_716341 := by exact prefixLift 716341
  have htrace : WordTrace (prefixWord ++ tailWord_716341) baseStart_716341 baseEnd_716341 := by
    simpa [prefixWord, tailWord_716341, baseEnd_716341] using wordTrace_append hprefix tailTrace_716341
  have hstable : (prefixWord ++ tailWord_716341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716341).length < 2 ^ (prefixWord ++ tailWord_716341).sum := by decide
  have hdescent : baseEnd_716341 < baseStart_716341 := by decide
  rcases family_descends (prefixWord ++ tailWord_716341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716352 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 7]
def baseStart_716352 : Nat := 118140960795 + 716352 * 2 ^ 59
def prefixEnd_716352 : Nat := 4983230072969 + 3 ^ 40 * 716352 * 2
def baseEnd_716352 : Nat := 163481286137638445869139

theorem tailTrace_716352 : CollatzResearch.WordTrace tailWord_716352 prefixEnd_716352 163481286137638445869139 := by
  unfold tailWord_716352
  simp only [CollatzResearch.WordTrace]
  refine ⟨13063751950393261013235655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17418335933857681350980873 13063751950393261013235655)
  ·
    refine ⟨19595627925589891519853483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13063751950393261013235655 19595627925589891519853483)
    ·
      refine ⟨29393441888384837279780225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19595627925589891519853483 29393441888384837279780225)
      ·
        refine ⟨22045081416288627959835169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29393441888384837279780225 22045081416288627959835169)
        ·
          refine ⟨16533811062216470969876377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22045081416288627959835169 16533811062216470969876377)
          ·
            refine ⟨12400358296662353227407283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16533811062216470969876377 12400358296662353227407283)
            ·
              refine ⟨18600537444993529841110925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12400358296662353227407283 18600537444993529841110925)
              ·
                refine ⟨6975201541872573690416597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18600537444993529841110925 6975201541872573690416597)
                ·
                  refine ⟨163481286137638445869139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6975201541872573690416597 163481286137638445869139)
                  ·
                    rfl

theorem cell21_716352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_716352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716352 prefixEnd_716352 := by exact prefixLift 716352
  have htrace : WordTrace (prefixWord ++ tailWord_716352) baseStart_716352 baseEnd_716352 := by
    simpa [prefixWord, tailWord_716352, baseEnd_716352] using wordTrace_append hprefix tailTrace_716352
  have hstable : (prefixWord ++ tailWord_716352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716352).length < 2 ^ (prefixWord ++ tailWord_716352).sum := by decide
  have hdescent : baseEnd_716352 < baseStart_716352 := by decide
  rcases family_descends (prefixWord ++ tailWord_716352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716400 : List Nat := [2, 1, 1, 1, 6, 1, 2, 3, 4]
def baseStart_716400 : Nat := 118140960795 + 716400 * 2 ^ 59
def prefixEnd_716400 : Nat := 4983230072969 + 3 ^ 40 * 716400 * 2
def baseEnd_716400 : Nat := 163492240391601029069041

theorem tailTrace_716400 : CollatzResearch.WordTrace tailWord_716400 prefixEnd_716400 163492240391601029069041 := by
  unfold tailWord_716400
  simp only [CollatzResearch.WordTrace]
  refine ⟨13064627302306313112109327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17419503069741750816145769 13064627302306313112109327)
  ·
    refine ⟨19596940953459469668163991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13064627302306313112109327 19596940953459469668163991)
    ·
      refine ⟨29395411430189204502245987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19596940953459469668163991 29395411430189204502245987)
      ·
        refine ⟨44093117145283806753368981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29395411430189204502245987 44093117145283806753368981)
        ·
          refine ⟨2066864866185178441564171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44093117145283806753368981 2066864866185178441564171)
          ·
            refine ⟨3100297299277767662346257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066864866185178441564171 3100297299277767662346257)
            ·
              refine ⟨2325222974458325746759693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3100297299277767662346257 2325222974458325746759693)
              ·
                refine ⟨871958615421872155034885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2325222974458325746759693 871958615421872155034885)
                ·
                  refine ⟨163492240391601029069041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 871958615421872155034885 163492240391601029069041)
                  ·
                    rfl

theorem cell21_716400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_716400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716400 prefixEnd_716400 := by exact prefixLift 716400
  have htrace : WordTrace (prefixWord ++ tailWord_716400) baseStart_716400 baseEnd_716400 := by
    simpa [prefixWord, tailWord_716400, baseEnd_716400] using wordTrace_append hprefix tailTrace_716400
  have hstable : (prefixWord ++ tailWord_716400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716400).length < 2 ^ (prefixWord ++ tailWord_716400).sum := by decide
  have hdescent : baseEnd_716400 < baseStart_716400 := by decide
  rcases family_descends (prefixWord ++ tailWord_716400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716428 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 7]
def baseStart_716428 : Nat := 118140960795 + 716428 * 2 ^ 59
def prefixEnd_716428 : Nat := 4983230072969 + 3 ^ 40 * 716428 * 2
def baseEnd_716428 : Nat := 163498630373079202602317

theorem tailTrace_716428 : CollatzResearch.WordTrace tailWord_716428 prefixEnd_716428 163498630373079202602317 := by
  unfold tailWord_716428
  simp only [CollatzResearch.WordTrace]
  refine ⟨13065137924255593503118969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17420183899007458004158625 13065137924255593503118969)
  ·
    refine ⟨9798853443191695127339227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13065137924255593503118969 9798853443191695127339227)
    ·
      refine ⟨14698280164787542691008841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9798853443191695127339227 14698280164787542691008841)
      ·
        refine ⟨11023710123590657018256631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14698280164787542691008841 11023710123590657018256631)
        ·
          refine ⟨16535565185385985527384947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11023710123590657018256631 16535565185385985527384947)
          ·
            refine ⟨24803347778078978291077421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16535565185385985527384947 24803347778078978291077421)
            ·
              refine ⟨9301255416779616859154033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24803347778078978291077421 9301255416779616859154033)
              ·
                refine ⟨6975941562584712644365525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9301255416779616859154033 6975941562584712644365525)
                ·
                  refine ⟨163498630373079202602317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6975941562584712644365525 163498630373079202602317)
                  ·
                    rfl

theorem cell21_716428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_716428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716428 prefixEnd_716428 := by exact prefixLift 716428
  have htrace : WordTrace (prefixWord ++ tailWord_716428) baseStart_716428 baseEnd_716428 := by
    simpa [prefixWord, tailWord_716428, baseEnd_716428] using wordTrace_append hprefix tailTrace_716428
  have hstable : (prefixWord ++ tailWord_716428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716428).length < 2 ^ (prefixWord ++ tailWord_716428).sum := by decide
  have hdescent : baseEnd_716428 < baseStart_716428 := by decide
  rcases family_descends (prefixWord ++ tailWord_716428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716434 : List Nat := [3, 2, 3, 1, 3, 2, 1, 2, 4]
def baseStart_716434 : Nat := 118140960795 + 716434 * 2 ^ 59
def prefixEnd_716434 : Nat := 4983230072969 + 3 ^ 40 * 716434 * 2
def baseEnd_716434 : Nat := 163499999654824525502305

theorem tailTrace_716434 : CollatzResearch.WordTrace tailWord_716434 prefixEnd_716434 163499999654824525502305 := by
  unfold tailWord_716434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6532623671622362507739089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17420329790992966687304237 6532623671622362507739089)
  ·
    refine ⟨4899467753716771880804317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6532623671622362507739089 4899467753716771880804317)
    ·
      refine ⟨1837300407643789455301619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4899467753716771880804317 1837300407643789455301619)
      ·
        refine ⟨2755950611465684182952429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1837300407643789455301619 2755950611465684182952429)
        ·
          refine ⟨1033481479299631568607161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2755950611465684182952429 1033481479299631568607161)
          ·
            refine ⟨775111109474723676455371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1033481479299631568607161 775111109474723676455371)
            ·
              refine ⟨1162666664212085514683057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775111109474723676455371 1162666664212085514683057)
              ·
                refine ⟨871999998159064136012293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1162666664212085514683057 871999998159064136012293)
                ·
                  refine ⟨163499999654824525502305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 871999998159064136012293 163499999654824525502305)
                  ·
                    rfl

theorem cell21_716434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_716434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716434 prefixEnd_716434 := by exact prefixLift 716434
  have htrace : WordTrace (prefixWord ++ tailWord_716434) baseStart_716434 baseEnd_716434 := by
    simpa [prefixWord, tailWord_716434, baseEnd_716434] using wordTrace_append hprefix tailTrace_716434
  have hstable : (prefixWord ++ tailWord_716434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716434).length < 2 ^ (prefixWord ++ tailWord_716434).sum := by decide
  have hdescent : baseEnd_716434 < baseStart_716434 := by decide
  rcases family_descends (prefixWord ++ tailWord_716434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716482 : List Nat := [3, 5, 1, 2, 2, 1, 7]
def baseStart_716482 : Nat := 118140960795 + 716482 * 2 ^ 59
def prefixEnd_716482 : Nat := 4983230072969 + 3 ^ 40 * 716482 * 2
def baseEnd_716482 : Nat := 18167883767643012078023

theorem tailTrace_716482 : CollatzResearch.WordTrace tailWord_716482 prefixEnd_716482 18167883767643012078023 := by
  unfold tailWord_716482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6533061347578888557175925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17421496926877036152469133 6533061347578888557175925)
  ·
    refine ⟨612474501335520802235243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6533061347578888557175925 612474501335520802235243)
    ·
      refine ⟨918711752003281203352865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 612474501335520802235243 918711752003281203352865)
      ·
        refine ⟨689033814002460902514649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 918711752003281203352865 689033814002460902514649)
        ·
          refine ⟨516775360501845676885987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 689033814002460902514649 516775360501845676885987)
          ·
            refine ⟨775163040752768515328981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516775360501845676885987 775163040752768515328981)
            ·
              refine ⟨18167883767643012078023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 775163040752768515328981 18167883767643012078023)
              ·
                rfl

theorem cell21_716482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 7].length) (baseStart_716482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716482 prefixEnd_716482 := by exact prefixLift 716482
  have htrace : WordTrace (prefixWord ++ tailWord_716482) baseStart_716482 baseEnd_716482 := by
    simpa [prefixWord, tailWord_716482, baseEnd_716482] using wordTrace_append hprefix tailTrace_716482
  have hstable : (prefixWord ++ tailWord_716482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716482).length < 2 ^ (prefixWord ++ tailWord_716482).sum := by decide
  have hdescent : baseEnd_716482 < baseStart_716482 := by decide
  rcases family_descends (prefixWord ++ tailWord_716482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716493 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 6]
def baseStart_716493 : Nat := 118140960795 + 716493 * 2 ^ 59
def prefixEnd_716493 : Nat := 4983230072969 + 3 ^ 40 * 716493 * 2
def baseEnd_716493 : Nat := 163513464258653534018851

theorem tailTrace_716493 : CollatzResearch.WordTrace tailWord_716493 prefixEnd_716493 163513464258653534018851 := by
  unfold tailWord_716493
  simp only [CollatzResearch.WordTrace]
  refine ⟨26132646593275703107354133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17421764395517135404902755 26132646593275703107354133)
  ·
    refine ⟨1224967809059798583157225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26132646593275703107354133 1224967809059798583157225)
    ·
      refine ⟨918725856794848937367919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1224967809059798583157225 918725856794848937367919)
      ·
        refine ⟨1378088785192273406051879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 918725856794848937367919 1378088785192273406051879)
        ·
          refine ⟨2067133177788410109077819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378088785192273406051879 2067133177788410109077819)
          ·
            refine ⟨3100699766682615163616729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2067133177788410109077819 3100699766682615163616729)
            ·
              refine ⟨2325524825011961372712547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3100699766682615163616729 2325524825011961372712547)
              ·
                refine ⟨3488287237517942059068821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2325524825011961372712547 3488287237517942059068821)
                ·
                  refine ⟨163513464258653534018851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3488287237517942059068821 163513464258653534018851)
                  ·
                    rfl

theorem cell21_716493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_716493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716493 prefixEnd_716493 := by exact prefixLift 716493
  have htrace : WordTrace (prefixWord ++ tailWord_716493) baseStart_716493 baseEnd_716493 := by
    simpa [prefixWord, tailWord_716493, baseEnd_716493] using wordTrace_append hprefix tailTrace_716493
  have hstable : (prefixWord ++ tailWord_716493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716493).length < 2 ^ (prefixWord ++ tailWord_716493).sum := by decide
  have hdescent : baseEnd_716493 < baseStart_716493 := by decide
  rcases family_descends (prefixWord ++ tailWord_716493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716552 : List Nat := [2, 1, 3, 2, 2, 1, 4, 2, 4]
def baseStart_716552 : Nat := 118140960795 + 716552 * 2 ^ 59
def prefixEnd_716552 : Nat := 4983230072969 + 3 ^ 40 * 716552 * 2
def baseEnd_716552 : Nat := 163526928862482542535397

theorem tailTrace_716552 : CollatzResearch.WordTrace tailWord_716552 prefixEnd_716552 163526928862482542535397 := by
  unfold tailWord_716552
  simp only [CollatzResearch.WordTrace]
  refine ⟨13067399250030978091875955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17423199000041304122501273 13067399250030978091875955)
  ·
    refine ⟨19601098875046467137813933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13067399250030978091875955 19601098875046467137813933)
    ·
      refine ⟨7350412078142425176680225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19601098875046467137813933 7350412078142425176680225)
      ·
        refine ⟨5512809058606818882510169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7350412078142425176680225 5512809058606818882510169)
        ·
          refine ⟨4134606793955114161882627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5512809058606818882510169 4134606793955114161882627)
          ·
            refine ⟨6201910190932671242823941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4134606793955114161882627 6201910190932671242823941)
            ·
              refine ⟨1162858160799875858029489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6201910190932671242823941 1162858160799875858029489)
              ·
                refine ⟨872143620599906893522117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1162858160799875858029489 872143620599906893522117)
                ·
                  refine ⟨163526928862482542535397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 872143620599906893522117 163526928862482542535397)
                  ·
                    rfl

theorem cell21_716552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_716552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716552 prefixEnd_716552 := by exact prefixLift 716552
  have htrace : WordTrace (prefixWord ++ tailWord_716552) baseStart_716552 baseEnd_716552 := by
    simpa [prefixWord, tailWord_716552, baseEnd_716552] using wordTrace_append hprefix tailTrace_716552
  have hstable : (prefixWord ++ tailWord_716552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716552).length < 2 ^ (prefixWord ++ tailWord_716552).sum := by decide
  have hdescent : baseEnd_716552 < baseStart_716552 := by decide
  rcases family_descends (prefixWord ++ tailWord_716552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716611 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 6]
def baseStart_716611 : Nat := 118140960795 + 716611 * 2 ^ 59
def prefixEnd_716611 : Nat := 4983230072969 + 3 ^ 40 * 716611 * 2
def baseEnd_716611 : Nat := 163540393466311551051943

theorem tailTrace_716611 : CollatzResearch.WordTrace tailWord_716611 prefixEnd_716611 163540393466311551051943 := by
  unfold tailWord_716611
  simp only [CollatzResearch.WordTrace]
  refine ⟨26136950406848209260149687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17424633604565472840099791 26136950406848209260149687)
  ·
    refine ⟨39205425610272313890224531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26136950406848209260149687 39205425610272313890224531)
    ·
      refine ⟨58808138415408470835336797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39205425610272313890224531 58808138415408470835336797)
      ·
        refine ⟨22053051905778176563251299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58808138415408470835336797 22053051905778176563251299)
        ·
          refine ⟨33079577858667264844876949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22053051905778176563251299 33079577858667264844876949)
          ·
            refine ⟨1550605212125028039603607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33079577858667264844876949 1550605212125028039603607)
            ·
              refine ⟨2325907818187542059405411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550605212125028039603607 2325907818187542059405411)
              ·
                refine ⟨3488861727281313089108117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2325907818187542059405411 3488861727281313089108117)
                ·
                  refine ⟨163540393466311551051943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3488861727281313089108117 163540393466311551051943)
                  ·
                    rfl

theorem cell21_716611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 6].length) (baseStart_716611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716611 prefixEnd_716611 := by exact prefixLift 716611
  have htrace : WordTrace (prefixWord ++ tailWord_716611) baseStart_716611 baseEnd_716611 := by
    simpa [prefixWord, tailWord_716611, baseEnd_716611] using wordTrace_append hprefix tailTrace_716611
  have hstable : (prefixWord ++ tailWord_716611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716611).length < 2 ^ (prefixWord ++ tailWord_716611).sum := by decide
  have hdescent : baseEnd_716611 < baseStart_716611 := by decide
  rcases family_descends (prefixWord ++ tailWord_716611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716724 : List Nat := [2, 5, 2, 1, 2, 1, 1, 4, 3]
def baseStart_716724 : Nat := 118140960795 + 716724 * 2 ^ 59
def prefixEnd_716724 : Nat := 4983230072969 + 3 ^ 40 * 716724 * 2
def baseEnd_716724 : Nat := 163566181605848465668379

theorem tailTrace_716724 : CollatzResearch.WordTrace tailWord_716724 prefixEnd_716724 163566181605848465668379 := by
  unfold tailWord_716724
  simp only [CollatzResearch.WordTrace]
  refine ⟨13070535927719414779506613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17427381236959219706008817 13070535927719414779506613)
  ·
    refine ⟨1225362743223695135578745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13070535927719414779506613 1225362743223695135578745)
    ·
      refine ⟨919022057417771351684059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1225362743223695135578745 919022057417771351684059)
      ·
        refine ⟨1378533086126657027526089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 919022057417771351684059 1378533086126657027526089)
        ·
          refine ⟨1033899814594992770644567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1378533086126657027526089 1033899814594992770644567)
          ·
            refine ⟨1550849721892489155966851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033899814594992770644567 1550849721892489155966851)
            ·
              refine ⟨2326274582838733733950277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550849721892489155966851 2326274582838733733950277)
              ·
                refine ⟨436176484282262575115677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2326274582838733733950277 436176484282262575115677)
                ·
                  refine ⟨163566181605848465668379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 436176484282262575115677 163566181605848465668379)
                  ·
                    rfl

theorem cell21_716724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_716724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716724 prefixEnd_716724 := by exact prefixLift 716724
  have htrace : WordTrace (prefixWord ++ tailWord_716724) baseStart_716724 baseEnd_716724 := by
    simpa [prefixWord, tailWord_716724, baseEnd_716724] using wordTrace_append hprefix tailTrace_716724
  have hstable : (prefixWord ++ tailWord_716724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716724).length < 2 ^ (prefixWord ++ tailWord_716724).sum := by decide
  have hdescent : baseEnd_716724 < baseStart_716724 := by decide
  rcases family_descends (prefixWord ++ tailWord_716724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716808 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 5]
def baseStart_716808 : Nat := 118140960795 + 716808 * 2 ^ 59
def prefixEnd_716808 : Nat := 4983230072969 + 3 ^ 40 * 716808 * 2
def baseEnd_716808 : Nat := 163585351550282986268207

theorem tailTrace_716808 : CollatzResearch.WordTrace tailWord_716808 prefixEnd_716808 163585351550282986268207 := by
  unfold tailWord_716808
  simp only [CollatzResearch.WordTrace]
  refine ⟨13072067793567255952535539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17429423724756341270047385 13072067793567255952535539)
  ·
    refine ⟨19608101690350883928803309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13072067793567255952535539 19608101690350883928803309)
    ·
      refine ⟨7353038133881581473301241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19608101690350883928803309 7353038133881581473301241)
      ·
        refine ⟨5514778600411186104975931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7353038133881581473301241 5514778600411186104975931)
        ·
          refine ⟨8272167900616779157463897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5514778600411186104975931 8272167900616779157463897)
          ·
            refine ⟨6204125925462584368097923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8272167900616779157463897 6204125925462584368097923)
            ·
              refine ⟨9306188888193876552146885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6204125925462584368097923 9306188888193876552146885)
              ·
                refine ⟨1744910416536351853527541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9306188888193876552146885 1744910416536351853527541)
                ·
                  refine ⟨163585351550282986268207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1744910416536351853527541 163585351550282986268207)
                  ·
                    rfl

theorem cell21_716808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_716808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716808 prefixEnd_716808 := by exact prefixLift 716808
  have htrace : WordTrace (prefixWord ++ tailWord_716808) baseStart_716808 baseEnd_716808 := by
    simpa [prefixWord, tailWord_716808, baseEnd_716808] using wordTrace_append hprefix tailTrace_716808
  have hstable : (prefixWord ++ tailWord_716808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716808).length < 2 ^ (prefixWord ++ tailWord_716808).sum := by decide
  have hdescent : baseEnd_716808 < baseStart_716808 := by decide
  rcases family_descends (prefixWord ++ tailWord_716808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716842 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 5]
def baseStart_716842 : Nat := 118140960795 + 716842 * 2 ^ 59
def prefixEnd_716842 : Nat := 4983230072969 + 3 ^ 40 * 716842 * 2
def baseEnd_716842 : Nat := 163593110813506482701471

theorem tailTrace_716842 : CollatzResearch.WordTrace tailWord_716842 prefixEnd_716842 163593110813506482701471 := by
  unfold tailWord_716842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6536343917252833927952195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17430250446007557141205853 6536343917252833927952195)
  ·
    refine ⟨9804515875879250891928293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6536343917252833927952195 9804515875879250891928293)
    ·
      refine ⟨1838346726727359542236555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9804515875879250891928293 1838346726727359542236555)
      ·
        refine ⟨2757520090091039313354833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1838346726727359542236555 2757520090091039313354833)
        ·
          refine ⟨2068140067568279485016125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2757520090091039313354833 2068140067568279485016125)
          ·
            refine ⟨775552525338104806881047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2068140067568279485016125 775552525338104806881047)
            ·
              refine ⟨1163328788007157210321571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775552525338104806881047 1163328788007157210321571)
              ·
                refine ⟨1744993182010735815482357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163328788007157210321571 1744993182010735815482357)
                ·
                  refine ⟨163593110813506482701471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1744993182010735815482357 163593110813506482701471)
                  ·
                    rfl

theorem cell21_716842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_716842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716842 prefixEnd_716842 := by exact prefixLift 716842
  have htrace : WordTrace (prefixWord ++ tailWord_716842) baseStart_716842 baseEnd_716842 := by
    simpa [prefixWord, tailWord_716842, baseEnd_716842] using wordTrace_append hprefix tailTrace_716842
  have hstable : (prefixWord ++ tailWord_716842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716842).length < 2 ^ (prefixWord ++ tailWord_716842).sum := by decide
  have hdescent : baseEnd_716842 < baseStart_716842 := by decide
  rcases family_descends (prefixWord ++ tailWord_716842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716853 : List Nat := [1, 3, 3, 1, 1, 1, 3, 8]
def baseStart_716853 : Nat := 118140960795 + 716853 * 2 ^ 59
def prefixEnd_716853 : Nat := 4983230072969 + 3 ^ 40 * 716853 * 2
def baseEnd_716853 : Nat := 54531873721124302672705

theorem tailTrace_716853 : CollatzResearch.WordTrace tailWord_716853 prefixEnd_716853 54531873721124302672705 := by
  unfold tailWord_716853
  simp only [CollatzResearch.WordTrace]
  refine ⟨26145776871971484590459213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17430517914647656393639475 26145776871971484590459213)
  ·
    refine ⟨9804666326989306721422205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26145776871971484590459213 9804666326989306721422205)
    ·
      refine ⟨3676749872620990020533327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9804666326989306721422205 3676749872620990020533327)
      ·
        refine ⟨5515124808931485030799991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3676749872620990020533327 5515124808931485030799991)
        ·
          refine ⟨8272687213397227546199987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5515124808931485030799991 8272687213397227546199987)
          ·
            refine ⟨12409030820095841319299981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8272687213397227546199987 12409030820095841319299981)
            ·
              refine ⟨4653386557535940494737493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12409030820095841319299981 4653386557535940494737493)
              ·
                refine ⟨54531873721124302672705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4653386557535940494737493 54531873721124302672705)
                ·
                  rfl

theorem cell21_716853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 8].length) (baseStart_716853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716853 prefixEnd_716853 := by exact prefixLift 716853
  have htrace : WordTrace (prefixWord ++ tailWord_716853) baseStart_716853 baseEnd_716853 := by
    simpa [prefixWord, tailWord_716853, baseEnd_716853] using wordTrace_append hprefix tailTrace_716853
  have hstable : (prefixWord ++ tailWord_716853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716853).length < 2 ^ (prefixWord ++ tailWord_716853).sum := by decide
  have hdescent : baseEnd_716853 < baseStart_716853 := by decide
  rcases family_descends (prefixWord ++ tailWord_716853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716856 : List Nat := [2, 1, 2, 1, 6, 1, 1, 3, 4]
def baseStart_716856 : Nat := 118140960795 + 716856 * 2 ^ 59
def prefixEnd_716856 : Nat := 4983230072969 + 3 ^ 40 * 716856 * 2
def baseEnd_716856 : Nat := 163596305804245569468109

theorem tailTrace_716856 : CollatzResearch.WordTrace tailWord_716856 prefixEnd_716856 163596305804245569468109 := by
  unfold tailWord_716856
  simp only [CollatzResearch.WordTrace]
  refine ⟨13072943145480308051409211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17430590860640410735212281 13072943145480308051409211)
  ·
    refine ⟨19609414718220462077113817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13072943145480308051409211 19609414718220462077113817)
    ·
      refine ⟨14707061038665346557835363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19609414718220462077113817 14707061038665346557835363)
      ·
        refine ⟨22060591557998019836753045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14707061038665346557835363 22060591557998019836753045)
        ·
          refine ⟨1034090229281157179847799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22060591557998019836753045 1034090229281157179847799)
          ·
            refine ⟨1551135343921735769771699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034090229281157179847799 1551135343921735769771699)
            ·
              refine ⟨2326703015882603654657549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1551135343921735769771699 2326703015882603654657549)
              ·
                refine ⟨872513630955976370496581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2326703015882603654657549 872513630955976370496581)
                ·
                  refine ⟨163596305804245569468109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 872513630955976370496581 163596305804245569468109)
                  ·
                    rfl

theorem cell21_716856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_716856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716856 prefixEnd_716856 := by exact prefixLift 716856
  have htrace : WordTrace (prefixWord ++ tailWord_716856) baseStart_716856 baseEnd_716856 := by
    simpa [prefixWord, tailWord_716856, baseEnd_716856] using wordTrace_append hprefix tailTrace_716856
  have hstable : (prefixWord ++ tailWord_716856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716856).length < 2 ^ (prefixWord ++ tailWord_716856).sum := by decide
  have hdescent : baseEnd_716856 < baseStart_716856 := by decide
  rcases family_descends (prefixWord ++ tailWord_716856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716960 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 5]
def baseStart_716960 : Nat := 118140960795 + 716960 * 2 ^ 59
def prefixEnd_716960 : Nat := 4983230072969 + 3 ^ 40 * 716960 * 2
def baseEnd_716960 : Nat := 163620040021164499734563

theorem tailTrace_716960 : CollatzResearch.WordTrace tailWord_716960 prefixEnd_716960 163620040021164499734563 := by
  unfold tailWord_716960
  simp only [CollatzResearch.WordTrace]
  refine ⟨13074839741291920932302167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17433119655055894576402889 13074839741291920932302167)
  ·
    refine ⟨19612259611937881398453251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13074839741291920932302167 19612259611937881398453251)
    ·
      refine ⟨29418389417906822097679877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19612259611937881398453251 29418389417906822097679877)
      ·
        refine ⟨5515948015857529143314977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29418389417906822097679877 5515948015857529143314977)
        ·
          refine ⟨4136961011893146857486233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5515948015857529143314977 4136961011893146857486233)
          ·
            refine ⟨3102720758919860143114675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4136961011893146857486233 3102720758919860143114675)
            ·
              refine ⟨4654081138379790214672013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3102720758919860143114675 4654081138379790214672013)
              ·
                refine ⟨1745280426892421330502005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4654081138379790214672013 1745280426892421330502005)
                ·
                  refine ⟨163620040021164499734563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1745280426892421330502005 163620040021164499734563)
                  ·
                    rfl

theorem cell21_716960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_716960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_716960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_716960 prefixEnd_716960 := by exact prefixLift 716960
  have htrace : WordTrace (prefixWord ++ tailWord_716960) baseStart_716960 baseEnd_716960 := by
    simpa [prefixWord, tailWord_716960, baseEnd_716960] using wordTrace_append hprefix tailTrace_716960
  have hstable : (prefixWord ++ tailWord_716960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716960).length < 2 ^ (prefixWord ++ tailWord_716960).sum := by decide
  have hdescent : baseEnd_716960 < baseStart_716960 := by decide
  rcases family_descends (prefixWord ++ tailWord_716960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717067 : List Nat := [1, 1, 1, 1, 5, 2, 4, 2, 4]
def baseStart_717067 : Nat := 118140960795 + 717067 * 2 ^ 59
def prefixEnd_717067 : Nat := 4983230072969 + 3 ^ 40 * 717067 * 2
def baseEnd_717067 : Nat := 163644458878956091451011

theorem tailTrace_717067 : CollatzResearch.WordTrace tailWord_717067 prefixEnd_717067 163644458878956091451011 := by
  unfold tailWord_717067
  simp only [CollatzResearch.WordTrace]
  refine ⟨26153582093196199138749455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17435721395464132759166303 26153582093196199138749455)
  ·
    refine ⟨39230373139794298708124183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26153582093196199138749455 39230373139794298708124183)
    ·
      refine ⟨58845559709691448062186275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39230373139794298708124183 58845559709691448062186275)
      ·
        refine ⟨88268339564537172093279413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58845559709691448062186275 88268339564537172093279413)
        ·
          refine ⟨8275156834175359883744945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88268339564537172093279413 8275156834175359883744945)
          ·
            refine ⟨6206367625631519912808709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8275156834175359883744945 6206367625631519912808709)
            ·
              refine ⟨1163693929805909983651633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6206367625631519912808709 1163693929805909983651633)
              ·
                refine ⟨872770447354432487738725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1163693929805909983651633 872770447354432487738725)
                ·
                  refine ⟨163644458878956091451011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 872770447354432487738725 163644458878956091451011)
                  ·
                    rfl

theorem cell21_717067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 4].length) (baseStart_717067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_717067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_717067 prefixEnd_717067 := by exact prefixLift 717067
  have htrace : WordTrace (prefixWord ++ tailWord_717067) baseStart_717067 baseEnd_717067 := by
    simpa [prefixWord, tailWord_717067, baseEnd_717067] using wordTrace_append hprefix tailTrace_717067
  have hstable : (prefixWord ++ tailWord_717067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717067).length < 2 ^ (prefixWord ++ tailWord_717067).sum := by decide
  have hdescent : baseEnd_717067 < baseStart_717067 := by decide
  rcases family_descends (prefixWord ++ tailWord_717067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717157 : List Nat := [1, 3, 1, 3, 1, 4, 1, 7]
def baseStart_717157 : Nat := 118140960795 + 717157 * 2 ^ 59
def prefixEnd_717157 : Nat := 4983230072969 + 3 ^ 40 * 717157 * 2
def baseEnd_717157 : Nat := 54554999368378644983609

theorem tailTrace_717157 : CollatzResearch.WordTrace tailWord_717157 prefixEnd_717157 54554999368378644983609 := by
  unfold tailWord_717157
  simp only [CollatzResearch.WordTrace]
  refine ⟨26156864662870144509525725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17437909775246763006350483 26156864662870144509525725)
  ·
    refine ⟨9808824248576304191072147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26156864662870144509525725 9808824248576304191072147)
    ·
      refine ⟨14713236372864456286608221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9808824248576304191072147 14713236372864456286608221)
      ·
        refine ⟨5517463639824171107478083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14713236372864456286608221 5517463639824171107478083)
        ·
          refine ⟨8276195459736256661217125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5517463639824171107478083 8276195459736256661217125)
          ·
            refine ⟨1551786648700548123978211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8276195459736256661217125 1551786648700548123978211)
            ·
              refine ⟨2327679973050822185967317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1551786648700548123978211 2327679973050822185967317)
              ·
                refine ⟨54554999368378644983609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2327679973050822185967317 54554999368378644983609)
                ·
                  rfl

theorem cell21_717157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 7].length) (baseStart_717157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_717157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_717157 prefixEnd_717157 := by exact prefixLift 717157
  have htrace : WordTrace (prefixWord ++ tailWord_717157) baseStart_717157 baseEnd_717157 := by
    simpa [prefixWord, tailWord_717157, baseEnd_717157] using wordTrace_append hprefix tailTrace_717157
  have hstable : (prefixWord ++ tailWord_717157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717157).length < 2 ^ (prefixWord ++ tailWord_717157).sum := by decide
  have hdescent : baseEnd_717157 < baseStart_717157 := by decide
  rcases family_descends (prefixWord ++ tailWord_717157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717194 : List Nat := [3, 1, 2, 5, 1, 2, 2, 1, 4]
def baseStart_717194 : Nat := 118140960795 + 717194 * 2 ^ 59
def prefixEnd_717194 : Nat := 4983230072969 + 3 ^ 40 * 717194 * 2
def baseEnd_717194 : Nat := 163673442009232092834085

theorem tailTrace_717194 : CollatzResearch.WordTrace tailWord_717194 prefixEnd_717194 163673442009232092834085 := by
  unfold tailWord_717194
  simp only [CollatzResearch.WordTrace]
  refine ⟨6539553540934024957155659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17438809442490733219081757 6539553540934024957155659)
  ·
    refine ⟨9809330311401037435733489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6539553540934024957155659 9809330311401037435733489)
    ·
      refine ⟨7356997733550778076800117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9809330311401037435733489 7356997733550778076800117)
      ·
        refine ⟨689718537520385444700011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7356997733550778076800117 689718537520385444700011)
        ·
          refine ⟨1034577806280578167050017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689718537520385444700011 1034577806280578167050017)
          ·
            refine ⟨775933354710433625287513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1034577806280578167050017 775933354710433625287513)
            ·
              refine ⟨581950016032825218965635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 775933354710433625287513 581950016032825218965635)
              ·
                refine ⟨872925024049237828448453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581950016032825218965635 872925024049237828448453)
                ·
                  refine ⟨163673442009232092834085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 872925024049237828448453 163673442009232092834085)
                  ·
                    rfl

theorem cell21_717194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_717194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_717194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_717194 prefixEnd_717194 := by exact prefixLift 717194
  have htrace : WordTrace (prefixWord ++ tailWord_717194) baseStart_717194 baseEnd_717194 := by
    simpa [prefixWord, tailWord_717194, baseEnd_717194] using wordTrace_append hprefix tailTrace_717194
  have hstable : (prefixWord ++ tailWord_717194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717194).length < 2 ^ (prefixWord ++ tailWord_717194).sum := by decide
  have hdescent : baseEnd_717194 < baseStart_717194 := by decide
  rcases family_descends (prefixWord ++ tailWord_717194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717281 : List Nat := [1, 2, 3, 1, 2, 2, 4, 3, 3]
def baseStart_717281 : Nat := 118140960795 + 717281 * 2 ^ 59
def prefixEnd_717281 : Nat := 4983230072969 + 3 ^ 40 * 717281 * 2
def baseEnd_717281 : Nat := 163693296594539274883907

theorem tailTrace_717281 : CollatzResearch.WordTrace tailWord_717281 prefixEnd_717281 163693296594539274883907 := by
  unfold tailWord_717281
  simp only [CollatzResearch.WordTrace]
  refine ⟨26161387314420913687039697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17440924876280609124693131 26161387314420913687039697)
  ·
    refine ⟨19621040485815685265279773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26161387314420913687039697 19621040485815685265279773)
    ·
      refine ⟨7357890182180881974479915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19621040485815685265279773 7357890182180881974479915)
      ·
        refine ⟨11036835273271322961719873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7357890182180881974479915 11036835273271322961719873)
        ·
          refine ⟨8277626454953492221289905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11036835273271322961719873 8277626454953492221289905)
          ·
            refine ⟨6208219841215119165967429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8277626454953492221289905 6208219841215119165967429)
            ·
              refine ⟨1164041220227834843618893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6208219841215119165967429 1164041220227834843618893)
              ·
                refine ⟨436515457585438066357085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1164041220227834843618893 436515457585438066357085)
                ·
                  refine ⟨163693296594539274883907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 436515457585438066357085 163693296594539274883907)
                  ·
                    rfl

theorem cell21_717281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 3].length) (baseStart_717281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_717281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_717281 prefixEnd_717281 := by exact prefixLift 717281
  have htrace : WordTrace (prefixWord ++ tailWord_717281) baseStart_717281 baseEnd_717281 := by
    simpa [prefixWord, tailWord_717281, baseEnd_717281] using wordTrace_append hprefix tailTrace_717281
  have hstable : (prefixWord ++ tailWord_717281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717281).length < 2 ^ (prefixWord ++ tailWord_717281).sum := by decide
  have hdescent : baseEnd_717281 < baseStart_717281 := by decide
  rcases family_descends (prefixWord ++ tailWord_717281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717292 : List Nat := [2, 2, 1, 1, 2, 1, 12]
def baseStart_717292 : Nat := 118140960795 + 717292 * 2 ^ 59
def prefixEnd_717292 : Nat := 4983230072969 + 3 ^ 40 * 717292 * 2
def baseEnd_717292 : Nat := 18188422993822855577839

theorem tailTrace_717292 : CollatzResearch.WordTrace tailWord_717292 prefixEnd_717292 18188422993822855577839 := by
  unfold tailWord_717292
  simp only [CollatzResearch.WordTrace]
  refine ⟨13080894258690531282845065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17441192344920708377126753 13080894258690531282845065)
  ·
    refine ⟨9810670694017898462133799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13080894258690531282845065 9810670694017898462133799)
    ·
      refine ⟨14716006041026847693200699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9810670694017898462133799 14716006041026847693200699)
      ·
        refine ⟨22074009061540271539801049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14716006041026847693200699 22074009061540271539801049)
        ·
          refine ⟨16555506796155203654850787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22074009061540271539801049 16555506796155203654850787)
          ·
            refine ⟨24833260194232805482276181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16555506796155203654850787 24833260194232805482276181)
            ·
              refine ⟨18188422993822855577839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 24833260194232805482276181 18188422993822855577839)
              ·
                rfl

theorem cell21_717292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 12].length) (baseStart_717292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_717292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_717292 prefixEnd_717292 := by exact prefixLift 717292
  have htrace : WordTrace (prefixWord ++ tailWord_717292) baseStart_717292 baseEnd_717292 := by
    simpa [prefixWord, tailWord_717292, baseEnd_717292] using wordTrace_append hprefix tailTrace_717292
  have hstable : (prefixWord ++ tailWord_717292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717292).length < 2 ^ (prefixWord ++ tailWord_717292).sum := by decide
  have hdescent : baseEnd_717292 < baseStart_717292 := by decide
  rcases family_descends (prefixWord ++ tailWord_717292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717326 : List Nat := [4, 1, 1, 2, 3, 1, 4, 5]
def baseStart_717326 : Nat := 118140960795 + 717326 * 2 ^ 59
def prefixEnd_717326 : Nat := 4983230072969 + 3 ^ 40 * 717326 * 2
def baseEnd_717326 : Nat := 54567855402543065544605

theorem tailTrace_717326 : CollatzResearch.WordTrace tailWord_717326 prefixEnd_717326 54567855402543065544605 := by
  unfold tailWord_717326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3270378574907235796553479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17442019066171924248285221 3270378574907235796553479)
  ·
    refine ⟨4905567862360853694830219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3270378574907235796553479 4905567862360853694830219)
    ·
      refine ⟨7358351793541280542245329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4905567862360853694830219 7358351793541280542245329)
      ·
        refine ⟨5518763845155960406683997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7358351793541280542245329 5518763845155960406683997)
        ·
          refine ⟨2069536441933485152506499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5518763845155960406683997 2069536441933485152506499)
          ·
            refine ⟨3104304662900227728759749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2069536441933485152506499 3104304662900227728759749)
            ·
              refine ⟨582057124293792699142453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3104304662900227728759749 582057124293792699142453)
              ·
                refine ⟨54567855402543065544605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 582057124293792699142453 54567855402543065544605)
                ·
                  rfl

theorem cell21_717326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_717326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_717326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_717326 prefixEnd_717326 := by exact prefixLift 717326
  have htrace : WordTrace (prefixWord ++ tailWord_717326) baseStart_717326 baseEnd_717326 := by
    simpa [prefixWord, tailWord_717326, baseEnd_717326] using wordTrace_append hprefix tailTrace_717326
  have hstable : (prefixWord ++ tailWord_717326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717326).length < 2 ^ (prefixWord ++ tailWord_717326).sum := by decide
  have hdescent : baseEnd_717326 < baseStart_717326 := by decide
  rcases family_descends (prefixWord ++ tailWord_717326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717450 : List Nat := [3, 1, 2, 3, 3, 1, 2, 3, 3]
def baseStart_717450 : Nat := 118140960795 + 717450 * 2 ^ 59
def prefixEnd_717450 : Nat := 4983230072969 + 3 ^ 40 * 717450 * 2
def baseEnd_717450 : Nat := 163731864697032536566895

theorem tailTrace_717450 : CollatzResearch.WordTrace tailWord_717450 prefixEnd_717450 163731864697032536566895 := by
  unfold tailWord_717450
  simp only [CollatzResearch.WordTrace]
  refine ⟨6541887812702163887485451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17445034167205770366627869 6541887812702163887485451)
  ·
    refine ⟨9812831719053245831228177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6541887812702163887485451 9812831719053245831228177)
    ·
      refine ⟨7359623789289934373421133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9812831719053245831228177 7359623789289934373421133)
      ·
        refine ⟨2759858920983725390032925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7359623789289934373421133 2759858920983725390032925)
        ·
          refine ⟨1034947095368897021262347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2759858920983725390032925 1034947095368897021262347)
          ·
            refine ⟨1552420643053345531893521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034947095368897021262347 1552420643053345531893521)
            ·
              refine ⟨1164315482290009148920141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1552420643053345531893521 1164315482290009148920141)
              ·
                refine ⟨436618305858753430845053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1164315482290009148920141 436618305858753430845053)
                ·
                  refine ⟨163731864697032536566895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 436618305858753430845053 163731864697032536566895)
                  ·
                    rfl

theorem cell21_717450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_717450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_717450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_717450 prefixEnd_717450 := by exact prefixLift 717450
  have htrace : WordTrace (prefixWord ++ tailWord_717450) baseStart_717450 baseEnd_717450 := by
    simpa [prefixWord, tailWord_717450, baseEnd_717450] using wordTrace_append hprefix tailTrace_717450
  have hstable : (prefixWord ++ tailWord_717450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717450).length < 2 ^ (prefixWord ++ tailWord_717450).sum := by decide
  have hdescent : baseEnd_717450 < baseStart_717450 := by decide
  rcases family_descends (prefixWord ++ tailWord_717450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717495 : List Nat := [1, 1, 3, 1, 7, 1, 2, 5]
def baseStart_717495 : Nat := 118140960795 + 717495 * 2 ^ 59
def prefixEnd_717495 : Nat := 4983230072969 + 3 ^ 40 * 717495 * 2
def baseEnd_717495 : Nat := 54580711436707486105601

theorem tailTrace_717495 : CollatzResearch.WordTrace tailWord_717495 prefixEnd_717495 54580711436707486105601 := by
  unfold tailWord_717495
  simp only [CollatzResearch.WordTrace]
  refine ⟨26169192535645628235329939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17446128357097085490219959 26169192535645628235329939)
  ·
    refine ⟨39253788803468442352994909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26169192535645628235329939 39253788803468442352994909)
    ·
      refine ⟨14720170801300665882373091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39253788803468442352994909 14720170801300665882373091)
      ·
        refine ⟨22080256201950998823559637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14720170801300665882373091 22080256201950998823559637)
        ·
          refine ⟨517506004733226534927179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 22080256201950998823559637 517506004733226534927179)
          ·
            refine ⟨776259007099839802390769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517506004733226534927179 776259007099839802390769)
            ·
              refine ⟨582194255324879851793077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 776259007099839802390769 582194255324879851793077)
              ·
                refine ⟨54580711436707486105601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 582194255324879851793077 54580711436707486105601)
                ·
                  rfl

theorem cell21_717495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 5].length) (baseStart_717495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_717495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_717495 prefixEnd_717495 := by exact prefixLift 717495
  have htrace : WordTrace (prefixWord ++ tailWord_717495) baseStart_717495 baseEnd_717495 := by
    simpa [prefixWord, tailWord_717495, baseEnd_717495] using wordTrace_append hprefix tailTrace_717495
  have hstable : (prefixWord ++ tailWord_717495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717495).length < 2 ^ (prefixWord ++ tailWord_717495).sum := by decide
  have hdescent : baseEnd_717495 < baseStart_717495 := by decide
  rcases family_descends (prefixWord ++ tailWord_717495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717537 : List Nat := [1, 2, 3, 1, 4, 2, 2, 6]
def baseStart_717537 : Nat := 118140960795 + 717537 * 2 ^ 59
def prefixEnd_717537 : Nat := 4983230072969 + 3 ^ 40 * 717537 * 2
def baseEnd_717537 : Nat := 54583906427446572872239

theorem tailTrace_717537 : CollatzResearch.WordTrace tailWord_717537 prefixEnd_717537 54583906427446572872239 := by
  unfold tailWord_717537
  simp only [CollatzResearch.WordTrace]
  refine ⟨26170724401493469408358865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17447149600995646272239243 26170724401493469408358865)
  ·
    refine ⟨19628043301120102056269149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26170724401493469408358865 19628043301120102056269149)
    ·
      refine ⟨7360516237920038271100931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19628043301120102056269149 7360516237920038271100931)
      ·
        refine ⟨11040774356880057406651397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7360516237920038271100931 11040774356880057406651397)
        ·
          refine ⟨2070145191915010763747137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11040774356880057406651397 2070145191915010763747137)
          ·
            refine ⟨1552608893936258072810353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2070145191915010763747137 1552608893936258072810353)
            ·
              refine ⟨1164456670452193554607765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1552608893936258072810353 1164456670452193554607765)
              ·
                refine ⟨54583906427446572872239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1164456670452193554607765 54583906427446572872239)
                ·
                  rfl

theorem cell21_717537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 6].length) (baseStart_717537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_717537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_717537 prefixEnd_717537 := by exact prefixLift 717537
  have htrace : WordTrace (prefixWord ++ tailWord_717537) baseStart_717537 baseEnd_717537 := by
    simpa [prefixWord, tailWord_717537, baseEnd_717537] using wordTrace_append hprefix tailTrace_717537
  have hstable : (prefixWord ++ tailWord_717537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717537).length < 2 ^ (prefixWord ++ tailWord_717537).sum := by decide
  have hdescent : baseEnd_717537 < baseStart_717537 := by decide
  rcases family_descends (prefixWord ++ tailWord_717537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717540 : List Nat := [2, 3, 1, 1, 1, 6, 2, 1, 4]
def baseStart_717540 : Nat := 118140960795 + 717540 * 2 ^ 59
def prefixEnd_717540 : Nat := 4983230072969 + 3 ^ 40 * 717540 * 2
def baseEnd_717540 : Nat := 163752403923212380066711

theorem tailTrace_717540 : CollatzResearch.WordTrace tailWord_717540 prefixEnd_717540 163752403923212380066711 := by
  unfold tailWord_717540
  simp only [CollatzResearch.WordTrace]
  refine ⟨13085416910241300460359037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17447222546988400613812049 13085416910241300460359037)
  ·
    refine ⟨4907031341340487672634639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13085416910241300460359037 4907031341340487672634639)
    ·
      refine ⟨7360547012010731508951959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4907031341340487672634639 7360547012010731508951959)
      ·
        refine ⟨11040820518016097263427939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7360547012010731508951959 11040820518016097263427939)
        ·
          refine ⟨16561230777024145895141909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11040820518016097263427939 16561230777024145895141909)
          ·
            refine ⟨776307692673006838834777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16561230777024145895141909 776307692673006838834777)
            ·
              refine ⟨582230769504755129126083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 776307692673006838834777 582230769504755129126083)
              ·
                refine ⟨873346154257132693689125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582230769504755129126083 873346154257132693689125)
                ·
                  refine ⟨163752403923212380066711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 873346154257132693689125 163752403923212380066711)
                  ·
                    rfl

theorem cell21_717540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_717540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_717540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_717540 prefixEnd_717540 := by exact prefixLift 717540
  have htrace : WordTrace (prefixWord ++ tailWord_717540) baseStart_717540 baseEnd_717540 := by
    simpa [prefixWord, tailWord_717540, baseEnd_717540] using wordTrace_append hprefix tailTrace_717540
  have hstable : (prefixWord ++ tailWord_717540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717540).length < 2 ^ (prefixWord ++ tailWord_717540).sum := by decide
  have hdescent : baseEnd_717540 < baseStart_717540 := by decide
  rcases family_descends (prefixWord ++ tailWord_717540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717585 : List Nat := [1, 2, 2, 1, 1, 3, 6, 2, 3]
def baseStart_717585 : Nat := 118140960795 + 717585 * 2 ^ 59
def prefixEnd_717585 : Nat := 4983230072969 + 3 ^ 40 * 717585 * 2
def baseEnd_717585 : Nat := 163762673536302301816619

theorem tailTrace_717585 : CollatzResearch.WordTrace tailWord_717585 prefixEnd_717585 163762673536302301816619 := by
  unfold tailWord_717585
  simp only [CollatzResearch.WordTrace]
  refine ⟨26172475105319573606106209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17448316736879715737404139 26172475105319573606106209)
  ·
    refine ⟨19629356328989680204579657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26172475105319573606106209 19629356328989680204579657)
    ·
      refine ⟨14722017246742260153434743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19629356328989680204579657 14722017246742260153434743)
      ·
        refine ⟨22083025870113390230152115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14722017246742260153434743 22083025870113390230152115)
        ·
          refine ⟨33124538805170085345228173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22083025870113390230152115 33124538805170085345228173)
          ·
            refine ⟨12421702051938782004460565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33124538805170085345228173 12421702051938782004460565)
            ·
              refine ⟨582267283684630406459089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12421702051938782004460565 582267283684630406459089)
              ·
                refine ⟨436700462763472804844317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 582267283684630406459089 436700462763472804844317)
                ·
                  refine ⟨163762673536302301816619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 436700462763472804844317 163762673536302301816619)
                  ·
                    rfl

theorem cell21_717585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 3].length) (baseStart_717585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_717585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_717585 prefixEnd_717585 := by exact prefixLift 717585
  have htrace : WordTrace (prefixWord ++ tailWord_717585) baseStart_717585 baseEnd_717585 := by
    simpa [prefixWord, tailWord_717585, baseEnd_717585] using wordTrace_append hprefix tailTrace_717585
  have hstable : (prefixWord ++ tailWord_717585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717585).length < 2 ^ (prefixWord ++ tailWord_717585).sum := by decide
  have hdescent : baseEnd_717585 < baseStart_717585 := by decide
  rcases family_descends (prefixWord ++ tailWord_717585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717633 : List Nat := [1, 2, 5, 3, 1, 2, 1, 2, 4]
def baseStart_717633 : Nat := 118140960795 + 717633 * 2 ^ 59
def prefixEnd_717633 : Nat := 4983230072969 + 3 ^ 40 * 717633 * 2
def baseEnd_717633 : Nat := 163773627790264885016521

theorem tailTrace_717633 : CollatzResearch.WordTrace tailWord_717633 prefixEnd_717633 163773627790264885016521 := by
  unfold tailWord_717633
  simp only [CollatzResearch.WordTrace]
  refine ⟨26174225809145677803853553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17449483872763785202569035 26174225809145677803853553)
  ·
    refine ⟨19630669356859258352890165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26174225809145677803853553 19630669356859258352890165)
    ·
      refine ⟨1840375252205555470583453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19630669356859258352890165 1840375252205555470583453)
      ·
        refine ⟨690140719577083301468795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1840375252205555470583453 690140719577083301468795)
        ·
          refine ⟨1035211079365624952203193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690140719577083301468795 1035211079365624952203193)
          ·
            refine ⟨776408309524218714152395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1035211079365624952203193 776408309524218714152395)
            ·
              refine ⟨1164612464286328071228593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776408309524218714152395 1164612464286328071228593)
              ·
                refine ⟨873459348214746053421445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1164612464286328071228593 873459348214746053421445)
                ·
                  refine ⟨163773627790264885016521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 873459348214746053421445 163773627790264885016521)
                  ·
                    rfl

theorem cell21_717633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_717633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_717633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_717633 prefixEnd_717633 := by exact prefixLift 717633
  have htrace : WordTrace (prefixWord ++ tailWord_717633) baseStart_717633 baseEnd_717633 := by
    simpa [prefixWord, tailWord_717633, baseEnd_717633] using wordTrace_append hprefix tailTrace_717633
  have hstable : (prefixWord ++ tailWord_717633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717633).length < 2 ^ (prefixWord ++ tailWord_717633).sum := by decide
  have hdescent : baseEnd_717633 < baseStart_717633 := by decide
  rcases family_descends (prefixWord ++ tailWord_717633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717644 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 5]
def baseStart_717644 : Nat := 118140960795 + 717644 * 2 ^ 59
def prefixEnd_717644 : Nat := 4983230072969 + 3 ^ 40 * 717644 * 2
def baseEnd_717644 : Nat := 163776138140131310333165

theorem tailTrace_717644 : CollatzResearch.WordTrace tailWord_717644 prefixEnd_717644 163776138140131310333165 := by
  unfold tailWord_717644
  simp only [CollatzResearch.WordTrace]
  refine ⟨13087313506052913341251993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17449751341403884455002657 13087313506052913341251993)
  ·
    refine ⟨9815485129539685005938995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13087313506052913341251993 9815485129539685005938995)
    ·
      refine ⟨14723227694309527508908493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9815485129539685005938995 14723227694309527508908493)
      ·
        refine ⟨5521210385366072815840685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14723227694309527508908493 5521210385366072815840685)
        ·
          refine ⟨2070453894512277305940257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5521210385366072815840685 2070453894512277305940257)
          ·
            refine ⟨1552840420884207979455193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2070453894512277305940257 1552840420884207979455193)
            ·
              refine ⟨1164630315663155984591395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1552840420884207979455193 1164630315663155984591395)
              ·
                refine ⟨1746945473494733976887093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164630315663155984591395 1746945473494733976887093)
                ·
                  refine ⟨163776138140131310333165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1746945473494733976887093 163776138140131310333165)
                  ·
                    rfl

theorem cell21_717644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_717644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_717644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_717644 prefixEnd_717644 := by exact prefixLift 717644
  have htrace : WordTrace (prefixWord ++ tailWord_717644) baseStart_717644 baseEnd_717644 := by
    simpa [prefixWord, tailWord_717644, baseEnd_717644] using wordTrace_append hprefix tailTrace_717644
  have hstable : (prefixWord ++ tailWord_717644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717644).length < 2 ^ (prefixWord ++ tailWord_717644).sum := by decide
  have hdescent : baseEnd_717644 < baseStart_717644 := by decide
  rcases family_descends (prefixWord ++ tailWord_717644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717793 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 6]
def baseStart_717793 : Nat := 118140960795 + 717793 * 2 ^ 59
def prefixEnd_717793 : Nat := 4983230072969 + 3 ^ 40 * 717793 * 2
def baseEnd_717793 : Nat := 163810141970140162349527

theorem tailTrace_717793 : CollatzResearch.WordTrace tailWord_717793 prefixEnd_717793 163810141970140162349527 := by
  unfold tailWord_717793
  simp only [CollatzResearch.WordTrace]
  refine ⟨26180061488566025129678033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17453374325710683419785355 26180061488566025129678033)
  ·
    refine ⟨19635046116424518847258525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26180061488566025129678033 19635046116424518847258525)
    ·
      refine ⟨7363142293659194567721947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19635046116424518847258525 7363142293659194567721947)
      ·
        refine ⟨11044713440488791851582921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7363142293659194567721947 11044713440488791851582921)
        ·
          refine ⟨8283535080366593888687191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11044713440488791851582921 8283535080366593888687191)
          ·
            refine ⟨12425302620549890833030787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8283535080366593888687191 12425302620549890833030787)
            ·
              refine ⟨18637953930824836249546181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12425302620549890833030787 18637953930824836249546181)
              ·
                refine ⟨3494616362029656796789909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18637953930824836249546181 3494616362029656796789909)
                ·
                  refine ⟨163810141970140162349527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3494616362029656796789909 163810141970140162349527)
                  ·
                    rfl

theorem cell21_717793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_717793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_717793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_717793 prefixEnd_717793 := by exact prefixLift 717793
  have htrace : WordTrace (prefixWord ++ tailWord_717793) baseStart_717793 baseEnd_717793 := by
    simpa [prefixWord, tailWord_717793, baseEnd_717793] using wordTrace_append hprefix tailTrace_717793
  have hstable : (prefixWord ++ tailWord_717793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717793).length < 2 ^ (prefixWord ++ tailWord_717793).sum := by decide
  have hdescent : baseEnd_717793 < baseStart_717793 := by decide
  rcases family_descends (prefixWord ++ tailWord_717793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717914 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 9]
def baseStart_717914 : Nat := 118140960795 + 717914 * 2 ^ 59
def prefixEnd_717914 : Nat := 4983230072969 + 3 ^ 40 * 717914 * 2
def baseEnd_717914 : Nat := 163837755818670840832613

theorem tailTrace_717914 : CollatzResearch.WordTrace tailWord_717914 prefixEnd_717914 163837755818670840832613 := by
  unfold tailWord_717914
  simp only [CollatzResearch.WordTrace]
  refine ⟨6546118680281915698708199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17456316480751775196555197 6546118680281915698708199)
  ·
    refine ⟨9819178020422873548062299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6546118680281915698708199 9819178020422873548062299)
    ·
      refine ⟨14728767030634310322093449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9819178020422873548062299 14728767030634310322093449)
      ·
        refine ⟨11046575272975732741570087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14728767030634310322093449 11046575272975732741570087)
        ·
          refine ⟨16569862909463599112355131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11046575272975732741570087 16569862909463599112355131)
          ·
            refine ⟨24854794364195398668532697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16569862909463599112355131 24854794364195398668532697)
            ·
              refine ⟨18641095773146549001399523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24854794364195398668532697 18641095773146549001399523)
              ·
                refine ⟨27961643659719823502099285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18641095773146549001399523 27961643659719823502099285)
                ·
                  refine ⟨163837755818670840832613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27961643659719823502099285 163837755818670840832613)
                  ·
                    rfl

theorem cell21_717914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_717914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_717914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_717914 prefixEnd_717914 := by exact prefixLift 717914
  have htrace : WordTrace (prefixWord ++ tailWord_717914) baseStart_717914 baseEnd_717914 := by
    simpa [prefixWord, tailWord_717914, baseEnd_717914] using wordTrace_append hprefix tailTrace_717914
  have hstable : (prefixWord ++ tailWord_717914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717914).length < 2 ^ (prefixWord ++ tailWord_717914).sum := by decide
  have hdescent : baseEnd_717914 < baseStart_717914 := by decide
  rcases family_descends (prefixWord ++ tailWord_717914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717917 : List Nat := [1, 4, 4, 1, 2, 9]
def baseStart_717917 : Nat := 118140960795 + 717917 * 2 ^ 59
def prefixEnd_717917 : Nat := 4983230072969 + 3 ^ 40 * 717917 * 2
def baseEnd_717917 : Nat := 6068090387390500084541

theorem tailTrace_717917 : CollatzResearch.WordTrace tailWord_717917 prefixEnd_717917 6068090387390500084541 := by
  unfold tailWord_717917
  simp only [CollatzResearch.WordTrace]
  refine ⟨26184584140116794307192005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17456389426744529538128003 26184584140116794307192005)
  ·
    refine ⟨4909609526271898932598501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26184584140116794307192005 4909609526271898932598501)
    ·
      refine ⟨920551786175981049862219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4909609526271898932598501 920551786175981049862219)
      ·
        refine ⟨1380827679263971574793329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 920551786175981049862219 1380827679263971574793329)
        ·
          refine ⟨1035620759447978681094997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1380827679263971574793329 1035620759447978681094997)
          ·
            refine ⟨6068090387390500084541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1035620759447978681094997 6068090387390500084541)
            ·
              rfl

theorem cell21_717917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 9].length) (baseStart_717917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_717917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_717917 prefixEnd_717917 := by exact prefixLift 717917
  have htrace : WordTrace (prefixWord ++ tailWord_717917) baseStart_717917 baseEnd_717917 := by
    simpa [prefixWord, tailWord_717917, baseEnd_717917] using wordTrace_append hprefix tailTrace_717917
  have hstable : (prefixWord ++ tailWord_717917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717917).length < 2 ^ (prefixWord ++ tailWord_717917).sum := by decide
  have hdescent : baseEnd_717917 < baseStart_717917 := by decide
  rcases family_descends (prefixWord ++ tailWord_717917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717976 : List Nat := [2, 1, 2, 4, 2, 2, 8]
def baseStart_717976 : Nat := 118140960795 + 717976 * 2 ^ 59
def prefixEnd_717976 : Nat := 4983230072969 + 3 ^ 40 * 717976 * 2
def baseEnd_717976 : Nat := 18205767229263612311017

theorem tailTrace_717976 : CollatzResearch.WordTrace tailWord_717976 prefixEnd_717976 18205767229263612311017 := by
  unfold tailWord_717976
  simp only [CollatzResearch.WordTrace]
  refine ⟨13093368023451523691794891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17457824031268698255726521 13093368023451523691794891)
  ·
    refine ⟨19640052035177285537692337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13093368023451523691794891 19640052035177285537692337)
    ·
      refine ⟨14730039026382964153269253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19640052035177285537692337 14730039026382964153269253)
      ·
        refine ⟨2761882317446805778737985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14730039026382964153269253 2761882317446805778737985)
        ·
          refine ⟨2071411738085104334053489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2761882317446805778737985 2071411738085104334053489)
          ·
            refine ⟨1553558803563828250540117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2071411738085104334053489 1553558803563828250540117)
            ·
              refine ⟨18205767229263612311017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1553558803563828250540117 18205767229263612311017)
              ·
                rfl

theorem cell21_717976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 8].length) (baseStart_717976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_717976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_717976 prefixEnd_717976 := by exact prefixLift 717976
  have htrace : WordTrace (prefixWord ++ tailWord_717976) baseStart_717976 baseEnd_717976 := by
    simpa [prefixWord, tailWord_717976, baseEnd_717976] using wordTrace_append hprefix tailTrace_717976
  have hstable : (prefixWord ++ tailWord_717976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717976).length < 2 ^ (prefixWord ++ tailWord_717976).sum := by decide
  have hdescent : baseEnd_717976 < baseStart_717976 := by decide
  rcases family_descends (prefixWord ++ tailWord_717976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718024 : List Nat := [2, 1, 3, 1, 2, 1, 5, 3, 3]
def baseStart_718024 : Nat := 118140960795 + 718024 * 2 ^ 59
def prefixEnd_718024 : Nat := 4983230072969 + 3 ^ 40 * 718024 * 2
def baseEnd_718024 : Nat := 163862859317335093999055

theorem tailTrace_718024 : CollatzResearch.WordTrace tailWord_718024 prefixEnd_718024 163862859317335093999055 := by
  unfold tailWord_718024
  simp only [CollatzResearch.WordTrace]
  refine ⟨13094243375364575790668563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17458991167152767720891417 13094243375364575790668563)
  ·
    refine ⟨19641365063046863686002845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13094243375364575790668563 19641365063046863686002845)
    ·
      refine ⟨7365511898642573882251067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19641365063046863686002845 7365511898642573882251067)
      ·
        refine ⟨11048267847963860823376601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7365511898642573882251067 11048267847963860823376601)
        ·
          refine ⟨8286200885972895617532451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11048267847963860823376601 8286200885972895617532451)
          ·
            refine ⟨12429301328959343426298677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8286200885972895617532451 12429301328959343426298677)
            ·
              refine ⟨1165246999589938446215501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12429301328959343426298677 1165246999589938446215501)
              ·
                refine ⟨436967624846226917330813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1165246999589938446215501 436967624846226917330813)
                ·
                  refine ⟨163862859317335093999055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 436967624846226917330813 163862859317335093999055)
                  ·
                    rfl

theorem cell21_718024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 3].length) (baseStart_718024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_718024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_718024 prefixEnd_718024 := by exact prefixLift 718024
  have htrace : WordTrace (prefixWord ++ tailWord_718024) baseStart_718024 baseEnd_718024 := by
    simpa [prefixWord, tailWord_718024, baseEnd_718024] using wordTrace_append hprefix tailTrace_718024
  have hstable : (prefixWord ++ tailWord_718024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718024).length < 2 ^ (prefixWord ++ tailWord_718024).sum := by decide
  have hdescent : baseEnd_718024 < baseStart_718024 := by decide
  rcases family_descends (prefixWord ++ tailWord_718024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718055 : List Nat := [1, 1, 5, 3, 2, 1, 1, 3, 4]
def baseStart_718055 : Nat := 118140960795 + 718055 * 2 ^ 59
def prefixEnd_718055 : Nat := 4983230072969 + 3 ^ 40 * 718055 * 2
def baseEnd_718055 : Nat := 163869933939685928982325

theorem tailTrace_718055 : CollatzResearch.WordTrace tailWord_718055 prefixEnd_718055 163869933939685928982325 := by
  unfold tailWord_718055
  simp only [CollatzResearch.WordTrace]
  refine ⟨26189617413616843875715619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17459744942411229250477079 26189617413616843875715619)
  ·
    refine ⟨39284426120425265813573429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26189617413616843875715619 39284426120425265813573429)
    ·
      refine ⟨3682914948789868670022509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39284426120425265813573429 3682914948789868670022509)
      ·
        refine ⟨1381093105796200751258441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3682914948789868670022509 1381093105796200751258441)
        ·
          refine ⟨1035819829347150563443831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1381093105796200751258441 1035819829347150563443831)
          ·
            refine ⟨1553729744020725845165747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035819829347150563443831 1553729744020725845165747)
            ·
              refine ⟨2330594616031088767748621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1553729744020725845165747 2330594616031088767748621)
              ·
                refine ⟨873972981011658287905733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2330594616031088767748621 873972981011658287905733)
                ·
                  refine ⟨163869933939685928982325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 873972981011658287905733 163869933939685928982325)
                  ·
                    rfl

theorem cell21_718055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 4].length) (baseStart_718055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_718055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_718055 prefixEnd_718055 := by exact prefixLift 718055
  have htrace : WordTrace (prefixWord ++ tailWord_718055) baseStart_718055 baseEnd_718055 := by
    simpa [prefixWord, tailWord_718055, baseEnd_718055] using wordTrace_append hprefix tailTrace_718055
  have hstable : (prefixWord ++ tailWord_718055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718055).length < 2 ^ (prefixWord ++ tailWord_718055).sum := by decide
  have hdescent : baseEnd_718055 < baseStart_718055 := by decide
  rcases family_descends (prefixWord ++ tailWord_718055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718128 : List Nat := [2, 1, 1, 1, 2, 2, 7, 5]
def baseStart_718128 : Nat := 118140960795 + 718128 * 2 ^ 59
def prefixEnd_718128 : Nat := 4983230072969 + 3 ^ 40 * 718128 * 2
def baseEnd_718128 : Nat := 54628864511418008088503

theorem tailTrace_718128 : CollatzResearch.WordTrace tailWord_718128 prefixEnd_718128 54628864511418008088503 := by
  unfold tailWord_718128
  simp only [CollatzResearch.WordTrace]
  refine ⟨13096139971176188671561519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17461519961568251562082025 13096139971176188671561519)
  ·
    refine ⟨19644209956764283007342279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13096139971176188671561519 19644209956764283007342279)
    ·
      refine ⟨29466314935146424511013419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19644209956764283007342279 29466314935146424511013419)
      ·
        refine ⟨44199472402719636766520129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29466314935146424511013419 44199472402719636766520129)
        ·
          refine ⟨33149604302039727574890097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44199472402719636766520129 33149604302039727574890097)
          ·
            refine ⟨24862203226529795681167573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33149604302039727574890097 24862203226529795681167573)
            ·
              refine ⟨582707888121792086277365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 24862203226529795681167573 582707888121792086277365)
              ·
                refine ⟨54628864511418008088503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 582707888121792086277365 54628864511418008088503)
                ·
                  rfl

theorem cell21_718128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 5].length) (baseStart_718128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_718128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_718128 prefixEnd_718128 := by exact prefixLift 718128
  have htrace : WordTrace (prefixWord ++ tailWord_718128) baseStart_718128 baseEnd_718128 := by
    simpa [prefixWord, tailWord_718128, baseEnd_718128] using wordTrace_append hprefix tailTrace_718128
  have hstable : (prefixWord ++ tailWord_718128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718128).length < 2 ^ (prefixWord ++ tailWord_718128).sum := by decide
  have hdescent : baseEnd_718128 < baseStart_718128 := by decide
  rcases family_descends (prefixWord ++ tailWord_718128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718148 : List Nat := [2, 3, 4, 1, 1, 3, 1, 2, 4]
def baseStart_718148 : Nat := 118140960795 + 718148 * 2 ^ 59
def prefixEnd_718148 : Nat := 4983230072969 + 3 ^ 40 * 718148 * 2
def baseEnd_718148 : Nat := 163891157806738433932135

theorem tailTrace_718148 : CollatzResearch.WordTrace tailWord_718148 prefixEnd_718148 163891157806738433932135 := by
  unfold tailWord_718148
  simp only [CollatzResearch.WordTrace]
  refine ⟨13096504701139960379425549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17462006268186613839234065 13096504701139960379425549)
  ·
    refine ⟨4911189262927485142284581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13096504701139960379425549 4911189262927485142284581)
    ·
      refine ⟨920847986798903464178359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4911189262927485142284581 920847986798903464178359)
      ·
        refine ⟨1381271980198355196267539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 920847986798903464178359 1381271980198355196267539)
        ·
          refine ⟨2071907970297532794401309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1381271980198355196267539 2071907970297532794401309)
          ·
            refine ⟨776965488861574797900491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2071907970297532794401309 776965488861574797900491)
            ·
              refine ⟨1165448233292362196850737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776965488861574797900491 1165448233292362196850737)
              ·
                refine ⟨874086174969271647638053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1165448233292362196850737 874086174969271647638053)
                ·
                  refine ⟨163891157806738433932135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 874086174969271647638053 163891157806738433932135)
                  ·
                    rfl

theorem cell21_718148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_718148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_718148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_718148 prefixEnd_718148 := by exact prefixLift 718148
  have htrace : WordTrace (prefixWord ++ tailWord_718148) baseStart_718148 baseEnd_718148 := by
    simpa [prefixWord, tailWord_718148, baseEnd_718148] using wordTrace_append hprefix tailTrace_718148
  have hstable : (prefixWord ++ tailWord_718148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718148).length < 2 ^ (prefixWord ++ tailWord_718148).sum := by decide
  have hdescent : baseEnd_718148 < baseStart_718148 := by decide
  rcases family_descends (prefixWord ++ tailWord_718148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718370 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 7]
def baseStart_718370 : Nat := 118140960795 + 718370 * 2 ^ 59
def prefixEnd_718370 : Nat := 4983230072969 + 3 ^ 40 * 718370 * 2
def baseEnd_718370 : Nat := 163941821231315381231681

theorem tailTrace_718370 : CollatzResearch.WordTrace tailWord_718370 prefixEnd_718370 163941821231315381231681 := by
  unfold tailWord_718370
  simp only [CollatzResearch.WordTrace]
  refine ⟨6550276601868913168358141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17467404271650435115621709 6550276601868913168358141)
  ·
    refine ⟨2456353725700842438134303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6550276601868913168358141 2456353725700842438134303)
    ·
      refine ⟨3684530588551263657201455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2456353725700842438134303 3684530588551263657201455)
      ·
        refine ⟨5526795882826895485802183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3684530588551263657201455 5526795882826895485802183)
        ·
          refine ⟨8290193824240343228703275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5526795882826895485802183 8290193824240343228703275)
          ·
            refine ⟨12435290736360514843054913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8290193824240343228703275 12435290736360514843054913)
            ·
              refine ⟨9326468052270386132291185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12435290736360514843054913 9326468052270386132291185)
              ·
                refine ⟨6994851039202789599218389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9326468052270386132291185 6994851039202789599218389)
                ·
                  refine ⟨163941821231315381231681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6994851039202789599218389 163941821231315381231681)
                  ·
                    rfl

theorem cell21_718370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_718370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_718370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_718370 prefixEnd_718370 := by exact prefixLift 718370
  have htrace : WordTrace (prefixWord ++ tailWord_718370) baseStart_718370 baseEnd_718370 := by
    simpa [prefixWord, tailWord_718370, baseEnd_718370] using wordTrace_append hprefix tailTrace_718370
  have hstable : (prefixWord ++ tailWord_718370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718370).length < 2 ^ (prefixWord ++ tailWord_718370).sum := by decide
  have hdescent : baseEnd_718370 < baseStart_718370 := by decide
  rcases family_descends (prefixWord ++ tailWord_718370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718387 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 5]
def baseStart_718387 : Nat := 118140960795 + 718387 * 2 ^ 59
def prefixEnd_718387 : Nat := 4983230072969 + 3 ^ 40 * 718387 * 2
def baseEnd_718387 : Nat := 163945700862927129448313

theorem tailTrace_718387 : CollatzResearch.WordTrace tailWord_718387 prefixEnd_718387 163945700862927129448313 := by
  unfold tailWord_718387
  simp only [CollatzResearch.WordTrace]
  refine ⟨26201726448414064576801415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17467817632276043051200943 26201726448414064576801415)
  ·
    refine ⟨39302589672621096865202123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26201726448414064576801415 39302589672621096865202123)
    ·
      refine ⟨58953884508931645297803185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39302589672621096865202123 58953884508931645297803185)
      ·
        refine ⟨44215413381698733973352389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58953884508931645297803185 44215413381698733973352389)
        ·
          refine ⟨8290390009068512620003573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44215413381698733973352389 8290390009068512620003573)
          ·
            refine ⟨777224063350173058125335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8290390009068512620003573 777224063350173058125335)
            ·
              refine ⟨1165836095025259587188003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777224063350173058125335 1165836095025259587188003)
              ·
                refine ⟨1748754142537889380782005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165836095025259587188003 1748754142537889380782005)
                ·
                  refine ⟨163945700862927129448313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1748754142537889380782005 163945700862927129448313)
                  ·
                    rfl

theorem cell21_718387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 5].length) (baseStart_718387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_718387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_718387 prefixEnd_718387 := by exact prefixLift 718387
  have htrace : WordTrace (prefixWord ++ tailWord_718387) baseStart_718387 baseEnd_718387 := by
    simpa [prefixWord, tailWord_718387, baseEnd_718387] using wordTrace_append hprefix tailTrace_718387
  have hstable : (prefixWord ++ tailWord_718387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718387).length < 2 ^ (prefixWord ++ tailWord_718387).sum := by decide
  have hdescent : baseEnd_718387 < baseStart_718387 := by decide
  rcases family_descends (prefixWord ++ tailWord_718387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718460 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 8]
def baseStart_718460 : Nat := 118140960795 + 718460 * 2 ^ 59
def prefixEnd_718460 : Nat := 4983230072969 + 3 ^ 40 * 718460 * 2
def baseEnd_718460 : Nat := 163962360457495224731497

theorem tailTrace_718460 : CollatzResearch.WordTrace tailWord_718460 prefixEnd_718460 163962360457495224731497 := by
  unfold tailWord_718460
  simp only [CollatzResearch.WordTrace]
  refine ⟨13102194488574799022104417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17469592651433065362805889 13102194488574799022104417)
  ·
    refine ⟨9826645866431099266578313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13102194488574799022104417 9826645866431099266578313)
    ·
      refine ⟨7369984399823324449933735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9826645866431099266578313 7369984399823324449933735)
      ·
        refine ⟨11054976599734986674900603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7369984399823324449933735 11054976599734986674900603)
        ·
          refine ⟨16582464899602480012350905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11054976599734986674900603 16582464899602480012350905)
          ·
            refine ⟨12436848674701860009263179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16582464899602480012350905 12436848674701860009263179)
            ·
              refine ⟨18655273012052790013894769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12436848674701860009263179 18655273012052790013894769)
              ·
                refine ⟨13991454759039592510421077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18655273012052790013894769 13991454759039592510421077)
                ·
                  refine ⟨163962360457495224731497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13991454759039592510421077 163962360457495224731497)
                  ·
                    rfl

theorem cell21_718460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_718460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_718460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_718460 prefixEnd_718460 := by exact prefixLift 718460
  have htrace : WordTrace (prefixWord ++ tailWord_718460) baseStart_718460 baseEnd_718460 := by
    simpa [prefixWord, tailWord_718460, baseEnd_718460] using wordTrace_append hprefix tailTrace_718460
  have hstable : (prefixWord ++ tailWord_718460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718460).length < 2 ^ (prefixWord ++ tailWord_718460).sum := by decide
  have hdescent : baseEnd_718460 < baseStart_718460 := by decide
  rcases family_descends (prefixWord ++ tailWord_718460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718494 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_718494 : Nat := 118140960795 + 718494 * 2 ^ 59
def prefixEnd_718494 : Nat := 4983230072969 + 3 ^ 40 * 718494 * 2
def baseEnd_718494 : Nat := 163970119720718721164761

theorem tailTrace_718494 : CollatzResearch.WordTrace tailWord_718494 prefixEnd_718494 163970119720718721164761 := by
  unfold tailWord_718494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3275703632378302731368317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17470419372684281233964357 3275703632378302731368317)
  ·
    refine ⟨1228388862141863524263119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3275703632378302731368317 1228388862141863524263119)
    ·
      refine ⟨1842583293212795286394679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1228388862141863524263119 1842583293212795286394679)
      ·
        refine ⟨2763874939819192929592019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1842583293212795286394679 2763874939819192929592019)
        ·
          refine ⟨4145812409728789394388029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2763874939819192929592019 4145812409728789394388029)
          ·
            refine ⟨1554679653648296022895511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4145812409728789394388029 1554679653648296022895511)
            ·
              refine ⟨2332019480472444034343267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554679653648296022895511 2332019480472444034343267)
              ·
                refine ⟨3498029220708666051514901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2332019480472444034343267 3498029220708666051514901)
                ·
                  refine ⟨163970119720718721164761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3498029220708666051514901 163970119720718721164761)
                  ·
                    rfl

theorem cell21_718494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_718494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_718494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_718494 prefixEnd_718494 := by exact prefixLift 718494
  have htrace : WordTrace (prefixWord ++ tailWord_718494) baseStart_718494 baseEnd_718494 := by
    simpa [prefixWord, tailWord_718494, baseEnd_718494] using wordTrace_append hprefix tailTrace_718494
  have hstable : (prefixWord ++ tailWord_718494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718494).length < 2 ^ (prefixWord ++ tailWord_718494).sum := by decide
  have hdescent : baseEnd_718494 < baseStart_718494 := by decide
  rcases family_descends (prefixWord ++ tailWord_718494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718522 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 5]
def baseStart_718522 : Nat := 118140960795 + 718522 * 2 ^ 59
def prefixEnd_718522 : Nat := 4983230072969 + 3 ^ 40 * 718522 * 2
def baseEnd_718522 : Nat := 163976509702196894698037

theorem tailTrace_718522 : CollatzResearch.WordTrace tailWord_718522 prefixEnd_718522 163976509702196894698037 := by
  unfold tailWord_718522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6551662575731245658241455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17471100201949988421977213 6551662575731245658241455)
  ·
    refine ⟨9827493863596868487362183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6551662575731245658241455 9827493863596868487362183)
    ·
      refine ⟨14741240795395302731043275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9827493863596868487362183 14741240795395302731043275)
      ·
        refine ⟨22111861193092954096564913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14741240795395302731043275 22111861193092954096564913)
        ·
          refine ⟨16583895894819715572423685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22111861193092954096564913 16583895894819715572423685)
          ·
            refine ⟨3109480480278696669829441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16583895894819715572423685 3109480480278696669829441)
            ·
              refine ⟨2332110360209022502372081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3109480480278696669829441 2332110360209022502372081)
              ·
                refine ⟨1749082770156766876779061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2332110360209022502372081 1749082770156766876779061)
                ·
                  refine ⟨163976509702196894698037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1749082770156766876779061 163976509702196894698037)
                  ·
                    rfl

theorem cell21_718522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_718522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_718522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_718522 prefixEnd_718522 := by exact prefixLift 718522
  have htrace : WordTrace (prefixWord ++ tailWord_718522) baseStart_718522 baseEnd_718522 := by
    simpa [prefixWord, tailWord_718522, baseEnd_718522] using wordTrace_append hprefix tailTrace_718522
  have hstable : (prefixWord ++ tailWord_718522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718522).length < 2 ^ (prefixWord ++ tailWord_718522).sum := by decide
  have hdescent : baseEnd_718522 < baseStart_718522 := by decide
  rcases family_descends (prefixWord ++ tailWord_718522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718536 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 8]
def baseStart_718536 : Nat := 118140960795 + 718536 * 2 ^ 59
def prefixEnd_718536 : Nat := 4983230072969 + 3 ^ 40 * 718536 * 2
def baseEnd_718536 : Nat := 163979704692935981464675

theorem tailTrace_718536 : CollatzResearch.WordTrace tailWord_718536 prefixEnd_718536 163979704692935981464675 := by
  unfold tailWord_718536
  simp only [CollatzResearch.WordTrace]
  refine ⟨13103580462437131511987731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17471440616582842015983641 13103580462437131511987731)
  ·
    refine ⟨19655370693655697267981597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13103580462437131511987731 19655370693655697267981597)
    ·
      refine ⟨7370764010120886475493099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19655370693655697267981597 7370764010120886475493099)
      ·
        refine ⟨11056146015181329713239649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7370764010120886475493099 11056146015181329713239649)
        ·
          refine ⟨8292109511385997284929737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11056146015181329713239649 8292109511385997284929737)
          ·
            refine ⟨6219082133539497963697303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8292109511385997284929737 6219082133539497963697303)
            ·
              refine ⟨9328623200309246945545955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6219082133539497963697303 9328623200309246945545955)
              ·
                refine ⟨13992934800463870418318933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9328623200309246945545955 13992934800463870418318933)
                ·
                  refine ⟨163979704692935981464675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13992934800463870418318933 163979704692935981464675)
                  ·
                    rfl

theorem cell21_718536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_718536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_718536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_718536 prefixEnd_718536 := by exact prefixLift 718536
  have htrace : WordTrace (prefixWord ++ tailWord_718536) baseStart_718536 baseEnd_718536 := by
    simpa [prefixWord, tailWord_718536, baseEnd_718536] using wordTrace_append hprefix tailTrace_718536
  have hstable : (prefixWord ++ tailWord_718536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718536).length < 2 ^ (prefixWord ++ tailWord_718536).sum := by decide
  have hdescent : baseEnd_718536 < baseStart_718536 := by decide
  rcases family_descends (prefixWord ++ tailWord_718536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718570 : List Nat := [3, 1, 3, 1, 1, 1, 6, 1, 4]
def baseStart_718570 : Nat := 118140960795 + 718570 * 2 ^ 59
def prefixEnd_718570 : Nat := 4983230072969 + 3 ^ 40 * 718570 * 2
def baseEnd_718570 : Nat := 163987463956159477897939

theorem tailTrace_718570 : CollatzResearch.WordTrace tailWord_718570 prefixEnd_718570 163987463956159477897939 := by
  unfold tailWord_718570
  simp only [CollatzResearch.WordTrace]
  refine ⟨6552100251687771707678291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17472267337834057887142109 6552100251687771707678291)
  ·
    refine ⟨9828150377531657561517437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6552100251687771707678291 9828150377531657561517437)
    ·
      refine ⟨3685556391574371585569039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9828150377531657561517437 3685556391574371585569039)
      ·
        refine ⟨5528334587361557378353559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3685556391574371585569039 5528334587361557378353559)
        ·
          refine ⟨8292501881042336067530339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5528334587361557378353559 8292501881042336067530339)
          ·
            refine ⟨12438752821563504101295509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8292501881042336067530339 12438752821563504101295509)
            ·
              refine ⟨583066538510789254748227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12438752821563504101295509 583066538510789254748227)
              ·
                refine ⟨874599807766183882122341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583066538510789254748227 874599807766183882122341)
                ·
                  refine ⟨163987463956159477897939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 874599807766183882122341 163987463956159477897939)
                  ·
                    rfl

theorem cell21_718570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_718570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_718570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_718570 prefixEnd_718570 := by exact prefixLift 718570
  have htrace : WordTrace (prefixWord ++ tailWord_718570) baseStart_718570 baseEnd_718570 := by
    simpa [prefixWord, tailWord_718570, baseEnd_718570] using wordTrace_append hprefix tailTrace_718570
  have hstable : (prefixWord ++ tailWord_718570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718570).length < 2 ^ (prefixWord ++ tailWord_718570).sum := by decide
  have hdescent : baseEnd_718570 < baseStart_718570 := by decide
  rcases family_descends (prefixWord ++ tailWord_718570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718629 : List Nat := [1, 3, 1, 2, 3, 2, 2, 3, 4]
def baseStart_718629 : Nat := 118140960795 + 718629 * 2 ^ 59
def prefixEnd_718629 : Nat := 4983230072969 + 3 ^ 40 * 718629 * 2
def baseEnd_718629 : Nat := 164000928559988486414485

theorem tailTrace_718629 : CollatzResearch.WordTrace tailWord_718629 prefixEnd_718629 164000928559988486414485 := by
  unfold tailWord_718629
  simp only [CollatzResearch.WordTrace]
  refine ⟨26210552913537339907110941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17473701942358226604740627 26210552913537339907110941)
  ·
    refine ⟨9828957342576502465166603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26210552913537339907110941 9828957342576502465166603)
    ·
      refine ⟨14743436013864753697749905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9828957342576502465166603 14743436013864753697749905)
      ·
        refine ⟨11057577010398565273312429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14743436013864753697749905 11057577010398565273312429)
        ·
          refine ⟨4146591378899461977492161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11057577010398565273312429 4146591378899461977492161)
          ·
            refine ⟨3109943534174596483119121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4146591378899461977492161 3109943534174596483119121)
            ·
              refine ⟨2332457650630947362339341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3109943534174596483119121 2332457650630947362339341)
              ·
                refine ⟨874671618986605260877253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2332457650630947362339341 874671618986605260877253)
                ·
                  refine ⟨164000928559988486414485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 874671618986605260877253 164000928559988486414485)
                  ·
                    rfl

theorem cell21_718629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_718629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_718629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_718629 prefixEnd_718629 := by exact prefixLift 718629
  have htrace : WordTrace (prefixWord ++ tailWord_718629) baseStart_718629 baseEnd_718629 := by
    simpa [prefixWord, tailWord_718629, baseEnd_718629] using wordTrace_append hprefix tailTrace_718629
  have hstable : (prefixWord ++ tailWord_718629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718629).length < 2 ^ (prefixWord ++ tailWord_718629).sum := by decide
  have hdescent : baseEnd_718629 < baseStart_718629 := by decide
  rcases family_descends (prefixWord ++ tailWord_718629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718649 : List Nat := [1, 2, 1, 7, 1, 1, 2, 3, 3]
def baseStart_718649 : Nat := 118140960795 + 718649 * 2 ^ 59
def prefixEnd_718649 : Nat := 4983230072969 + 3 ^ 40 * 718649 * 2
def baseEnd_718649 : Nat := 164005492832472896081111

theorem tailTrace_718649 : CollatzResearch.WordTrace tailWord_718649 prefixEnd_718649 164005492832472896081111 := by
  unfold tailWord_718649
  simp only [CollatzResearch.WordTrace]
  refine ⟨26211282373464883322839001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17474188248976588881892667 26211282373464883322839001)
  ·
    refine ⟨19658461780098662492129251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26211282373464883322839001 19658461780098662492129251)
    ·
      refine ⟨29487692670147993738193877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19658461780098662492129251 29487692670147993738193877)
      ·
        refine ⟨691117796956593603238919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 29487692670147993738193877 691117796956593603238919)
        ·
          refine ⟨1036676695434890404858379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691117796956593603238919 1036676695434890404858379)
          ·
            refine ⟨1555015043152335607287569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036676695434890404858379 1555015043152335607287569)
            ·
              refine ⟨1166261282364251705465677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1555015043152335607287569 1166261282364251705465677)
              ·
                refine ⟨437347980886594389549629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1166261282364251705465677 437347980886594389549629)
                ·
                  refine ⟨164005492832472896081111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 437347980886594389549629 164005492832472896081111)
                  ·
                    rfl

theorem cell21_718649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 3].length) (baseStart_718649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_718649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_718649 prefixEnd_718649 := by exact prefixLift 718649
  have htrace : WordTrace (prefixWord ++ tailWord_718649) baseStart_718649 baseEnd_718649 := by
    simpa [prefixWord, tailWord_718649, baseEnd_718649] using wordTrace_append hprefix tailTrace_718649
  have hstable : (prefixWord ++ tailWord_718649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718649).length < 2 ^ (prefixWord ++ tailWord_718649).sum := by decide
  have hdescent : baseEnd_718649 < baseStart_718649 := by decide
  rcases family_descends (prefixWord ++ tailWord_718649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718674 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 5]
def baseStart_718674 : Nat := 118140960795 + 718674 * 2 ^ 59
def prefixEnd_718674 : Nat := 4983230072969 + 3 ^ 40 * 718674 * 2
def baseEnd_718674 : Nat := 164011198173078408164393

theorem tailTrace_718674 : CollatzResearch.WordTrace tailWord_718674 prefixEnd_718674 164011198173078408164393 := by
  unfold tailWord_718674
  simp only [CollatzResearch.WordTrace]
  refine ⟨6553048549593578148124769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17474796132249541728332717 6553048549593578148124769)
  ·
    refine ⟨4914786412195183611093577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6553048549593578148124769 4914786412195183611093577)
    ·
      refine ⟨3686089809146387708320183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4914786412195183611093577 3686089809146387708320183)
      ·
        refine ⟨5529134713719581562480275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3686089809146387708320183 5529134713719581562480275)
        ·
          refine ⟨8293702070579372343720413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5529134713719581562480275 8293702070579372343720413)
          ·
            refine ⟨3110138276467264628895155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8293702070579372343720413 3110138276467264628895155)
            ·
              refine ⟨4665207414700896943342733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110138276467264628895155 4665207414700896943342733)
              ·
                refine ⟨1749452780512836353753525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4665207414700896943342733 1749452780512836353753525)
                ·
                  refine ⟨164011198173078408164393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1749452780512836353753525 164011198173078408164393)
                  ·
                    rfl

theorem cell21_718674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_718674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_718674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_718674 prefixEnd_718674 := by exact prefixLift 718674
  have htrace : WordTrace (prefixWord ++ tailWord_718674) baseStart_718674 baseEnd_718674 := by
    simpa [prefixWord, tailWord_718674, baseEnd_718674] using wordTrace_append hprefix tailTrace_718674
  have hstable : (prefixWord ++ tailWord_718674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718674).length < 2 ^ (prefixWord ++ tailWord_718674).sum := by decide
  have hdescent : baseEnd_718674 < baseStart_718674 := by decide
  rcases family_descends (prefixWord ++ tailWord_718674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718781 : List Nat := [1, 4, 1, 2, 3, 1, 1, 4, 4]
def baseStart_718781 : Nat := 118140960795 + 718781 * 2 ^ 59
def prefixEnd_718781 : Nat := 4983230072969 + 3 ^ 40 * 718781 * 2
def baseEnd_718781 : Nat := 164035617030869999880841

theorem tailTrace_718781 : CollatzResearch.WordTrace tailWord_718781 prefixEnd_718781 164035617030869999880841 := by
  unfold tailWord_718781
  simp only [CollatzResearch.WordTrace]
  refine ⟨26216096808986669866644197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17477397872657779911096131 26216096808986669866644197)
  ·
    refine ⟨4915518151685000599995787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26216096808986669866644197 4915518151685000599995787)
    ·
      refine ⟨7373277227527500899993681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4915518151685000599995787 7373277227527500899993681)
      ·
        refine ⟨5529957920645625674995261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7373277227527500899993681 5529957920645625674995261)
        ·
          refine ⟨2073734220242109628123223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5529957920645625674995261 2073734220242109628123223)
          ·
            refine ⟨3110601330363164442184835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2073734220242109628123223 3110601330363164442184835)
            ·
              refine ⟨4665901995544746663277253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110601330363164442184835 4665901995544746663277253)
              ·
                refine ⟨874856624164639999364485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4665901995544746663277253 874856624164639999364485)
                ·
                  refine ⟨164035617030869999880841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 874856624164639999364485 164035617030869999880841)
                  ·
                    rfl

theorem cell21_718781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_718781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_718781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_718781 prefixEnd_718781 := by exact prefixLift 718781
  have htrace : WordTrace (prefixWord ++ tailWord_718781) baseStart_718781 baseEnd_718781 := by
    simpa [prefixWord, tailWord_718781, baseEnd_718781] using wordTrace_append hprefix tailTrace_718781
  have hstable : (prefixWord ++ tailWord_718781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718781).length < 2 ^ (prefixWord ++ tailWord_718781).sum := by decide
  have hdescent : baseEnd_718781 < baseStart_718781 := by decide
  rcases family_descends (prefixWord ++ tailWord_718781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718961 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 5]
def baseStart_718961 : Nat := 118140960795 + 718961 * 2 ^ 59
def prefixEnd_718961 : Nat := 4983230072969 + 3 ^ 40 * 718961 * 2
def baseEnd_718961 : Nat := 164076695483229686880473

theorem tailTrace_718961 : CollatzResearch.WordTrace tailWord_718961 prefixEnd_718961 164076695483229686880473 := by
  unfold tailWord_718961
  simp only [CollatzResearch.WordTrace]
  refine ⟨26222661948334560608196737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17481774632223040405464491 26222661948334560608196737)
  ·
    refine ⟨19666996461250920456147553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26222661948334560608196737 19666996461250920456147553)
    ·
      refine ⟨14750247345938190342110665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19666996461250920456147553 14750247345938190342110665)
      ·
        refine ⟨11062685509453642756582999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14750247345938190342110665 11062685509453642756582999)
        ·
          refine ⟨16594028264180464134874499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11062685509453642756582999 16594028264180464134874499)
          ·
            refine ⟨24891042396270696202311749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16594028264180464134874499 24891042396270696202311749)
            ·
              refine ⟨4667070449300755537933453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24891042396270696202311749 4667070449300755537933453)
              ·
                refine ⟨1750151418487783326725045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4667070449300755537933453 1750151418487783326725045)
                ·
                  refine ⟨164076695483229686880473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1750151418487783326725045 164076695483229686880473)
                  ·
                    rfl

theorem cell21_718961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_718961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_718961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_718961 prefixEnd_718961 := by exact prefixLift 718961
  have htrace : WordTrace (prefixWord ++ tailWord_718961) baseStart_718961 baseEnd_718961 := by
    simpa [prefixWord, tailWord_718961, baseEnd_718961] using wordTrace_append hprefix tailTrace_718961
  have hstable : (prefixWord ++ tailWord_718961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718961).length < 2 ^ (prefixWord ++ tailWord_718961).sum := by decide
  have hdescent : baseEnd_718961 < baseStart_718961 := by decide
  rcases family_descends (prefixWord ++ tailWord_718961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719009 : List Nat := [1, 2, 3, 3, 1, 2, 3, 2, 4]
def baseStart_719009 : Nat := 118140960795 + 719009 * 2 ^ 59
def prefixEnd_719009 : Nat := 4983230072969 + 3 ^ 40 * 719009 * 2
def baseEnd_719009 : Nat := 164087649737192270080375

theorem tailTrace_719009 : CollatzResearch.WordTrace tailWord_719009 prefixEnd_719009 164087649737192270080375 := by
  unfold tailWord_719009
  simp only [CollatzResearch.WordTrace]
  refine ⟨26224412652160664805944081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17482941768107109870629387 26224412652160664805944081)
  ·
    refine ⟨19668309489120498604458061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26224412652160664805944081 19668309489120498604458061)
    ·
      refine ⟨7375616058420186976671773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19668309489120498604458061 7375616058420186976671773)
      ·
        refine ⟨2765856021907570116251915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7375616058420186976671773 2765856021907570116251915)
        ·
          refine ⟨4148784032861355174377873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2765856021907570116251915 4148784032861355174377873)
          ·
            refine ⟨3111588024646016380783405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4148784032861355174377873 3111588024646016380783405)
            ·
              refine ⟨1166845509242256142793777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3111588024646016380783405 1166845509242256142793777)
              ·
                refine ⟨875134131931692107095333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1166845509242256142793777 875134131931692107095333)
                ·
                  refine ⟨164087649737192270080375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 875134131931692107095333 164087649737192270080375)
                  ·
                    rfl

theorem cell21_719009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_719009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719009 prefixEnd_719009 := by exact prefixLift 719009
  have htrace : WordTrace (prefixWord ++ tailWord_719009) baseStart_719009 baseEnd_719009 := by
    simpa [prefixWord, tailWord_719009, baseEnd_719009] using wordTrace_append hprefix tailTrace_719009
  have hstable : (prefixWord ++ tailWord_719009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719009).length < 2 ^ (prefixWord ++ tailWord_719009).sum := by decide
  have hdescent : baseEnd_719009 < baseStart_719009 := by decide
  rcases family_descends (prefixWord ++ tailWord_719009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719040 : List Nat := [2, 1, 1, 2, 5, 3, 2, 5]
def baseStart_719040 : Nat := 118140960795 + 719040 * 2 ^ 59
def prefixEnd_719040 : Nat := 4983230072969 + 3 ^ 40 * 719040 * 2
def baseEnd_719040 : Nat := 54698241453181035021215

theorem tailTrace_719040 : CollatzResearch.WordTrace tailWord_719040 prefixEnd_719040 54698241453181035021215 := by
  unfold tailWord_719040
  simp only [CollatzResearch.WordTrace]
  refine ⟨13112771657524178550161287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17483695543365571400215049 13112771657524178550161287)
  ·
    refine ⟨19669157486286267825241931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13112771657524178550161287 19669157486286267825241931)
    ·
      refine ⟨29503736229429401737862897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19669157486286267825241931 29503736229429401737862897)
      ·
        refine ⟨22127802172072051303397173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29503736229429401737862897 22127802172072051303397173)
        ·
          refine ⟨2074481453631754809693485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22127802172072051303397173 2074481453631754809693485)
          ·
            refine ⟨777930545111908053635057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2074481453631754809693485 777930545111908053635057)
            ·
              refine ⟨583447908833931040226293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 777930545111908053635057 583447908833931040226293)
              ·
                refine ⟨54698241453181035021215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 583447908833931040226293 54698241453181035021215)
                ·
                  rfl

theorem cell21_719040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 5].length) (baseStart_719040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719040 prefixEnd_719040 := by exact prefixLift 719040
  have htrace : WordTrace (prefixWord ++ tailWord_719040) baseStart_719040 baseEnd_719040 := by
    simpa [prefixWord, tailWord_719040, baseEnd_719040] using wordTrace_append hprefix tailTrace_719040
  have hstable : (prefixWord ++ tailWord_719040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719040).length < 2 ^ (prefixWord ++ tailWord_719040).sum := by decide
  have hdescent : baseEnd_719040 < baseStart_719040 := by decide
  rcases family_descends (prefixWord ++ tailWord_719040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719051 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 8]
def baseStart_719051 : Nat := 118140960795 + 719051 * 2 ^ 59
def prefixEnd_719051 : Nat := 4983230072969 + 3 ^ 40 * 719051 * 2
def baseEnd_719051 : Nat := 164097234709409530380289

theorem tailTrace_719051 : CollatzResearch.WordTrace tailWord_719051 prefixEnd_719051 164097234709409530380289 := by
  unfold tailWord_719051
  simp only [CollatzResearch.WordTrace]
  refine ⟨26225944518008505978973007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17483963012005670652648671 26225944518008505978973007)
  ·
    refine ⟨39338916777012758968459511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26225944518008505978973007 39338916777012758968459511)
    ·
      refine ⟨59008375165519138452689267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39338916777012758968459511 59008375165519138452689267)
      ·
        refine ⟨88512562748278707679033901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59008375165519138452689267 88512562748278707679033901)
        ·
          refine ⟨33192211030604515379637713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88512562748278707679033901 33192211030604515379637713)
          ·
            refine ⟨24894158272953386534728285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33192211030604515379637713 24894158272953386534728285)
            ·
              refine ⟨9335309352357519950523107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24894158272953386534728285 9335309352357519950523107)
              ·
                refine ⟨14002964028536279925784661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9335309352357519950523107 14002964028536279925784661)
                ·
                  refine ⟨164097234709409530380289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14002964028536279925784661 164097234709409530380289)
                  ·
                    rfl

theorem cell21_719051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 8].length) (baseStart_719051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719051 prefixEnd_719051 := by exact prefixLift 719051
  have htrace : WordTrace (prefixWord ++ tailWord_719051) baseStart_719051 baseEnd_719051 := by
    simpa [prefixWord, tailWord_719051, baseEnd_719051] using wordTrace_append hprefix tailTrace_719051
  have hstable : (prefixWord ++ tailWord_719051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719051).length < 2 ^ (prefixWord ++ tailWord_719051).sum := by decide
  have hdescent : baseEnd_719051 < baseStart_719051 := by decide
  rcases family_descends (prefixWord ++ tailWord_719051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719074 : List Nat := [3, 3, 4, 1, 1, 1, 2, 6]
def baseStart_719074 : Nat := 118140960795 + 719074 * 2 ^ 59
def prefixEnd_719074 : Nat := 4983230072969 + 3 ^ 40 * 719074 * 2
def baseEnd_719074 : Nat := 54700827874255533832303

theorem tailTrace_719074 : CollatzResearch.WordTrace tailWord_719074 prefixEnd_719074 54700827874255533832303 := by
  unfold tailWord_719074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6556695849231295226765069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17484522264616787271373517 6556695849231295226765069)
  ·
    refine ⟨2458760943461735710036901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6556695849231295226765069 2458760943461735710036901)
    ·
      refine ⟨461017676899075445631919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2458760943461735710036901 461017676899075445631919)
      ·
        refine ⟨691526515348613168447879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461017676899075445631919 691526515348613168447879)
        ·
          refine ⟨1037289773022919752671819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691526515348613168447879 1037289773022919752671819)
          ·
            refine ⟨1555934659534379629007729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037289773022919752671819 1555934659534379629007729)
            ·
              refine ⟨1166950994650784721755797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1555934659534379629007729 1166950994650784721755797)
              ·
                refine ⟨54700827874255533832303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1166950994650784721755797 54700827874255533832303)
                ·
                  rfl

theorem cell21_719074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_719074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719074 prefixEnd_719074 := by exact prefixLift 719074
  have htrace : WordTrace (prefixWord ++ tailWord_719074) baseStart_719074 baseEnd_719074 := by
    simpa [prefixWord, tailWord_719074, baseEnd_719074] using wordTrace_append hprefix tailTrace_719074
  have hstable : (prefixWord ++ tailWord_719074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719074).length < 2 ^ (prefixWord ++ tailWord_719074).sum := by decide
  have hdescent : baseEnd_719074 < baseStart_719074 := by decide
  rcases family_descends (prefixWord ++ tailWord_719074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719133 : List Nat := [1, 4, 2, 3, 3, 1, 1, 6]
def baseStart_719133 : Nat := 118140960795 + 719133 * 2 ^ 59
def prefixEnd_719133 : Nat := 4983230072969 + 3 ^ 40 * 719133 * 2
def baseEnd_719133 : Nat := 54705316075531870004485

theorem tailTrace_719133 : CollatzResearch.WordTrace tailWord_719133 prefixEnd_719133 54705316075531870004485 := by
  unfold tailWord_719133
  simp only [CollatzResearch.WordTrace]
  refine ⟨26228935303711433983458053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17485956869140955988972035 26228935303711433983458053)
  ·
    refine ⟨4917925369445893871898385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26228935303711433983458053 4917925369445893871898385)
    ·
      refine ⟨3688444027084420403923789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4917925369445893871898385 3688444027084420403923789)
      ·
        refine ⟨1383166510156657651471421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3688444027084420403923789 1383166510156657651471421)
        ·
          refine ⟨518687441308746619301783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1383166510156657651471421 518687441308746619301783)
          ·
            refine ⟨778031161963119928952675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518687441308746619301783 778031161963119928952675)
            ·
              refine ⟨1167046742944679893429013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778031161963119928952675 1167046742944679893429013)
              ·
                refine ⟨54705316075531870004485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1167046742944679893429013 54705316075531870004485)
                ·
                  rfl

theorem cell21_719133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 6].length) (baseStart_719133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719133 prefixEnd_719133 := by exact prefixLift 719133
  have htrace : WordTrace (prefixWord ++ tailWord_719133) baseStart_719133 baseEnd_719133 := by
    simpa [prefixWord, tailWord_719133, baseEnd_719133] using wordTrace_append hprefix tailTrace_719133
  have hstable : (prefixWord ++ tailWord_719133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719133).length < 2 ^ (prefixWord ++ tailWord_719133).sum := by decide
  have hdescent : baseEnd_719133 < baseStart_719133 := by decide
  rcases family_descends (prefixWord ++ tailWord_719133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719248 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 11]
def baseStart_719248 : Nat := 118140960795 + 719248 * 2 ^ 59
def prefixEnd_719248 : Nat := 4983230072969 + 3 ^ 40 * 719248 * 2
def baseEnd_719248 : Nat := 164142192793380965596553

theorem tailTrace_719248 : CollatzResearch.WordTrace tailWord_719248 prefixEnd_719248 164142192793380965596553 := by
  unfold tailWord_719248
  simp only [CollatzResearch.WordTrace]
  refine ⟨13116564849147404311947199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17488753132196539082596265 13116564849147404311947199)
  ·
    refine ⟨19674847273721106467920799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13116564849147404311947199 19674847273721106467920799)
    ·
      refine ⟨29512270910581659701881199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19674847273721106467920799 29512270910581659701881199)
      ·
        refine ⟨44268406365872489552821799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29512270910581659701881199 44268406365872489552821799)
        ·
          refine ⟨66402609548808734329232699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44268406365872489552821799 66402609548808734329232699)
          ·
            refine ⟨99603914323213101493849049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66402609548808734329232699 99603914323213101493849049)
            ·
              refine ⟨74702935742409826120386787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99603914323213101493849049 74702935742409826120386787)
              ·
                refine ⟨112054403613614739180580181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74702935742409826120386787 112054403613614739180580181)
                ·
                  refine ⟨164142192793380965596553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 112054403613614739180580181 164142192793380965596553)
                  ·
                    rfl

theorem cell21_719248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_719248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719248 prefixEnd_719248 := by exact prefixLift 719248
  have htrace : WordTrace (prefixWord ++ tailWord_719248) baseStart_719248 baseEnd_719248 := by
    simpa [prefixWord, tailWord_719248, baseEnd_719248] using wordTrace_append hprefix tailTrace_719248
  have hstable : (prefixWord ++ tailWord_719248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719248).length < 2 ^ (prefixWord ++ tailWord_719248).sum := by decide
  have hdescent : baseEnd_719248 < baseStart_719248 := by decide
  rcases family_descends (prefixWord ++ tailWord_719248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719282 : List Nat := [3, 2, 1, 1, 1, 1, 4, 5, 3]
def baseStart_719282 : Nat := 118140960795 + 719282 * 2 ^ 59
def prefixEnd_719282 : Nat := 4983230072969 + 3 ^ 40 * 719282 * 2
def baseEnd_719282 : Nat := 164149952056604462029817

theorem tailTrace_719282 : CollatzResearch.WordTrace tailWord_719282 prefixEnd_719282 164149952056604462029817 := by
  unfold tailWord_719282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6558592445042908107658025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17489579853447754953754733 6558592445042908107658025)
  ·
    refine ⟨4918944333782181080743519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6558592445042908107658025 4918944333782181080743519)
    ·
      refine ⟨7378416500673271621115279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4918944333782181080743519 7378416500673271621115279)
      ·
        refine ⟨11067624751009907431672919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7378416500673271621115279 11067624751009907431672919)
        ·
          refine ⟨16601437126514861147509379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11067624751009907431672919 16601437126514861147509379)
          ·
            refine ⟨24902155689772291721264069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16601437126514861147509379 24902155689772291721264069)
            ·
              refine ⟨4669154191832304697737013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24902155689772291721264069 4669154191832304697737013)
              ·
                refine ⟨437733205484278565412845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4669154191832304697737013 437733205484278565412845)
                ·
                  refine ⟨164149952056604462029817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 437733205484278565412845 164149952056604462029817)
                  ·
                    rfl

theorem cell21_719282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_719282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719282 prefixEnd_719282 := by exact prefixLift 719282
  have htrace : WordTrace (prefixWord ++ tailWord_719282) baseStart_719282 baseEnd_719282 := by
    simpa [prefixWord, tailWord_719282, baseEnd_719282] using wordTrace_append hprefix tailTrace_719282
  have hstable : (prefixWord ++ tailWord_719282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719282).length < 2 ^ (prefixWord ++ tailWord_719282).sum := by decide
  have hdescent : baseEnd_719282 < baseStart_719282 := by decide
  rcases family_descends (prefixWord ++ tailWord_719282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719327 : List Nat := [1, 1, 2, 3, 3, 3, 3, 5]
def baseStart_719327 : Nat := 118140960795 + 719327 * 2 ^ 59
def prefixEnd_719327 : Nat := 4983230072969 + 3 ^ 40 * 719327 * 2
def baseEnd_719327 : Nat := 54720073889898127926575

theorem tailTrace_719327 : CollatzResearch.WordTrace tailWord_719327 prefixEnd_719327 54720073889898127926575 := by
  unfold tailWord_719327
  simp only [CollatzResearch.WordTrace]
  refine ⟨26236011065008605116020235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17490674043339070077346823 26236011065008605116020235)
  ·
    refine ⟨39354016597512907674030353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26236011065008605116020235 39354016597512907674030353)
    ·
      refine ⟨29515512448134680755522765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39354016597512907674030353 29515512448134680755522765)
      ·
        refine ⟨11068317168050505283321037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29515512448134680755522765 11068317168050505283321037)
        ·
          refine ⟨4150618938018939481245389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11068317168050505283321037 4150618938018939481245389)
          ·
            refine ⟨1556482101757102305467021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4150618938018939481245389 1556482101757102305467021)
            ·
              refine ⟨583680788158913364550133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1556482101757102305467021 583680788158913364550133)
              ·
                refine ⟨54720073889898127926575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 583680788158913364550133 54720073889898127926575)
                ·
                  rfl

theorem cell21_719327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 5].length) (baseStart_719327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719327 prefixEnd_719327 := by exact prefixLift 719327
  have htrace : WordTrace (prefixWord ++ tailWord_719327) baseStart_719327 baseEnd_719327 := by
    simpa [prefixWord, tailWord_719327, baseEnd_719327] using wordTrace_append hprefix tailTrace_719327
  have hstable : (prefixWord ++ tailWord_719327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719327).length < 2 ^ (prefixWord ++ tailWord_719327).sum := by decide
  have hdescent : baseEnd_719327 < baseStart_719327 := by decide
  rcases family_descends (prefixWord ++ tailWord_719327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719392 : List Nat := [2, 1, 1, 6, 2, 2, 1, 3, 3]
def baseStart_719392 : Nat := 118140960795 + 719392 * 2 ^ 59
def prefixEnd_719392 : Nat := 4983230072969 + 3 ^ 40 * 719392 * 2
def baseEnd_719392 : Nat := 164175055555268715196259

theorem tailTrace_719392 : CollatzResearch.WordTrace tailWord_719392 prefixEnd_719392 164175055555268715196259 := by
  unfold tailWord_719392
  simp only [CollatzResearch.WordTrace]
  refine ⟨13119190904886560608568215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17492254539848747478090953 13119190904886560608568215)
  ·
    refine ⟨19678786357329840912852323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13119190904886560608568215 19678786357329840912852323)
    ·
      refine ⟨29518179535994761369278485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19678786357329840912852323 29518179535994761369278485)
      ·
        refine ⟨1383664665749754439184929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29518179535994761369278485 1383664665749754439184929)
        ·
          refine ⟨1037748499312315829388697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1383664665749754439184929 1037748499312315829388697)
          ·
            refine ⟨778311374484236872041523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1037748499312315829388697 778311374484236872041523)
            ·
              refine ⟨1167467061726355308062285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778311374484236872041523 1167467061726355308062285)
              ·
                refine ⟨437800148147383240523357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1167467061726355308062285 437800148147383240523357)
                ·
                  refine ⟨164175055555268715196259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 437800148147383240523357 164175055555268715196259)
                  ·
                    rfl

theorem cell21_719392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 3].length) (baseStart_719392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719392 prefixEnd_719392 := by exact prefixLift 719392
  have htrace : WordTrace (prefixWord ++ tailWord_719392) baseStart_719392 baseEnd_719392 := by
    simpa [prefixWord, tailWord_719392, baseEnd_719392] using wordTrace_append hprefix tailTrace_719392
  have hstable : (prefixWord ++ tailWord_719392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719392).length < 2 ^ (prefixWord ++ tailWord_719392).sum := by decide
  have hdescent : baseEnd_719392 < baseStart_719392 := by decide
  rcases family_descends (prefixWord ++ tailWord_719392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719493 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 5]
def baseStart_719493 : Nat := 118140960795 + 719493 * 2 ^ 59
def prefixEnd_719493 : Nat := 4983230072969 + 3 ^ 40 * 719493 * 2
def baseEnd_719493 : Nat := 164198105131314984012719

theorem tailTrace_719493 : CollatzResearch.WordTrace tailWord_719493 prefixEnd_719493 164198105131314984012719 := by
  unfold tailWord_719493
  simp only [CollatzResearch.WordTrace]
  refine ⟨26242065582407215466563133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17494710388271476977708755 26242065582407215466563133)
  ·
    refine ⟨9840774593402705799961175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26242065582407215466563133 9840774593402705799961175)
    ·
      refine ⟨14761161890104058699941763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9840774593402705799961175 14761161890104058699941763)
      ·
        refine ⟨22141742835156088049912645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14761161890104058699941763 22141742835156088049912645)
        ·
          refine ⟨4151576781591766509358621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22141742835156088049912645 4151576781591766509358621)
          ·
            refine ⟨1556841293096912441009483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4151576781591766509358621 1556841293096912441009483)
            ·
              refine ⟨2335261939645368661514225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556841293096912441009483 2335261939645368661514225)
              ·
                refine ⟨1751446454734026496135669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2335261939645368661514225 1751446454734026496135669)
                ·
                  refine ⟨164198105131314984012719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1751446454734026496135669 164198105131314984012719)
                  ·
                    rfl

theorem cell21_719493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_719493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719493 prefixEnd_719493 := by exact prefixLift 719493
  have htrace : WordTrace (prefixWord ++ tailWord_719493) baseStart_719493 baseEnd_719493 := by
    simpa [prefixWord, tailWord_719493, baseEnd_719493] using wordTrace_append hprefix tailTrace_719493
  have hstable : (prefixWord ++ tailWord_719493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719493).length < 2 ^ (prefixWord ++ tailWord_719493).sum := by decide
  have hdescent : baseEnd_719493 < baseStart_719493 := by decide
  rcases family_descends (prefixWord ++ tailWord_719493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719527 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 5]
def baseStart_719527 : Nat := 118140960795 + 719527 * 2 ^ 59
def prefixEnd_719527 : Nat := 4983230072969 + 3 ^ 40 * 719527 * 2
def baseEnd_719527 : Nat := 164205864394538480445983

theorem tailTrace_719527 : CollatzResearch.WordTrace tailWord_719527 prefixEnd_719527 164205864394538480445983 := by
  unfold tailWord_719527
  simp only [CollatzResearch.WordTrace]
  refine ⟨26243305664284039273300835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17495537109522692848867223 26243305664284039273300835)
  ·
    refine ⟨39364958496426058909951253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26243305664284039273300835 39364958496426058909951253)
    ·
      refine ⟨1845232429519971511403965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39364958496426058909951253 1845232429519971511403965)
      ·
        refine ⟨691962161069989316776487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1845232429519971511403965 691962161069989316776487)
        ·
          refine ⟨1037943241604983975164731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691962161069989316776487 1037943241604983975164731)
          ·
            refine ⟨1556914862407475962747097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037943241604983975164731 1556914862407475962747097)
            ·
              refine ⟨1167686146805606972060323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1556914862407475962747097 1167686146805606972060323)
              ·
                refine ⟨1751529220208410458090485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1167686146805606972060323 1751529220208410458090485)
                ·
                  refine ⟨164205864394538480445983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1751529220208410458090485 164205864394538480445983)
                  ·
                    rfl

theorem cell21_719527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 5].length) (baseStart_719527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719527 prefixEnd_719527 := by exact prefixLift 719527
  have htrace : WordTrace (prefixWord ++ tailWord_719527) baseStart_719527 baseEnd_719527 := by
    simpa [prefixWord, tailWord_719527, baseEnd_719527] using wordTrace_append hprefix tailTrace_719527
  have hstable : (prefixWord ++ tailWord_719527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719527).length < 2 ^ (prefixWord ++ tailWord_719527).sum := by decide
  have hdescent : baseEnd_719527 < baseStart_719527 := by decide
  rcases family_descends (prefixWord ++ tailWord_719527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719572 : List Nat := [2, 4, 1, 3, 3, 1, 7]
def baseStart_719572 : Nat := 118140960795 + 719572 * 2 ^ 59
def prefixEnd_719572 : Nat := 4983230072969 + 3 ^ 40 * 719572 * 2
def baseEnd_719572 : Nat := 18246237111958711355099

theorem tailTrace_719572 : CollatzResearch.WordTrace tailWord_719572 prefixEnd_719572 18246237111958711355099 := by
  unfold tailWord_719572
  simp only [CollatzResearch.WordTrace]
  refine ⟨13122473474560505979344485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17496631299414007972459313 13122473474560505979344485)
  ·
    refine ⟨2460463776480094871127091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13122473474560505979344485 2460463776480094871127091)
    ·
      refine ⟨3690695664720142306690637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2460463776480094871127091 3690695664720142306690637)
      ·
        refine ⟨1384010874270053365008989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3690695664720142306690637 1384010874270053365008989)
        ·
          refine ⟨519004077851270011878371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1384010874270053365008989 519004077851270011878371)
          ·
            refine ⟨778506116776905017817557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519004077851270011878371 778506116776905017817557)
            ·
              refine ⟨18246237111958711355099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 778506116776905017817557 18246237111958711355099)
              ·
                rfl

theorem cell21_719572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 7].length) (baseStart_719572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719572 prefixEnd_719572 := by exact prefixLift 719572
  have htrace : WordTrace (prefixWord ++ tailWord_719572) baseStart_719572 baseEnd_719572 := by
    simpa [prefixWord, tailWord_719572, baseEnd_719572] using wordTrace_append hprefix tailTrace_719572
  have hstable : (prefixWord ++ tailWord_719572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719572).length < 2 ^ (prefixWord ++ tailWord_719572).sum := by decide
  have hdescent : baseEnd_719572 < baseStart_719572 := by decide
  rcases family_descends (prefixWord ++ tailWord_719572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719583 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 6]
def baseStart_719583 : Nat := 118140960795 + 719583 * 2 ^ 59
def prefixEnd_719583 : Nat := 4983230072969 + 3 ^ 40 * 719583 * 2
def baseEnd_719583 : Nat := 164218644357494827512535

theorem tailTrace_719583 : CollatzResearch.WordTrace tailWord_719583 prefixEnd_719583 164218644357494827512535 := by
  unfold tailWord_719583
  simp only [CollatzResearch.WordTrace]
  refine ⟨26245348152081160837339403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17496898768054107224892935 26245348152081160837339403)
  ·
    refine ⟨39368022228121741256009105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26245348152081160837339403 39368022228121741256009105)
    ·
      refine ⟨29526016671091305942006829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39368022228121741256009105 29526016671091305942006829)
      ·
        refine ⟨11072256251659239728252561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29526016671091305942006829 11072256251659239728252561)
        ·
          refine ⟨8304192188744429796189421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11072256251659239728252561 8304192188744429796189421)
          ·
            refine ⟨3114072070779161173571033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8304192188744429796189421 3114072070779161173571033)
            ·
              refine ⟨2335554053084370880178275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3114072070779161173571033 2335554053084370880178275)
              ·
                refine ⟨3503331079626556320267413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2335554053084370880178275 3503331079626556320267413)
                ·
                  refine ⟨164218644357494827512535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3503331079626556320267413 164218644357494827512535)
                  ·
                    rfl

theorem cell21_719583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 6].length) (baseStart_719583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719583 prefixEnd_719583 := by exact prefixLift 719583
  have htrace : WordTrace (prefixWord ++ tailWord_719583) baseStart_719583 baseEnd_719583 := by
    simpa [prefixWord, tailWord_719583, baseEnd_719583] using wordTrace_append hprefix tailTrace_719583
  have hstable : (prefixWord ++ tailWord_719583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719583).length < 2 ^ (prefixWord ++ tailWord_719583).sum := by decide
  have hdescent : baseEnd_719583 < baseStart_719583 := by decide
  rcases family_descends (prefixWord ++ tailWord_719583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719634 : List Nat := [3, 2, 4, 1, 2, 1, 2, 2, 4]
def baseStart_719634 : Nat := 118140960795 + 719634 * 2 ^ 59
def prefixEnd_719634 : Nat := 4983230072969 + 3 ^ 40 * 719634 * 2
def baseEnd_719634 : Nat := 164230283252330072162431

theorem tailTrace_719634 : CollatzResearch.WordTrace tailWord_719634 prefixEnd_719634 164230283252330072162431 := by
  unfold tailWord_719634
  simp only [CollatzResearch.WordTrace]
  refine ⟨6561802068724099136861489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17498138849930931031630637 6561802068724099136861489)
  ·
    refine ⟨4921351551543074352646117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6561802068724099136861489 4921351551543074352646117)
    ·
      refine ⟨922753415914326441121147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4921351551543074352646117 922753415914326441121147)
      ·
        refine ⟨1384130123871489661681721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 922753415914326441121147 1384130123871489661681721)
        ·
          refine ⟨1038097592903617246261291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1384130123871489661681721 1038097592903617246261291)
          ·
            refine ⟨1557146389355425869391937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038097592903617246261291 1557146389355425869391937)
            ·
              refine ⟨1167859792016569402043953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1557146389355425869391937 1167859792016569402043953)
              ·
                refine ⟨875894844012427051532965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1167859792016569402043953 875894844012427051532965)
                ·
                  refine ⟨164230283252330072162431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 875894844012427051532965 164230283252330072162431)
                  ·
                    rfl

theorem cell21_719634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_719634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719634 prefixEnd_719634 := by exact prefixLift 719634
  have htrace : WordTrace (prefixWord ++ tailWord_719634) baseStart_719634 baseEnd_719634 := by
    simpa [prefixWord, tailWord_719634, baseEnd_719634] using wordTrace_append hprefix tailTrace_719634
  have hstable : (prefixWord ++ tailWord_719634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719634).length < 2 ^ (prefixWord ++ tailWord_719634).sum := by decide
  have hdescent : baseEnd_719634 < baseStart_719634 := by decide
  rcases family_descends (prefixWord ++ tailWord_719634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719662 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_719662 : Nat := 118140960795 + 719662 * 2 ^ 59
def prefixEnd_719662 : Nat := 4983230072969 + 3 ^ 40 * 719662 * 2
def baseEnd_719662 : Nat := 164236673233808245695707

theorem tailTrace_719662 : CollatzResearch.WordTrace tailWord_719662 prefixEnd_719662 164236673233808245695707 := by
  unfold tailWord_719662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3281028689849369666183155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17498819679196638219643493 3281028689849369666183155)
  ·
    refine ⟨4921543034774054499274733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3281028689849369666183155 4921543034774054499274733)
    ·
      refine ⟨1845578638040270437228025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4921543034774054499274733 1845578638040270437228025)
      ·
        refine ⟨1384183978530202827921019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1845578638040270437228025 1384183978530202827921019)
        ·
          refine ⟨2076275967795304241881529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384183978530202827921019 2076275967795304241881529)
          ·
            refine ⟨1557206975846478181411147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2076275967795304241881529 1557206975846478181411147)
            ·
              refine ⟨2335810463769717272116721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557206975846478181411147 2335810463769717272116721)
              ·
                refine ⟨1751857847827287954087541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2335810463769717272116721 1751857847827287954087541)
                ·
                  refine ⟨164236673233808245695707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1751857847827287954087541 164236673233808245695707)
                  ·
                    rfl

theorem cell21_719662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_719662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719662 prefixEnd_719662 := by exact prefixLift 719662
  have htrace : WordTrace (prefixWord ++ tailWord_719662) baseStart_719662 baseEnd_719662 := by
    simpa [prefixWord, tailWord_719662, baseEnd_719662] using wordTrace_append hprefix tailTrace_719662
  have hstable : (prefixWord ++ tailWord_719662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719662).length < 2 ^ (prefixWord ++ tailWord_719662).sum := by decide
  have hdescent : baseEnd_719662 < baseStart_719662 := by decide
  rcases family_descends (prefixWord ++ tailWord_719662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719693 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 6]
def baseStart_719693 : Nat := 118140960795 + 719693 * 2 ^ 59
def prefixEnd_719693 : Nat := 4983230072969 + 3 ^ 40 * 719693 * 2
def baseEnd_719693 : Nat := 164243747856159080678977

theorem tailTrace_719693 : CollatzResearch.WordTrace tailWord_719693 prefixEnd_719693 164243747856159080678977 := by
  unfold tailWord_719693
  simp only [CollatzResearch.WordTrace]
  refine ⟨26249360181682649623843733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17499573454455099749229155 26249360181682649623843733)
  ·
    refine ⟨1230438758516374201117675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26249360181682649623843733 1230438758516374201117675)
    ·
      refine ⟨1845658137774561301676513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1230438758516374201117675 1845658137774561301676513)
      ·
        refine ⟨1384243603330920976257385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1845658137774561301676513 1384243603330920976257385)
        ·
          refine ⟨1038182702498190732193039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1384243603330920976257385 1038182702498190732193039)
          ·
            refine ⟨1557274053747286098289559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038182702498190732193039 1557274053747286098289559)
            ·
              refine ⟨2335911080620929147434339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557274053747286098289559 2335911080620929147434339)
              ·
                refine ⟨3503866620931393721151509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2335911080620929147434339 3503866620931393721151509)
                ·
                  refine ⟨164243747856159080678977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3503866620931393721151509 164243747856159080678977)
                  ·
                    rfl

theorem cell21_719693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_719693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719693 prefixEnd_719693 := by exact prefixLift 719693
  have htrace : WordTrace (prefixWord ++ tailWord_719693) baseStart_719693 baseEnd_719693 := by
    simpa [prefixWord, tailWord_719693, baseEnd_719693] using wordTrace_append hprefix tailTrace_719693
  have hstable : (prefixWord ++ tailWord_719693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719693).length < 2 ^ (prefixWord ++ tailWord_719693).sum := by decide
  have hdescent : baseEnd_719693 < baseStart_719693 := by decide
  rcases family_descends (prefixWord ++ tailWord_719693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719749 : List Nat := [1, 3, 1, 1, 3, 3, 9]
def baseStart_719749 : Nat := 118140960795 + 719749 * 2 ^ 59
def prefixEnd_719749 : Nat := 4983230072969 + 3 ^ 40 * 719749 * 2
def baseEnd_719749 : Nat := 18250725313235047527281

theorem tailTrace_719749 : CollatzResearch.WordTrace tailWord_719749 prefixEnd_719749 18250725313235047527281 := by
  unfold tailWord_719749
  simp only [CollatzResearch.WordTrace]
  refine ⟨26251402669479771187882301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17500935112986514125254867 26251402669479771187882301)
  ·
    refine ⟨9844276001054914195455863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26251402669479771187882301 9844276001054914195455863)
    ·
      refine ⟨14766414001582371293183795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9844276001054914195455863 14766414001582371293183795)
      ·
        refine ⟨22149621002373556939775693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14766414001582371293183795 22149621002373556939775693)
        ·
          refine ⟨8306107875890083852415885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22149621002373556939775693 8306107875890083852415885)
          ·
            refine ⟨3114790453458781444655957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8306107875890083852415885 3114790453458781444655957)
            ·
              refine ⟨18250725313235047527281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3114790453458781444655957 18250725313235047527281)
              ·
                rfl

theorem cell21_719749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 9].length) (baseStart_719749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719749 prefixEnd_719749 := by exact prefixLift 719749
  have htrace : WordTrace (prefixWord ++ tailWord_719749) baseStart_719749 baseEnd_719749 := by
    simpa [prefixWord, tailWord_719749, baseEnd_719749] using wordTrace_append hprefix tailTrace_719749
  have hstable : (prefixWord ++ tailWord_719749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719749).length < 2 ^ (prefixWord ++ tailWord_719749).sum := by decide
  have hdescent : baseEnd_719749 < baseStart_719749 := by decide
  rcases family_descends (prefixWord ++ tailWord_719749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719780 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 7]
def baseStart_719780 : Nat := 118140960795 + 719780 * 2 ^ 59
def prefixEnd_719780 : Nat := 4983230072969 + 3 ^ 40 * 719780 * 2
def baseEnd_719780 : Nat := 164263602441466262728799

theorem tailTrace_719780 : CollatzResearch.WordTrace tailWord_719780 prefixEnd_719780 164263602441466262728799 := by
  unfold tailWord_719780
  simp only [CollatzResearch.WordTrace]
  refine ⟨13126266666183731741130397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17501688888244975654840529 13126266666183731741130397)
  ·
    refine ⟨4922349999818899402923899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13126266666183731741130397 4922349999818899402923899)
    ·
      refine ⟨7383524999728349104385849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4922349999818899402923899 7383524999728349104385849)
      ·
        refine ⟨5537643749796261828289387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7383524999728349104385849 5537643749796261828289387)
        ·
          refine ⟨8306465624694392742434081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5537643749796261828289387 8306465624694392742434081)
          ·
            refine ⟨6229849218520794556825561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8306465624694392742434081 6229849218520794556825561)
            ·
              refine ⟨4672386913890595917619171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6229849218520794556825561 4672386913890595917619171)
              ·
                refine ⟨7008580370835893876428757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4672386913890595917619171 7008580370835893876428757)
                ·
                  refine ⟨164263602441466262728799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7008580370835893876428757 164263602441466262728799)
                  ·
                    rfl

theorem cell21_719780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_719780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719780 prefixEnd_719780 := by exact prefixLift 719780
  have htrace : WordTrace (prefixWord ++ tailWord_719780) baseStart_719780 baseEnd_719780 := by
    simpa [prefixWord, tailWord_719780, baseEnd_719780] using wordTrace_append hprefix tailTrace_719780
  have hstable : (prefixWord ++ tailWord_719780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719780).length < 2 ^ (prefixWord ++ tailWord_719780).sum := by decide
  have hdescent : baseEnd_719780 < baseStart_719780 := by decide
  rcases family_descends (prefixWord ++ tailWord_719780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719828 : List Nat := [2, 4, 1, 2, 1, 2, 2, 3, 4]
def baseStart_719828 : Nat := 118140960795 + 719828 * 2 ^ 59
def prefixEnd_719828 : Nat := 4983230072969 + 3 ^ 40 * 719828 * 2
def baseEnd_719828 : Nat := 164274556695428845928701

theorem tailTrace_719828 : CollatzResearch.WordTrace tailWord_719828 prefixEnd_719828 164274556695428845928701 := by
  unfold tailWord_719828
  simp only [CollatzResearch.WordTrace]
  refine ⟨13127142018096783840004069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17502856024129045120005425 13127142018096783840004069)
  ·
    refine ⟨2461339128393146970000763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13127142018096783840004069 2461339128393146970000763)
    ·
      refine ⟨3692008692589720455001145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2461339128393146970000763 3692008692589720455001145)
      ·
        refine ⟨2769006519442290341250859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3692008692589720455001145 2769006519442290341250859)
        ·
          refine ⟨4153509779163435511876289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2769006519442290341250859 4153509779163435511876289)
          ·
            refine ⟨3115132334372576633907217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4153509779163435511876289 3115132334372576633907217)
            ·
              refine ⟨2336349250779432475430413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3115132334372576633907217 2336349250779432475430413)
              ·
                refine ⟨876130969042287178286405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2336349250779432475430413 876130969042287178286405)
                ·
                  refine ⟨164274556695428845928701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 876130969042287178286405 164274556695428845928701)
                  ·
                    rfl

theorem cell21_719828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_719828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719828 prefixEnd_719828 := by exact prefixLift 719828
  have htrace : WordTrace (prefixWord ++ tailWord_719828) baseStart_719828 baseEnd_719828 := by
    simpa [prefixWord, tailWord_719828, baseEnd_719828] using wordTrace_append hprefix tailTrace_719828
  have hstable : (prefixWord ++ tailWord_719828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719828).length < 2 ^ (prefixWord ++ tailWord_719828).sum := by decide
  have hdescent : baseEnd_719828 < baseStart_719828 := by decide
  rcases family_descends (prefixWord ++ tailWord_719828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719873 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 5]
def baseStart_719873 : Nat := 118140960795 + 719873 * 2 ^ 59
def prefixEnd_719873 : Nat := 4983230072969 + 3 ^ 40 * 719873 * 2
def baseEnd_719873 : Nat := 164284826308518767678609

theorem tailTrace_719873 : CollatzResearch.WordTrace tailWord_719873 prefixEnd_719873 164284826308518767678609 := by
  unfold tailWord_719873
  simp only [CollatzResearch.WordTrace]
  refine ⟨26255925321030540365396273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17503950214020360243597515 26255925321030540365396273)
  ·
    refine ⟨19691943990772905274047205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26255925321030540365396273 19691943990772905274047205)
    ·
      refine ⟨3692239498269919738883851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19691943990772905274047205 3692239498269919738883851)
      ·
        refine ⟨5538359247404879608325777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3692239498269919738883851 5538359247404879608325777)
        ·
          refine ⟨4153769435553659706244333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5538359247404879608325777 4153769435553659706244333)
          ·
            refine ⟨1557663538332622389841625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4153769435553659706244333 1557663538332622389841625)
            ·
              refine ⟨1168247653749466792381219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1557663538332622389841625 1168247653749466792381219)
              ·
                refine ⟨1752371480624200188571829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168247653749466792381219 1752371480624200188571829)
                ·
                  refine ⟨164284826308518767678609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1752371480624200188571829 164284826308518767678609)
                  ·
                    rfl

theorem cell21_719873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_719873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719873 prefixEnd_719873 := by exact prefixLift 719873
  have htrace : WordTrace (prefixWord ++ tailWord_719873) baseStart_719873 baseEnd_719873 := by
    simpa [prefixWord, tailWord_719873, baseEnd_719873] using wordTrace_append hprefix tailTrace_719873
  have hstable : (prefixWord ++ tailWord_719873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719873).length < 2 ^ (prefixWord ++ tailWord_719873).sum := by decide
  have hdescent : baseEnd_719873 < baseStart_719873 := by decide
  rcases family_descends (prefixWord ++ tailWord_719873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719924 : List Nat := [2, 5, 1, 2, 1, 2, 3, 2, 3]
def baseStart_719924 : Nat := 118140960795 + 719924 * 2 ^ 59
def prefixEnd_719924 : Nat := 4983230072969 + 3 ^ 40 * 719924 * 2
def baseEnd_719924 : Nat := 164296465203354012328505

theorem tailTrace_719924 : CollatzResearch.WordTrace tailWord_719924 prefixEnd_719924 164296465203354012328505 := by
  unfold tailWord_719924
  simp only [CollatzResearch.WordTrace]
  refine ⟨13128892721922888037751413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17505190295897184050335217 13128892721922888037751413)
  ·
    refine ⟨1230833692680270753539195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13128892721922888037751413 1230833692680270753539195)
    ·
      refine ⟨1846250539020406130308793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1230833692680270753539195 1846250539020406130308793)
      ·
        refine ⟨1384687904265304597731595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1846250539020406130308793 1384687904265304597731595)
        ·
          refine ⟨2077031856397956896597393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384687904265304597731595 2077031856397956896597393)
          ·
            refine ⟨1557773892298467672448045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2077031856397956896597393 1557773892298467672448045)
            ·
              refine ⟨584165209611925377168017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1557773892298467672448045 584165209611925377168017)
              ·
                refine ⟨438123907208944032876013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584165209611925377168017 438123907208944032876013)
                ·
                  refine ⟨164296465203354012328505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 438123907208944032876013 164296465203354012328505)
                  ·
                    rfl

theorem cell21_719924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_719924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_719924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_719924 prefixEnd_719924 := by exact prefixLift 719924
  have htrace : WordTrace (prefixWord ++ tailWord_719924) baseStart_719924 baseEnd_719924 := by
    simpa [prefixWord, tailWord_719924, baseEnd_719924] using wordTrace_append hprefix tailTrace_719924
  have hstable : (prefixWord ++ tailWord_719924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719924).length < 2 ^ (prefixWord ++ tailWord_719924).sum := by decide
  have hdescent : baseEnd_719924 < baseStart_719924 := by decide
  rcases family_descends (prefixWord ++ tailWord_719924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720042 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 5]
def baseStart_720042 : Nat := 118140960795 + 720042 * 2 ^ 59
def prefixEnd_720042 : Nat := 4983230072969 + 3 ^ 40 * 720042 * 2
def baseEnd_720042 : Nat := 164323394411012029361597

theorem tailTrace_720042 : CollatzResearch.WordTrace tailWord_720042 prefixEnd_720042 164323394411012029361597 := by
  unfold tailWord_720042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6565522314354570557074595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17508059504945521485532253 6565522314354570557074595)
  ·
    refine ⟨9848283471531855835611893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6565522314354570557074595 9848283471531855835611893)
    ·
      refine ⟨923276575456111484588615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9848283471531855835611893 923276575456111484588615)
      ·
        refine ⟨1384914863184167226882923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 923276575456111484588615 1384914863184167226882923)
        ·
          refine ⟨2077372294776250840324385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384914863184167226882923 2077372294776250840324385)
          ·
            refine ⟨1558029221082188130243289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2077372294776250840324385 1558029221082188130243289)
            ·
              refine ⟨1168521915811641097682467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1558029221082188130243289 1168521915811641097682467)
              ·
                refine ⟨1752782873717461646523701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168521915811641097682467 1752782873717461646523701)
                ·
                  refine ⟨164323394411012029361597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1752782873717461646523701 164323394411012029361597)
                  ·
                    rfl

theorem cell21_720042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_720042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720042 prefixEnd_720042 := by exact prefixLift 720042
  have htrace : WordTrace (prefixWord ++ tailWord_720042) baseStart_720042 baseEnd_720042 := by
    simpa [prefixWord, tailWord_720042, baseEnd_720042] using wordTrace_append hprefix tailTrace_720042
  have hstable : (prefixWord ++ tailWord_720042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720042).length < 2 ^ (prefixWord ++ tailWord_720042).sum := by decide
  have hdescent : baseEnd_720042 < baseStart_720042 := by decide
  rcases family_descends (prefixWord ++ tailWord_720042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720067 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 7]
def baseStart_720067 : Nat := 118140960795 + 720067 * 2 ^ 59
def prefixEnd_720067 : Nat := 4983230072969 + 3 ^ 40 * 720067 * 2
def baseEnd_720067 : Nat := 164329099751617541444879

theorem tailTrace_720067 : CollatzResearch.WordTrace tailWord_720067 prefixEnd_720067 164329099751617541444879 := by
  unfold tailWord_720067
  simp only [CollatzResearch.WordTrace]
  refine ⟨26263001082327711497958455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17508667388218474331972303 26263001082327711497958455)
  ·
    refine ⟨39394501623491567246937683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26263001082327711497958455 39394501623491567246937683)
    ·
      refine ⟨59091752435237350870406525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39394501623491567246937683 59091752435237350870406525)
      ·
        refine ⟨22159407163214006576402447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59091752435237350870406525 22159407163214006576402447)
        ·
          refine ⟨33239110744821009864603671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22159407163214006576402447 33239110744821009864603671)
          ·
            refine ⟨49858666117231514796905507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33239110744821009864603671 49858666117231514796905507)
            ·
              refine ⟨74787999175847272195358261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49858666117231514796905507 74787999175847272195358261)
              ·
                refine ⟨7011374922735681768314837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74787999175847272195358261 7011374922735681768314837)
                ·
                  refine ⟨164329099751617541444879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7011374922735681768314837 164329099751617541444879)
                  ·
                    rfl

theorem cell21_720067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 7].length) (baseStart_720067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720067 prefixEnd_720067 := by exact prefixLift 720067
  have htrace : WordTrace (prefixWord ++ tailWord_720067) baseStart_720067 baseEnd_720067 := by
    simpa [prefixWord, tailWord_720067, baseEnd_720067] using wordTrace_append hprefix tailTrace_720067
  have hstable : (prefixWord ++ tailWord_720067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720067).length < 2 ^ (prefixWord ++ tailWord_720067).sum := by decide
  have hdescent : baseEnd_720067 < baseStart_720067 := by decide
  rcases family_descends (prefixWord ++ tailWord_720067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720115 : List Nat := [1, 1, 1, 2, 2, 6, 1, 3, 4]
def baseStart_720115 : Nat := 118140960795 + 720115 * 2 ^ 59
def prefixEnd_720115 : Nat := 4983230072969 + 3 ^ 40 * 720115 * 2
def baseEnd_720115 : Nat := 164340054005580124644781

theorem tailTrace_720115 : CollatzResearch.WordTrace tailWord_720115 prefixEnd_720115 164340054005580124644781 := by
  unfold tailWord_720115
  simp only [CollatzResearch.WordTrace]
  refine ⟨26264751786153815695705799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17509834524102543797137199 26264751786153815695705799)
  ·
    refine ⟨39397127679230723543558699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26264751786153815695705799 39397127679230723543558699)
    ·
      refine ⟨59095691518846085315338049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39397127679230723543558699 59095691518846085315338049)
      ·
        refine ⟨44321768639134563986503537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59095691518846085315338049 44321768639134563986503537)
        ·
          refine ⟨33241326479350922989877653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44321768639134563986503537 33241326479350922989877653)
          ·
            refine ⟨1558187178719574515150515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33241326479350922989877653 1558187178719574515150515)
            ·
              refine ⟨2337280768079361772725773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1558187178719574515150515 2337280768079361772725773)
              ·
                refine ⟨876480288029760664772165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2337280768079361772725773 876480288029760664772165)
                ·
                  refine ⟨164340054005580124644781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 876480288029760664772165 164340054005580124644781)
                  ·
                    rfl

theorem cell21_720115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 4].length) (baseStart_720115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720115 prefixEnd_720115 := by exact prefixLift 720115
  have htrace : WordTrace (prefixWord ++ tailWord_720115) baseStart_720115 baseEnd_720115 := by
    simpa [prefixWord, tailWord_720115, baseEnd_720115] using wordTrace_append hprefix tailTrace_720115
  have hstable : (prefixWord ++ tailWord_720115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720115).length < 2 ^ (prefixWord ++ tailWord_720115).sum := by decide
  have hdescent : baseEnd_720115 < baseStart_720115 := by decide
  rcases family_descends (prefixWord ++ tailWord_720115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720129 : List Nat := [1, 2, 4, 1, 1, 3, 2, 7]
def baseStart_720129 : Nat := 118140960795 + 720129 * 2 ^ 59
def prefixEnd_720129 : Nat := 4983230072969 + 3 ^ 40 * 720129 * 2
def baseEnd_720129 : Nat := 54781082998773070470473

theorem tailTrace_720129 : CollatzResearch.WordTrace tailWord_720129 prefixEnd_720129 54781082998773070470473 := by
  unfold tailWord_720129
  simp only [CollatzResearch.WordTrace]
  refine ⟨26265262408103096086715441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17510174938735397391143627 26265262408103096086715441)
  ·
    refine ⟨19698946806077322065036581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26265262408103096086715441 19698946806077322065036581)
    ·
      refine ⟨3693552526139497887194359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19698946806077322065036581 3693552526139497887194359)
      ·
        refine ⟨5540328789209246830791539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3693552526139497887194359 5540328789209246830791539)
        ·
          refine ⟨8310493183813870246187309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5540328789209246830791539 8310493183813870246187309)
          ·
            refine ⟨3116434943930201342320241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8310493183813870246187309 3116434943930201342320241)
            ·
              refine ⟨2337326207947651006740181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3116434943930201342320241 2337326207947651006740181)
              ·
                refine ⟨54781082998773070470473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2337326207947651006740181 54781082998773070470473)
                ·
                  rfl

theorem cell21_720129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 7].length) (baseStart_720129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720129 prefixEnd_720129 := by exact prefixLift 720129
  have htrace : WordTrace (prefixWord ++ tailWord_720129) baseStart_720129 baseEnd_720129 := by
    simpa [prefixWord, tailWord_720129, baseEnd_720129] using wordTrace_append hprefix tailTrace_720129
  have hstable : (prefixWord ++ tailWord_720129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720129).length < 2 ^ (prefixWord ++ tailWord_720129).sum := by decide
  have hdescent : baseEnd_720129 < baseStart_720129 := by decide
  rcases family_descends (prefixWord ++ tailWord_720129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720146 : List Nat := [3, 2, 4, 2, 10]
def baseStart_720146 : Nat := 118140960795 + 720146 * 2 ^ 59
def prefixEnd_720146 : Nat := 4983230072969 + 3 ^ 40 * 720146 * 2
def baseEnd_720146 : Nat := 2028976896641122958371

theorem tailTrace_720146 : CollatzResearch.WordTrace tailWord_720146 prefixEnd_720146 2028976896641122958371 := by
  unfold tailWord_720146
  simp only [CollatzResearch.WordTrace]
  refine ⟨6566470612260376997521073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17510588299361005326722861 6566470612260376997521073)
  ·
    refine ⟨4924852959195282748140805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6566470612260376997521073 4924852959195282748140805)
    ·
      refine ⟨923409929849115515276401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4924852959195282748140805 923409929849115515276401)
      ·
        refine ⟨692557447386836636457301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 923409929849115515276401 692557447386836636457301)
        ·
          refine ⟨2028976896641122958371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 692557447386836636457301 2028976896641122958371)
          ·
            rfl

theorem cell21_720146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 10].length) (baseStart_720146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720146 prefixEnd_720146 := by exact prefixLift 720146
  have htrace : WordTrace (prefixWord ++ tailWord_720146) baseStart_720146 baseEnd_720146 := by
    simpa [prefixWord, tailWord_720146, baseEnd_720146] using wordTrace_append hprefix tailTrace_720146
  have hstable : (prefixWord ++ tailWord_720146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720146).length < 2 ^ (prefixWord ++ tailWord_720146).sum := by decide
  have hdescent : baseEnd_720146 < baseStart_720146 := by decide
  rcases family_descends (prefixWord ++ tailWord_720146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720236 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 5]
def baseStart_720236 : Nat := 118140960795 + 720236 * 2 ^ 59
def prefixEnd_720236 : Nat := 4983230072969 + 3 ^ 40 * 720236 * 2
def baseEnd_720236 : Nat := 164367667854110803127867

theorem tailTrace_720236 : CollatzResearch.WordTrace tailWord_720236 prefixEnd_720236 164367667854110803127867 := by
  unfold tailWord_720236
  simp only [CollatzResearch.WordTrace]
  refine ⟨13134582509357726680430281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17512776679143635573907041 13134582509357726680430281)
  ·
    refine ⟨9850936882018295010322711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13134582509357726680430281 9850936882018295010322711)
    ·
      refine ⟨14776405323027442515484067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9850936882018295010322711 14776405323027442515484067)
      ·
        refine ⟨22164607984541163773226101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14776405323027442515484067 22164607984541163773226101)
        ·
          refine ⟨2077931998550734103739947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22164607984541163773226101 2077931998550734103739947)
          ·
            refine ⟨3116897997826101155609921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2077931998550734103739947 3116897997826101155609921)
            ·
              refine ⟨2337673498369575866707441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3116897997826101155609921 2337673498369575866707441)
              ·
                refine ⟨1753255123777181900030581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2337673498369575866707441 1753255123777181900030581)
                ·
                  refine ⟨164367667854110803127867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1753255123777181900030581 164367667854110803127867)
                  ·
                    rfl

theorem cell21_720236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_720236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720236 prefixEnd_720236 := by exact prefixLift 720236
  have htrace : WordTrace (prefixWord ++ tailWord_720236) baseStart_720236 baseEnd_720236 := by
    simpa [prefixWord, tailWord_720236, baseEnd_720236] using wordTrace_append hprefix tailTrace_720236
  have hstable : (prefixWord ++ tailWord_720236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720236).length < 2 ^ (prefixWord ++ tailWord_720236).sum := by decide
  have hdescent : baseEnd_720236 < baseStart_720236 := by decide
  rcases family_descends (prefixWord ++ tailWord_720236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720270 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_720270 : Nat := 118140960795 + 720270 * 2 ^ 59
def prefixEnd_720270 : Nat := 4983230072969 + 3 ^ 40 * 720270 * 2
def baseEnd_720270 : Nat := 164375427117334299561131

theorem tailTrace_720270 : CollatzResearch.WordTrace tailWord_720270 prefixEnd_720270 164375427117334299561131 := by
  unfold tailWord_720270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3283800637574034645949783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17513603400394851445065509 3283800637574034645949783)
  ·
    refine ⟨4925700956361051968924675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3283800637574034645949783 4925700956361051968924675)
    ·
      refine ⟨7388551434541577953387013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4925700956361051968924675 7388551434541577953387013)
      ·
        refine ⟨1385353393976545866260065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7388551434541577953387013 1385353393976545866260065)
        ·
          refine ⟨1039015045482409399695049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1385353393976545866260065 1039015045482409399695049)
          ·
            refine ⟨779261284111807049771287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1039015045482409399695049 779261284111807049771287)
            ·
              refine ⟨1168891926167710574656931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779261284111807049771287 1168891926167710574656931)
              ·
                refine ⟨1753337889251565861985397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168891926167710574656931 1753337889251565861985397)
                ·
                  refine ⟨164375427117334299561131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1753337889251565861985397 164375427117334299561131)
                  ·
                    rfl

theorem cell21_720270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_720270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720270 prefixEnd_720270 := by exact prefixLift 720270
  have htrace : WordTrace (prefixWord ++ tailWord_720270) baseStart_720270 baseEnd_720270 := by
    simpa [prefixWord, tailWord_720270, baseEnd_720270] using wordTrace_append hprefix tailTrace_720270
  have hstable : (prefixWord ++ tailWord_720270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720270).length < 2 ^ (prefixWord ++ tailWord_720270).sum := by decide
  have hdescent : baseEnd_720270 < baseStart_720270 := by decide
  rcases family_descends (prefixWord ++ tailWord_720270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720281 : List Nat := [1, 2, 1, 2, 1, 6, 2, 6]
def baseStart_720281 : Nat := 118140960795 + 720281 * 2 ^ 59
def prefixEnd_720281 : Nat := 4983230072969 + 3 ^ 40 * 720281 * 2
def baseEnd_720281 : Nat := 54792645822400241625925

theorem tailTrace_720281 : CollatzResearch.WordTrace tailWord_720281 prefixEnd_720281 54792645822400241625925 := by
  unfold tailWord_720281
  simp only [CollatzResearch.WordTrace]
  refine ⟨26270806303552426046248697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17513870869034950697499131 26270806303552426046248697)
  ·
    refine ⟨19703104727664319534686523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26270806303552426046248697 19703104727664319534686523)
    ·
      refine ⟨29554657091496479302029785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19703104727664319534686523 29554657091496479302029785)
      ·
        refine ⟨22165992818622359476522339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29554657091496479302029785 22165992818622359476522339)
        ·
          refine ⟨33248989227933539214783509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22165992818622359476522339 33248989227933539214783509)
          ·
            refine ⟨1558546370059384650692977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33248989227933539214783509 1558546370059384650692977)
            ·
              refine ⟨1168909777544538488019733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1558546370059384650692977 1168909777544538488019733)
              ·
                refine ⟨54792645822400241625925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1168909777544538488019733 54792645822400241625925)
                ·
                  rfl

theorem cell21_720281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 6].length) (baseStart_720281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720281 prefixEnd_720281 := by exact prefixLift 720281
  have htrace : WordTrace (prefixWord ++ tailWord_720281) baseStart_720281 baseEnd_720281 := by
    simpa [prefixWord, tailWord_720281, baseEnd_720281] using wordTrace_append hprefix tailTrace_720281
  have hstable : (prefixWord ++ tailWord_720281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720281).length < 2 ^ (prefixWord ++ tailWord_720281).sum := by decide
  have hdescent : baseEnd_720281 < baseStart_720281 := by decide
  rcases family_descends (prefixWord ++ tailWord_720281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720414 : List Nat := [4, 3, 3, 1, 2, 1, 1, 3, 3]
def baseStart_720414 : Nat := 118140960795 + 720414 * 2 ^ 59
def prefixEnd_720414 : Nat := 4983230072969 + 3 ^ 40 * 720414 * 2
def baseEnd_720414 : Nat := 164408289879222049160837

theorem tailTrace_720414 : CollatzResearch.WordTrace tailWord_720414 prefixEnd_720414 164408289879222049160837 := by
  unfold tailWord_720414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3284457151508823720105037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17517104808047059840560197 3284457151508823720105037)
  ·
    refine ⟨1231671431815808895039389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3284457151508823720105037 1231671431815808895039389)
    ·
      refine ⟨461876786930928335639771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1231671431815808895039389 461876786930928335639771)
      ·
        refine ⟨692815180396392503459657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461876786930928335639771 692815180396392503459657)
        ·
          refine ⟨519611385297294377594743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 692815180396392503459657 519611385297294377594743)
          ·
            refine ⟨779417077945941566392115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519611385297294377594743 779417077945941566392115)
            ·
              refine ⟨1169125616918912349588173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779417077945941566392115 1169125616918912349588173)
              ·
                refine ⟨438422106344592131095565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1169125616918912349588173 438422106344592131095565)
                ·
                  refine ⟨164408289879222049160837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 438422106344592131095565 164408289879222049160837)
                  ·
                    rfl

theorem cell21_720414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_720414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720414 prefixEnd_720414 := by exact prefixLift 720414
  have htrace : WordTrace (prefixWord ++ tailWord_720414) baseStart_720414 baseEnd_720414 := by
    simpa [prefixWord, tailWord_720414, baseEnd_720414] using wordTrace_append hprefix tailTrace_720414
  have hstable : (prefixWord ++ tailWord_720414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720414).length < 2 ^ (prefixWord ++ tailWord_720414).sum := by decide
  have hdescent : baseEnd_720414 < baseStart_720414 := by decide
  rcases family_descends (prefixWord ++ tailWord_720414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720498 : List Nat := [3, 2, 1, 2, 3, 1, 4, 2, 3]
def baseStart_720498 : Nat := 118140960795 + 720498 * 2 ^ 59
def prefixEnd_720498 : Nat := 4983230072969 + 3 ^ 40 * 720498 * 2
def baseEnd_720498 : Nat := 164427459823656569760665

theorem tailTrace_720498 : CollatzResearch.WordTrace tailWord_720498 prefixEnd_720498 164427459823656569760665 := by
  unfold tailWord_720498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6569680235941568026724537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17519147295844181404598765 6569680235941568026724537)
  ·
    refine ⟨4927260176956176020043403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6569680235941568026724537 4927260176956176020043403)
    ·
      refine ⟨7390890265434264030065105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4927260176956176020043403 7390890265434264030065105)
      ·
        refine ⟨5543167699075698022548829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7390890265434264030065105 5543167699075698022548829)
        ·
          refine ⟨2078687887153386758455811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5543167699075698022548829 2078687887153386758455811)
          ·
            refine ⟨3118031830730080137683717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078687887153386758455811 3118031830730080137683717)
            ·
              refine ⟨584630968261890025815697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3118031830730080137683717 584630968261890025815697)
              ·
                refine ⟨438473226196417519361773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584630968261890025815697 438473226196417519361773)
                ·
                  refine ⟨164427459823656569760665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 438473226196417519361773 164427459823656569760665)
                  ·
                    rfl

theorem cell21_720498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_720498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720498 prefixEnd_720498 := by exact prefixLift 720498
  have htrace : WordTrace (prefixWord ++ tailWord_720498) baseStart_720498 baseEnd_720498 := by
    simpa [prefixWord, tailWord_720498, baseEnd_720498] using wordTrace_append hprefix tailTrace_720498
  have hstable : (prefixWord ++ tailWord_720498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720498).length < 2 ^ (prefixWord ++ tailWord_720498).sum := by decide
  have hdescent : baseEnd_720498 < baseStart_720498 := by decide
  rcases family_descends (prefixWord ++ tailWord_720498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720509 : List Nat := [1, 4, 1, 1, 4, 1, 3, 6]
def baseStart_720509 : Nat := 118140960795 + 720509 * 2 ^ 59
def prefixEnd_720509 : Nat := 4983230072969 + 3 ^ 40 * 720509 * 2
def baseEnd_720509 : Nat := 54809990057840998359103

theorem tailTrace_720509 : CollatzResearch.WordTrace tailWord_720509 prefixEnd_720509 54809990057840998359103 := by
  unfold tailWord_720509
  simp only [CollatzResearch.WordTrace]
  refine ⟨26279122146726420985548581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17519414764484280657032387 26279122146726420985548581)
  ·
    refine ⟨4927335402511203934790359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26279122146726420985548581 4927335402511203934790359)
    ·
      refine ⟨7391003103766805902185539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4927335402511203934790359 7391003103766805902185539)
      ·
        refine ⟨11086504655650208853278309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7391003103766805902185539 11086504655650208853278309)
        ·
          refine ⟨2078719622934414159989683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11086504655650208853278309 2078719622934414159989683)
          ·
            refine ⟨3118079434401621239984525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078719622934414159989683 3118079434401621239984525)
            ·
              refine ⟨1169279787900607964994197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3118079434401621239984525 1169279787900607964994197)
              ·
                refine ⟨54809990057840998359103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1169279787900607964994197 54809990057840998359103)
                ·
                  rfl

theorem cell21_720509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 6].length) (baseStart_720509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720509 prefixEnd_720509 := by exact prefixLift 720509
  have htrace : WordTrace (prefixWord ++ tailWord_720509) baseStart_720509 baseEnd_720509 := by
    simpa [prefixWord, tailWord_720509, baseEnd_720509] using wordTrace_append hprefix tailTrace_720509
  have hstable : (prefixWord ++ tailWord_720509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720509).length < 2 ^ (prefixWord ++ tailWord_720509).sum := by decide
  have hdescent : baseEnd_720509 < baseStart_720509 := by decide
  rcases family_descends (prefixWord ++ tailWord_720509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720523 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 5]
def baseStart_720523 : Nat := 118140960795 + 720523 * 2 ^ 59
def prefixEnd_720523 : Nat := 4983230072969 + 3 ^ 40 * 720523 * 2
def baseEnd_720523 : Nat := 164433165164262081843947

theorem tailTrace_720523 : CollatzResearch.WordTrace tailWord_720523 prefixEnd_720523 164433165164262081843947 := by
  unfold tailWord_720523
  simp only [CollatzResearch.WordTrace]
  refine ⟨26279632768675701376558223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17519755179117134251038815 26279632768675701376558223)
  ·
    refine ⟨39419449153013552064837335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26279632768675701376558223 39419449153013552064837335)
    ·
      refine ⟨59129173729520328097256003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39419449153013552064837335 59129173729520328097256003)
      ·
        refine ⟨88693760594280492145884005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59129173729520328097256003 88693760594280492145884005)
        ·
          refine ⟨16630080111427592277353251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88693760594280492145884005 16630080111427592277353251)
          ·
            refine ⟨24945120167141388416029877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16630080111427592277353251 24945120167141388416029877)
            ·
              refine ⟨2338605015669505164002801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24945120167141388416029877 2338605015669505164002801)
              ·
                refine ⟨1753953761752128873002101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2338605015669505164002801 1753953761752128873002101)
                ·
                  refine ⟨164433165164262081843947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1753953761752128873002101 164433165164262081843947)
                  ·
                    rfl

theorem cell21_720523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 5].length) (baseStart_720523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720523 prefixEnd_720523 := by exact prefixLift 720523
  have htrace : WordTrace (prefixWord ++ tailWord_720523) baseStart_720523 baseEnd_720523 := by
    simpa [prefixWord, tailWord_720523, baseEnd_720523] using wordTrace_append hprefix tailTrace_720523
  have hstable : (prefixWord ++ tailWord_720523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720523).length < 2 ^ (prefixWord ++ tailWord_720523).sum := by decide
  have hdescent : baseEnd_720523 < baseStart_720523 := by decide
  rcases family_descends (prefixWord ++ tailWord_720523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720526 : List Nat := [4, 1, 1, 3, 1, 3, 3, 5]
def baseStart_720526 : Nat := 118140960795 + 720526 * 2 ^ 59
def prefixEnd_720526 : Nat := 4983230072969 + 3 ^ 40 * 720526 * 2
def baseEnd_720526 : Nat := 54811283268378247764647

theorem tailTrace_720526 : CollatzResearch.WordTrace tailWord_720526 prefixEnd_720526 54811283268378247764647 := by
  unfold tailWord_720526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3284967773458104111114679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17519828125109888592611621 3284967773458104111114679)
  ·
    refine ⟨4927451660187156166672019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3284967773458104111114679 4927451660187156166672019)
    ·
      refine ⟨7391177490280734250008029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4927451660187156166672019 7391177490280734250008029)
      ·
        refine ⟨2771691558855275343753011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7391177490280734250008029 2771691558855275343753011)
        ·
          refine ⟨4157537338282913015629517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2771691558855275343753011 4157537338282913015629517)
          ·
            refine ⟨1559076501856092380861069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4157537338282913015629517 1559076501856092380861069)
            ·
              refine ⟨584653688196034642822901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1559076501856092380861069 584653688196034642822901)
              ·
                refine ⟨54811283268378247764647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 584653688196034642822901 54811283268378247764647)
                ·
                  rfl

theorem cell21_720526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_720526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720526 prefixEnd_720526 := by exact prefixLift 720526
  have htrace : WordTrace (prefixWord ++ tailWord_720526) baseStart_720526 baseEnd_720526 := by
    simpa [prefixWord, tailWord_720526, baseEnd_720526] using wordTrace_append hprefix tailTrace_720526
  have hstable : (prefixWord ++ tailWord_720526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720526).length < 2 ^ (prefixWord ++ tailWord_720526).sum := by decide
  have hdescent : baseEnd_720526 < baseStart_720526 := by decide
  rcases family_descends (prefixWord ++ tailWord_720526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720546 : List Nat := [3, 3, 1, 4, 2, 1, 1, 2, 4]
def baseStart_720546 : Nat := 118140960795 + 720546 * 2 ^ 59
def prefixEnd_720546 : Nat := 4983230072969 + 3 ^ 40 * 720546 * 2
def baseEnd_720546 : Nat := 164438414077619152960567

theorem tailTrace_720546 : CollatzResearch.WordTrace tailWord_720546 prefixEnd_720546 164438414077619152960567 := by
  unfold tailWord_720546
  simp only [CollatzResearch.WordTrace]
  refine ⟨6570117911898094076161373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17520314431728250869763661 6570117911898094076161373)
  ·
    refine ⟨2463794216961785278560515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6570117911898094076161373 2463794216961785278560515)
    ·
      refine ⟨3695691325442677917840773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2463794216961785278560515 3695691325442677917840773)
      ·
        refine ⟨692942123520502109595145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3695691325442677917840773 692942123520502109595145)
        ·
          refine ⟨519706592640376582196359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 692942123520502109595145 519706592640376582196359)
          ·
            refine ⟨779559888960564873294539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519706592640376582196359 779559888960564873294539)
            ·
              refine ⟨1169339833440847309941809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779559888960564873294539 1169339833440847309941809)
              ·
                refine ⟨877004875080635482456357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1169339833440847309941809 877004875080635482456357)
                ·
                  refine ⟨164438414077619152960567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 877004875080635482456357 164438414077619152960567)
                  ·
                    rfl

theorem cell21_720546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_720546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720546 prefixEnd_720546 := by exact prefixLift 720546
  have htrace : WordTrace (prefixWord ++ tailWord_720546) baseStart_720546 baseEnd_720546 := by
    simpa [prefixWord, tailWord_720546, baseEnd_720546] using wordTrace_append hprefix tailTrace_720546
  have hstable : (prefixWord ++ tailWord_720546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720546).length < 2 ^ (prefixWord ++ tailWord_720546).sum := by decide
  have hdescent : baseEnd_720546 < baseStart_720546 := by decide
  rcases family_descends (prefixWord ++ tailWord_720546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720557 : List Nat := [1, 5, 2, 1, 1, 1, 1, 6, 3]
def baseStart_720557 : Nat := 118140960795 + 720557 * 2 ^ 59
def prefixEnd_720557 : Nat := 4983230072969 + 3 ^ 40 * 720557 * 2
def baseEnd_720557 : Nat := 164440924427485578277211

theorem tailTrace_720557 : CollatzResearch.WordTrace tailWord_720557 prefixEnd_720557 164440924427485578277211 := by
  unfold tailWord_720557
  simp only [CollatzResearch.WordTrace]
  refine ⟨26280872850552525183295925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17520581900368350122197283 26280872850552525183295925)
  ·
    refine ⟨2463831829739299235933993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26280872850552525183295925 2463831829739299235933993)
    ·
      refine ⟨1847873872304474426950495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2463831829739299235933993 1847873872304474426950495)
      ·
        refine ⟨2771810808456711640425743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1847873872304474426950495 2771810808456711640425743)
        ·
          refine ⟨4157716212685067460638615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2771810808456711640425743 4157716212685067460638615)
          ·
            refine ⟨6236574319027601190957923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4157716212685067460638615 6236574319027601190957923)
            ·
              refine ⟨9354861478541401786436885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6236574319027601190957923 9354861478541401786436885)
              ·
                refine ⟨438509131806628208739229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9354861478541401786436885 438509131806628208739229)
                ·
                  refine ⟨164440924427485578277211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 438509131806628208739229 164440924427485578277211)
                  ·
                    rfl

theorem cell21_720557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_720557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720557 prefixEnd_720557 := by exact prefixLift 720557
  have htrace : WordTrace (prefixWord ++ tailWord_720557) baseStart_720557 baseEnd_720557 := by
    simpa [prefixWord, tailWord_720557, baseEnd_720557] using wordTrace_append hprefix tailTrace_720557
  have hstable : (prefixWord ++ tailWord_720557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720557).length < 2 ^ (prefixWord ++ tailWord_720557).sum := by decide
  have hdescent : baseEnd_720557 < baseStart_720557 := by decide
  rcases family_descends (prefixWord ++ tailWord_720557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720616 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 5]
def baseStart_720616 : Nat := 118140960795 + 720616 * 2 ^ 59
def prefixEnd_720616 : Nat := 4983230072969 + 3 ^ 40 * 720616 * 2
def baseEnd_720616 : Nat := 164454389031314586793757

theorem tailTrace_720616 : CollatzResearch.WordTrace tailWord_720616 prefixEnd_720616 164454389031314586793757 := by
  unfold tailWord_720616
  simp only [CollatzResearch.WordTrace]
  refine ⟨13141512378669389129846851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17522016504892518839795801 13141512378669389129846851)
  ·
    refine ⟨19712268568004083694770277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13141512378669389129846851 19712268568004083694770277)
    ·
      refine ⟨3696050356500765692769427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19712268568004083694770277 3696050356500765692769427)
      ·
        refine ⟨5544075534751148539154141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3696050356500765692769427 5544075534751148539154141)
        ·
          refine ⟨2079028325531680702182803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5544075534751148539154141 2079028325531680702182803)
          ·
            refine ⟨3118542488297521053274205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079028325531680702182803 3118542488297521053274205)
            ·
              refine ⟨1169453433111570394977827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3118542488297521053274205 1169453433111570394977827)
              ·
                refine ⟨1754180149667355592466741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1169453433111570394977827 1754180149667355592466741)
                ·
                  refine ⟨164454389031314586793757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1754180149667355592466741 164454389031314586793757)
                  ·
                    rfl

theorem cell21_720616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_720616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720616 prefixEnd_720616 := by exact prefixLift 720616
  have htrace : WordTrace (prefixWord ++ tailWord_720616) baseStart_720616 baseEnd_720616 := by
    simpa [prefixWord, tailWord_720616, baseEnd_720616] using wordTrace_append hprefix tailTrace_720616
  have hstable : (prefixWord ++ tailWord_720616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720616).length < 2 ^ (prefixWord ++ tailWord_720616).sum := by decide
  have hdescent : baseEnd_720616 < baseStart_720616 := by decide
  rcases family_descends (prefixWord ++ tailWord_720616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720692 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 7]
def baseStart_720692 : Nat := 118140960795 + 720692 * 2 ^ 59
def prefixEnd_720692 : Nat := 4983230072969 + 3 ^ 40 * 720692 * 2
def baseEnd_720692 : Nat := 164471733266755343526935

theorem tailTrace_720692 : CollatzResearch.WordTrace tailWord_720692 prefixEnd_720692 164471733266755343526935 := by
  unfold tailWord_720692
  simp only [CollatzResearch.WordTrace]
  refine ⟨13142898352531721619730165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17523864470042295492973553 13142898352531721619730165)
  ·
    refine ⟨1232146720549848901849703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13142898352531721619730165 1232146720549848901849703)
    ·
      refine ⟨1848220080824773352774555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1232146720549848901849703 1848220080824773352774555)
      ·
        refine ⟨2772330121237160029161833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1848220080824773352774555 2772330121237160029161833)
        ·
          refine ⟨2079247590927870021871375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2772330121237160029161833 2079247590927870021871375)
          ·
            refine ⟨3118871386391805032807063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079247590927870021871375 3118871386391805032807063)
            ·
              refine ⟨4678307079587707549210595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118871386391805032807063 4678307079587707549210595)
              ·
                refine ⟨7017460619381561323815893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4678307079587707549210595 7017460619381561323815893)
                ·
                  refine ⟨164471733266755343526935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7017460619381561323815893 164471733266755343526935)
                  ·
                    rfl

theorem cell21_720692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_720692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720692 prefixEnd_720692 := by exact prefixLift 720692
  have htrace : WordTrace (prefixWord ++ tailWord_720692) baseStart_720692 baseEnd_720692 := by
    simpa [prefixWord, tailWord_720692, baseEnd_720692] using wordTrace_append hprefix tailTrace_720692
  have hstable : (prefixWord ++ tailWord_720692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720692).length < 2 ^ (prefixWord ++ tailWord_720692).sum := by decide
  have hdescent : baseEnd_720692 < baseStart_720692 := by decide
  rcases family_descends (prefixWord ++ tailWord_720692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720740 : List Nat := [2, 3, 1, 1, 5, 1, 3, 1, 4]
def baseStart_720740 : Nat := 118140960795 + 720740 * 2 ^ 59
def prefixEnd_720740 : Nat := 4983230072969 + 3 ^ 40 * 720740 * 2
def baseEnd_720740 : Nat := 164482687520717926726837

theorem tailTrace_720740 : CollatzResearch.WordTrace tailWord_720740 prefixEnd_720740 164482687520717926726837 := by
  unfold tailWord_720740
  simp only [CollatzResearch.WordTrace]
  refine ⟨13143773704444773718603837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17525031605926364958138449 13143773704444773718603837)
  ·
    refine ⟨4928915139166790144476439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13143773704444773718603837 4928915139166790144476439)
    ·
      refine ⟨7393372708750185216714659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4928915139166790144476439 7393372708750185216714659)
      ·
        refine ⟨11090059063125277825071989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7393372708750185216714659 11090059063125277825071989)
        ·
          refine ⟨1039693037167994796100499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11090059063125277825071989 1039693037167994796100499)
          ·
            refine ⟨1559539555751992194150749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039693037167994796100499 1559539555751992194150749)
            ·
              refine ⟨584827333406997072806531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1559539555751992194150749 584827333406997072806531)
              ·
                refine ⟨877241000110495609209797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584827333406997072806531 877241000110495609209797)
                ·
                  refine ⟨164482687520717926726837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 877241000110495609209797 164482687520717926726837)
                  ·
                    rfl

theorem cell21_720740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_720740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720740 prefixEnd_720740 := by exact prefixLift 720740
  have htrace : WordTrace (prefixWord ++ tailWord_720740) baseStart_720740 baseEnd_720740 := by
    simpa [prefixWord, tailWord_720740, baseEnd_720740] using wordTrace_append hprefix tailTrace_720740
  have hstable : (prefixWord ++ tailWord_720740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720740).length < 2 ^ (prefixWord ++ tailWord_720740).sum := by decide
  have hdescent : baseEnd_720740 < baseStart_720740 := by decide
  rcases family_descends (prefixWord ++ tailWord_720740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720799 : List Nat := [1, 1, 2, 5, 3, 1, 1, 3, 4]
def baseStart_720799 : Nat := 118140960795 + 720799 * 2 ^ 59
def prefixEnd_720799 : Nat := 4983230072969 + 3 ^ 40 * 720799 * 2
def baseEnd_720799 : Nat := 164496152124546935243383

theorem tailTrace_720799 : CollatzResearch.WordTrace tailWord_720799 prefixEnd_720799 164496152124546935243383 := by
  unfold tailWord_720799
  simp only [CollatzResearch.WordTrace]
  refine ⟨26289699315675800513605451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17526466210450533675736967 26289699315675800513605451)
  ·
    refine ⟨39434548973513700770408177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26289699315675800513605451 39434548973513700770408177)
    ·
      refine ⟨29575911730135275577806133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39434548973513700770408177 29575911730135275577806133)
      ·
        refine ⟨2772741724700182085419325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29575911730135275577806133 2772741724700182085419325)
        ·
          refine ⟨1039778146762568282032247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2772741724700182085419325 1039778146762568282032247)
          ·
            refine ⟨1559667220143852423048371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039778146762568282032247 1559667220143852423048371)
            ·
              refine ⟨2339500830215778634572557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1559667220143852423048371 2339500830215778634572557)
              ·
                refine ⟨877312811330916987964709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2339500830215778634572557 877312811330916987964709)
                ·
                  refine ⟨164496152124546935243383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 877312811330916987964709 164496152124546935243383)
                  ·
                    rfl

theorem cell21_720799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 4].length) (baseStart_720799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720799 prefixEnd_720799 := by exact prefixLift 720799
  have htrace : WordTrace (prefixWord ++ tailWord_720799) baseStart_720799 baseEnd_720799 := by
    simpa [prefixWord, tailWord_720799, baseEnd_720799] using wordTrace_append hprefix tailTrace_720799
  have hstable : (prefixWord ++ tailWord_720799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720799).length < 2 ^ (prefixWord ++ tailWord_720799).sum := by decide
  have hdescent : baseEnd_720799 < baseStart_720799 := by decide
  rcases family_descends (prefixWord ++ tailWord_720799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720903 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 5]
def baseStart_720903 : Nat := 118140960795 + 720903 * 2 ^ 59
def prefixEnd_720903 : Nat := 4983230072969 + 3 ^ 40 * 720903 * 2
def baseEnd_720903 : Nat := 164519886341465865509837

theorem tailTrace_720903 : CollatzResearch.WordTrace tailWord_720903 prefixEnd_720903 164519886341465865509837 := by
  unfold tailWord_720903
  simp only [CollatzResearch.WordTrace]
  refine ⟨26293492507299026275391363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17528995004866017516927575 26293492507299026275391363)
  ·
    refine ⟨39440238760948539413087045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26293492507299026275391363 39440238760948539413087045)
    ·
      refine ⟨7395044767677851139953821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39440238760948539413087045 7395044767677851139953821)
      ·
        refine ⟨2773141787879194177482683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7395044767677851139953821 2773141787879194177482683)
        ·
          refine ⟨4159712681818791266224025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773141787879194177482683 4159712681818791266224025)
          ·
            refine ⟨3119784511364093449668019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4159712681818791266224025 3119784511364093449668019)
            ·
              refine ⟨4679676767046140174502029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3119784511364093449668019 4679676767046140174502029)
              ·
                refine ⟨1754878787642302565438261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4679676767046140174502029 1754878787642302565438261)
                ·
                  refine ⟨164519886341465865509837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1754878787642302565438261 164519886341465865509837)
                  ·
                    rfl

theorem cell21_720903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 5].length) (baseStart_720903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720903 prefixEnd_720903 := by exact prefixLift 720903
  have htrace : WordTrace (prefixWord ++ tailWord_720903) baseStart_720903 baseEnd_720903 := by
    simpa [prefixWord, tailWord_720903, baseEnd_720903] using wordTrace_append hprefix tailTrace_720903
  have hstable : (prefixWord ++ tailWord_720903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720903).length < 2 ^ (prefixWord ++ tailWord_720903).sum := by decide
  have hdescent : baseEnd_720903 < baseStart_720903 := by decide
  rcases family_descends (prefixWord ++ tailWord_720903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720982 : List Nat := [5, 2, 2, 1, 1, 1, 2, 7]
def baseStart_720982 : Nat := 118140960795 + 720982 * 2 ^ 59
def prefixEnd_720982 : Nat := 4983230072969 + 3 ^ 40 * 720982 * 2
def baseEnd_720982 : Nat := 54845971739259761231003

theorem tailTrace_720982 : CollatzResearch.WordTrace tailWord_720982 prefixEnd_720982 54845971739259761231003 := by
  unfold tailWord_720982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1643523367125801422969825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17530915916008548511678133 1643523367125801422969825)
  ·
    refine ⟨1232642525344351067227369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1643523367125801422969825 1232642525344351067227369)
    ·
      refine ⟨924481894008263300420527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1232642525344351067227369 924481894008263300420527)
      ·
        refine ⟨1386722841012394950630791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 924481894008263300420527 1386722841012394950630791)
        ·
          refine ⟨2080084261518592425946187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1386722841012394950630791 2080084261518592425946187)
          ·
            refine ⟨3120126392277888638919281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080084261518592425946187 3120126392277888638919281)
            ·
              refine ⟨2340094794208416479189461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3120126392277888638919281 2340094794208416479189461)
              ·
                refine ⟨54845971739259761231003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2340094794208416479189461 54845971739259761231003)
                ·
                  rfl

theorem cell21_720982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_720982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_720982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_720982 prefixEnd_720982 := by exact prefixLift 720982
  have htrace : WordTrace (prefixWord ++ tailWord_720982) baseStart_720982 baseEnd_720982 := by
    simpa [prefixWord, tailWord_720982, baseEnd_720982] using wordTrace_append hprefix tailTrace_720982
  have hstable : (prefixWord ++ tailWord_720982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720982).length < 2 ^ (prefixWord ++ tailWord_720982).sum := by decide
  have hdescent : baseEnd_720982 < baseStart_720982 := by decide
  rcases family_descends (prefixWord ++ tailWord_720982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721007 : List Nat := [1, 1, 2, 1, 3, 13]
def baseStart_721007 : Nat := 118140960795 + 721007 * 2 ^ 59
def prefixEnd_721007 : Nat := 4983230072969 + 3 ^ 40 * 721007 * 2
def baseEnd_721007 : Nat := 6094208168829066510233

theorem tailTrace_721007 : CollatzResearch.WordTrace tailWord_721007 prefixEnd_721007 6094208168829066510233 := by
  unfold tailWord_721007
  simp only [CollatzResearch.WordTrace]
  refine ⟨26297285698922252037177275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17531523799281501358118183 26297285698922252037177275)
  ·
    refine ⟨39445928548383378055765913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26297285698922252037177275 39445928548383378055765913)
    ·
      refine ⟨29584446411287533541824435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39445928548383378055765913 29584446411287533541824435)
      ·
        refine ⟨44376669616931300312736653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29584446411287533541824435 44376669616931300312736653)
        ·
          refine ⟨16641251106349237617276245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44376669616931300312736653 16641251106349237617276245)
          ·
            refine ⟨6094208168829066510233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 16641251106349237617276245 6094208168829066510233)
            ·
              rfl

theorem cell21_721007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 13].length) (baseStart_721007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721007 prefixEnd_721007 := by exact prefixLift 721007
  have htrace : WordTrace (prefixWord ++ tailWord_721007) baseStart_721007 baseEnd_721007 := by
    simpa [prefixWord, tailWord_721007, baseEnd_721007] using wordTrace_append hprefix tailTrace_721007
  have hstable : (prefixWord ++ tailWord_721007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721007).length < 2 ^ (prefixWord ++ tailWord_721007).sum := by decide
  have hdescent : baseEnd_721007 < baseStart_721007 := by decide
  rcases family_descends (prefixWord ++ tailWord_721007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721010 : List Nat := [3, 2, 1, 2, 2, 2, 1, 4, 4]
def baseStart_721010 : Nat := 118140960795 + 721010 * 2 ^ 59
def prefixEnd_721010 : Nat := 4983230072969 + 3 ^ 40 * 721010 * 2
def baseEnd_721010 : Nat := 164544305199257457226285

theorem tailTrace_721010 : CollatzResearch.WordTrace tailWord_721010 prefixEnd_721010 164544305199257457226285 := by
  unfold tailWord_721010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6574348779477845887384121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17531596745274255699690989 6574348779477845887384121)
  ·
    refine ⟨4930761584608384415538091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6574348779477845887384121 4930761584608384415538091)
    ·
      refine ⟨7396142376912576623307137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4930761584608384415538091 7396142376912576623307137)
      ·
        refine ⟨5547106782684432467480353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7396142376912576623307137 5547106782684432467480353)
        ·
          refine ⟨4160330087013324350610265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5547106782684432467480353 4160330087013324350610265)
          ·
            refine ⟨3120247565259993262957699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4160330087013324350610265 3120247565259993262957699)
            ·
              refine ⟨4680371347889989894436549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120247565259993262957699 4680371347889989894436549)
              ·
                refine ⟨877569627729373105206853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4680371347889989894436549 877569627729373105206853)
                ·
                  refine ⟨164544305199257457226285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 877569627729373105206853 164544305199257457226285)
                  ·
                    rfl

theorem cell21_721010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_721010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721010 prefixEnd_721010 := by exact prefixLift 721010
  have htrace : WordTrace (prefixWord ++ tailWord_721010) baseStart_721010 baseEnd_721010 := by
    simpa [prefixWord, tailWord_721010, baseEnd_721010] using wordTrace_append hprefix tailTrace_721010
  have hstable : (prefixWord ++ tailWord_721010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721010).length < 2 ^ (prefixWord ++ tailWord_721010).sum := by decide
  have hdescent : baseEnd_721010 < baseStart_721010 := by decide
  rcases family_descends (prefixWord ++ tailWord_721010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721083 : List Nat := [1, 1, 1, 1, 1, 2, 6, 8]
def baseStart_721083 : Nat := 118140960795 + 721083 * 2 ^ 59
def prefixEnd_721083 : Nat := 4983230072969 + 3 ^ 40 * 721083 * 2
def baseEnd_721083 : Nat := 54853654931275184169823

theorem tailTrace_721083 : CollatzResearch.WordTrace tailWord_721083 prefixEnd_721083 54853654931275184169823 := by
  unfold tailWord_721083
  simp only [CollatzResearch.WordTrace]
  refine ⟨26300057646646917016943903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17533371764431278011295935 26300057646646917016943903)
  ·
    refine ⟨39450086469970375525415855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26300057646646917016943903 39450086469970375525415855)
    ·
      refine ⟨59175129704955563288123783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39450086469970375525415855 59175129704955563288123783)
      ·
        refine ⟨88762694557433344932185675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59175129704955563288123783 88762694557433344932185675)
        ·
          refine ⟨133144041836150017398278513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88762694557433344932185675 133144041836150017398278513)
          ·
            refine ⟨99858031377112513048708885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133144041836150017398278513 99858031377112513048708885)
            ·
              refine ⟨4680845220802149049158229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99858031377112513048708885 4680845220802149049158229)
              ·
                refine ⟨54853654931275184169823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4680845220802149049158229 54853654931275184169823)
                ·
                  rfl

theorem cell21_721083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 8].length) (baseStart_721083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721083 prefixEnd_721083 := by exact prefixLift 721083
  have htrace : WordTrace (prefixWord ++ tailWord_721083) baseStart_721083 baseEnd_721083 := by
    simpa [prefixWord, tailWord_721083, baseEnd_721083] using wordTrace_append hprefix tailTrace_721083
  have hstable : (prefixWord ++ tailWord_721083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721083).length < 2 ^ (prefixWord ++ tailWord_721083).sum := by decide
  have hdescent : baseEnd_721083 < baseStart_721083 := by decide
  rcases family_descends (prefixWord ++ tailWord_721083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721114 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 7]
def baseStart_721114 : Nat := 118140960795 + 721114 * 2 ^ 59
def prefixEnd_721114 : Nat := 4983230072969 + 3 ^ 40 * 721114 * 2
def baseEnd_721114 : Nat := 164568039416176387492739

theorem tailTrace_721114 : CollatzResearch.WordTrace tailWord_721114 prefixEnd_721114 164568039416176387492739 := by
  unfold tailWord_721114
  simp only [CollatzResearch.WordTrace]
  refine ⟨6575297077383652327830599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17534125539689739540881597 6575297077383652327830599)
  ·
    refine ⟨9862945616075478491745899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6575297077383652327830599 9862945616075478491745899)
    ·
      refine ⟨14794418424113217737618849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9862945616075478491745899 14794418424113217737618849)
      ·
        refine ⟨11095813818084913303214137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14794418424113217737618849 11095813818084913303214137)
        ·
          refine ⟨8321860363563684977410603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11095813818084913303214137 8321860363563684977410603)
          ·
            refine ⟨12482790545345527466115905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8321860363563684977410603 12482790545345527466115905)
            ·
              refine ⟨9362092909009145599586929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12482790545345527466115905 9362092909009145599586929)
              ·
                refine ⟨7021569681756859199690197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9362092909009145599586929 7021569681756859199690197)
                ·
                  refine ⟨164568039416176387492739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7021569681756859199690197 164568039416176387492739)
                  ·
                    rfl

theorem cell21_721114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_721114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721114 prefixEnd_721114 := by exact prefixLift 721114
  have htrace : WordTrace (prefixWord ++ tailWord_721114) baseStart_721114 baseEnd_721114 := by
    simpa [prefixWord, tailWord_721114, baseEnd_721114] using wordTrace_append hprefix tailTrace_721114
  have hstable : (prefixWord ++ tailWord_721114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721114).length < 2 ^ (prefixWord ++ tailWord_721114).sum := by decide
  have hdescent : baseEnd_721114 < baseStart_721114 := by decide
  rcases family_descends (prefixWord ++ tailWord_721114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721117 : List Nat := [1, 4, 3, 2, 1, 3, 7]
def baseStart_721117 : Nat := 118140960795 + 721117 * 2 ^ 59
def prefixEnd_721117 : Nat := 4983230072969 + 3 ^ 40 * 721117 * 2
def baseEnd_721117 : Nat := 18285413784116560993637

theorem tailTrace_721117 : CollatzResearch.WordTrace tailWord_721117 prefixEnd_721117 18285413784116560993637 := by
  unfold tailWord_721117
  simp only [CollatzResearch.WordTrace]
  refine ⟨26301297728523740823681605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17534198485682493882454403 26301297728523740823681605)
  ·
    refine ⟨4931493324098201404440301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26301297728523740823681605 4931493324098201404440301)
    ·
      refine ⟨1849309996536825526665113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4931493324098201404440301 1849309996536825526665113)
      ·
        refine ⟨1386982497402619144998835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1849309996536825526665113 1386982497402619144998835)
        ·
          refine ⟨2080473746103928717498253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1386982497402619144998835 2080473746103928717498253)
          ·
            refine ⟨780177654788973269061845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2080473746103928717498253 780177654788973269061845)
            ·
              refine ⟨18285413784116560993637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 780177654788973269061845 18285413784116560993637)
              ·
                rfl

theorem cell21_721117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 7].length) (baseStart_721117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721117 prefixEnd_721117 := by exact prefixLift 721117
  have htrace : WordTrace (prefixWord ++ tailWord_721117) baseStart_721117 baseEnd_721117 := by
    simpa [prefixWord, tailWord_721117, baseEnd_721117] using wordTrace_append hprefix tailTrace_721117
  have hstable : (prefixWord ++ tailWord_721117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721117).length < 2 ^ (prefixWord ++ tailWord_721117).sum := by decide
  have hdescent : baseEnd_721117 < baseStart_721117 := by decide
  rcases family_descends (prefixWord ++ tailWord_721117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721182 : List Nat := [4, 3, 2, 1, 1, 2, 1, 4, 3]
def baseStart_721182 : Nat := 118140960795 + 721182 * 2 ^ 59
def prefixEnd_721182 : Nat := 4983230072969 + 3 ^ 40 * 721182 * 2
def baseEnd_721182 : Nat := 164583557942623380359267

theorem tailTrace_721182 : CollatzResearch.WordTrace tailWord_721182 prefixEnd_721182 164583557942623380359267 := by
  unfold tailWord_721182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3287958559161032115599725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17535778982192171283198533 3287958559161032115599725)
  ·
    refine ⟨1232984459685387043349897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3287958559161032115599725 1232984459685387043349897)
    ·
      refine ⟨924738344764040282512423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1232984459685387043349897 924738344764040282512423)
      ·
        refine ⟨1387107517146060423768635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 924738344764040282512423 1387107517146060423768635)
        ·
          refine ⟨2080661275719090635652953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1387107517146060423768635 2080661275719090635652953)
          ·
            refine ⟨1560495956789317976739715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2080661275719090635652953 1560495956789317976739715)
            ·
              refine ⟨2340743935183976965109573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1560495956789317976739715 2340743935183976965109573)
              ·
                refine ⟨438889487846995680958045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2340743935183976965109573 438889487846995680958045)
                ·
                  refine ⟨164583557942623380359267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 438889487846995680958045 164583557942623380359267)
                  ·
                    rfl

theorem cell21_721182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_721182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721182 prefixEnd_721182 := by exact prefixLift 721182
  have htrace : WordTrace (prefixWord ++ tailWord_721182) baseStart_721182 baseEnd_721182 := by
    simpa [prefixWord, tailWord_721182, baseEnd_721182] using wordTrace_append hprefix tailTrace_721182
  have hstable : (prefixWord ++ tailWord_721182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721182).length < 2 ^ (prefixWord ++ tailWord_721182).sum := by decide
  have hdescent : baseEnd_721182 < baseStart_721182 := by decide
  rcases family_descends (prefixWord ++ tailWord_721182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721255 : List Nat := [1, 1, 5, 1, 3, 2, 3, 1, 4]
def baseStart_721255 : Nat := 118140960795 + 721255 * 2 ^ 59
def prefixEnd_721255 : Nat := 4983230072969 + 3 ^ 40 * 721255 * 2
def baseEnd_721255 : Nat := 164600217537191475642451

theorem tailTrace_721255 : CollatzResearch.WordTrace tailWord_721255 prefixEnd_721255 164600217537191475642451 := by
  unfold tailWord_721255
  simp only [CollatzResearch.WordTrace]
  refine ⟨26306331002023790392205219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17537554001349193594803479 26306331002023790392205219)
  ·
    refine ⟨39459496503035685588307829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26306331002023790392205219 39459496503035685588307829)
    ·
      refine ⟨3699327797159595523903859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39459496503035685588307829 3699327797159595523903859)
      ·
        refine ⟨5548991695739393285855789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3699327797159595523903859 5548991695739393285855789)
        ·
          refine ⟨2080871885902272482195921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5548991695739393285855789 2080871885902272482195921)
          ·
            refine ⟨1560653914426704361646941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2080871885902272482195921 1560653914426704361646941)
            ·
              refine ⟨585245217910014135617603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1560653914426704361646941 585245217910014135617603)
              ·
                refine ⟨877867826865021203426405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585245217910014135617603 877867826865021203426405)
                ·
                  refine ⟨164600217537191475642451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 877867826865021203426405 164600217537191475642451)
                  ·
                    rfl

theorem cell21_721255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 4].length) (baseStart_721255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721255 prefixEnd_721255 := by exact prefixLift 721255
  have htrace : WordTrace (prefixWord ++ tailWord_721255) baseStart_721255 baseEnd_721255 := by
    simpa [prefixWord, tailWord_721255, baseEnd_721255] using wordTrace_append hprefix tailTrace_721255
  have hstable : (prefixWord ++ tailWord_721255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721255).length < 2 ^ (prefixWord ++ tailWord_721255).sum := by decide
  have hdescent : baseEnd_721255 < baseStart_721255 := by decide
  rcases family_descends (prefixWord ++ tailWord_721255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721269 : List Nat := [1, 3, 4, 1, 2, 1, 4, 5]
def baseStart_721269 : Nat := 118140960795 + 721269 * 2 ^ 59
def prefixEnd_721269 : Nat := 4983230072969 + 3 ^ 40 * 721269 * 2
def baseEnd_721269 : Nat := 54867804175976854136363

theorem tailTrace_721269 : CollatzResearch.WordTrace tailWord_721269 prefixEnd_721269 54867804175976854136363 := by
  unfold tailWord_721269
  simp only [CollatzResearch.WordTrace]
  refine ⟨26306841623973070783214861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17537894415982047188809907 26306841623973070783214861)
  ·
    refine ⟨9865065608989901543705573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26306841623973070783214861 9865065608989901543705573)
    ·
      refine ⟨1849699801685606539444795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9865065608989901543705573 1849699801685606539444795)
      ·
        refine ⟨2774549702528409809167193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849699801685606539444795 2774549702528409809167193)
        ·
          refine ⟨2080912276896307356875395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2774549702528409809167193 2080912276896307356875395)
          ·
            refine ⟨3121368415344461035313093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080912276896307356875395 3121368415344461035313093)
            ·
              refine ⟨585256577877086444121205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3121368415344461035313093 585256577877086444121205)
              ·
                refine ⟨54867804175976854136363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 585256577877086444121205 54867804175976854136363)
                ·
                  rfl

theorem cell21_721269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 5].length) (baseStart_721269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721269 prefixEnd_721269 := by exact prefixLift 721269
  have htrace : WordTrace (prefixWord ++ tailWord_721269) baseStart_721269 baseEnd_721269 := by
    simpa [prefixWord, tailWord_721269, baseEnd_721269] using wordTrace_append hprefix tailTrace_721269
  have hstable : (prefixWord ++ tailWord_721269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721269).length < 2 ^ (prefixWord ++ tailWord_721269).sum := by decide
  have hdescent : baseEnd_721269 < baseStart_721269 := by decide
  rcases family_descends (prefixWord ++ tailWord_721269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721314 : List Nat := [3, 3, 1, 2, 1, 1, 3, 3, 4]
def baseStart_721314 : Nat := 118140960795 + 721314 * 2 ^ 59
def prefixEnd_721314 : Nat := 4983230072969 + 3 ^ 40 * 721314 * 2
def baseEnd_721314 : Nat := 164613682141020484158997

theorem tailTrace_721314 : CollatzResearch.WordTrace tailWord_721314 prefixEnd_721314 164613682141020484158997 := by
  unfold tailWord_721314
  simp only [CollatzResearch.WordTrace]
  refine ⟨6577120727202510867150749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17538988605873362312401997 6577120727202510867150749)
  ·
    refine ⟨2466420272700941575181531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6577120727202510867150749 2466420272700941575181531)
    ·
      refine ⟨3699630409051412362772297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2466420272700941575181531 3699630409051412362772297)
      ·
        refine ⟨2774722806788559272079223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3699630409051412362772297 2774722806788559272079223)
        ·
          refine ⟨4162084210182838908118835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2774722806788559272079223 4162084210182838908118835)
          ·
            refine ⟨6243126315274258362178253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162084210182838908118835 6243126315274258362178253)
            ·
              refine ⟨2341172368227846885816845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6243126315274258362178253 2341172368227846885816845)
              ·
                refine ⟨877939638085442582181317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2341172368227846885816845 877939638085442582181317)
                ·
                  refine ⟨164613682141020484158997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 877939638085442582181317 164613682141020484158997)
                  ·
                    rfl

theorem cell21_721314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_721314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721314 prefixEnd_721314 := by exact prefixLift 721314
  have htrace : WordTrace (prefixWord ++ tailWord_721314) baseStart_721314 baseEnd_721314 := by
    simpa [prefixWord, tailWord_721314, baseEnd_721314] using wordTrace_append hprefix tailTrace_721314
  have hstable : (prefixWord ++ tailWord_721314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721314).length < 2 ^ (prefixWord ++ tailWord_721314).sum := by decide
  have hdescent : baseEnd_721314 < baseStart_721314 := by decide
  rcases family_descends (prefixWord ++ tailWord_721314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721345 : List Nat := [1, 2, 7, 1, 10]
def baseStart_721345 : Nat := 118140960795 + 721345 * 2 ^ 59
def prefixEnd_721345 : Nat := 4983230072969 + 3 ^ 40 * 721345 * 2
def baseEnd_721345 : Nat := 2032355021770016285707

theorem tailTrace_721345 : CollatzResearch.WordTrace tailWord_721345 prefixEnd_721345 2032355021770016285707 := by
  unfold tailWord_721345
  simp only [CollatzResearch.WordTrace]
  refine ⟨26309613571697735762981489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17539742381131823841987659 26309613571697735762981489)
  ·
    refine ⟨19732210178773301822236117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26309613571697735762981489 19732210178773301822236117)
    ·
      refine ⟨462473676064999261458659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 19732210178773301822236117 462473676064999261458659)
      ·
        refine ⟨693710514097498892187989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462473676064999261458659 693710514097498892187989)
        ·
          refine ⟨2032355021770016285707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 693710514097498892187989 2032355021770016285707)
          ·
            rfl

theorem cell21_721345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 10].length) (baseStart_721345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721345 prefixEnd_721345 := by exact prefixLift 721345
  have htrace : WordTrace (prefixWord ++ tailWord_721345) baseStart_721345 baseEnd_721345 := by
    simpa [prefixWord, tailWord_721345, baseEnd_721345] using wordTrace_append hprefix tailTrace_721345
  have hstable : (prefixWord ++ tailWord_721345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721345).length < 2 ^ (prefixWord ++ tailWord_721345).sum := by decide
  have hdescent : baseEnd_721345 < baseStart_721345 := by decide
  rcases family_descends (prefixWord ++ tailWord_721345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721362 : List Nat := [3, 2, 2, 4, 1, 2, 1, 6]
def baseStart_721362 : Nat := 118140960795 + 721362 * 2 ^ 59
def prefixEnd_721362 : Nat := 4983230072969 + 3 ^ 40 * 721362 * 2
def baseEnd_721362 : Nat := 54874878798327689119633

theorem tailTrace_721362 : CollatzResearch.WordTrace tailWord_721362 prefixEnd_721362 54874878798327689119633 := by
  unfold tailWord_721362
  simp only [CollatzResearch.WordTrace]
  refine ⟨6577558403159036916587585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17540155741757431777566893 6577558403159036916587585)
  ·
    refine ⟨4933168802369277687440689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6577558403159036916587585 4933168802369277687440689)
    ·
      refine ⟨3699876601776958265580517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4933168802369277687440689 3699876601776958265580517)
      ·
        refine ⟨693726862833179674796347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3699876601776958265580517 693726862833179674796347)
        ·
          refine ⟨1040590294249769512194521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693726862833179674796347 1040590294249769512194521)
          ·
            refine ⟨780442720687327134145891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1040590294249769512194521 780442720687327134145891)
            ·
              refine ⟨1170664081030990701218837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 780442720687327134145891 1170664081030990701218837)
              ·
                refine ⟨54874878798327689119633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1170664081030990701218837 54874878798327689119633)
                ·
                  rfl

theorem cell21_721362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_721362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721362 prefixEnd_721362 := by exact prefixLift 721362
  have htrace : WordTrace (prefixWord ++ tailWord_721362) baseStart_721362 baseEnd_721362 := by
    simpa [prefixWord, tailWord_721362, baseEnd_721362] using wordTrace_append hprefix tailTrace_721362
  have hstable : (prefixWord ++ tailWord_721362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721362).length < 2 ^ (prefixWord ++ tailWord_721362).sum := by decide
  have hdescent : baseEnd_721362 < baseStart_721362 := by decide
  rcases family_descends (prefixWord ++ tailWord_721362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721469 : List Nat := [1, 4, 1, 3, 2, 2, 3, 2, 3]
def baseStart_721469 : Nat := 118140960795 + 721469 * 2 ^ 59
def prefixEnd_721469 : Nat := 4983230072969 + 3 ^ 40 * 721469 * 2
def baseEnd_721469 : Nat := 164649055252774659075347

theorem tailTrace_721469 : CollatzResearch.WordTrace tailWord_721469 prefixEnd_721469 164649055252774659075347 := by
  unfold tailWord_721469
  simp only [CollatzResearch.WordTrace]
  refine ⟨26314136223248504940495461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17542757482165669960330307 26314136223248504940495461)
  ·
    refine ⟨4933900541859094676342899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26314136223248504940495461 4933900541859094676342899)
    ·
      refine ⟨7400850812788642014514349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4933900541859094676342899 7400850812788642014514349)
      ·
        refine ⟨2775319054795740755442881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7400850812788642014514349 2775319054795740755442881)
        ·
          refine ⟨2081489291096805566582161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2775319054795740755442881 2081489291096805566582161)
          ·
            refine ⟨1561116968322604174936621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2081489291096805566582161 1561116968322604174936621)
            ·
              refine ⟨585418863120976565601233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1561116968322604174936621 585418863120976565601233)
              ·
                refine ⟨439064147340732424200925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585418863120976565601233 439064147340732424200925)
                ·
                  refine ⟨164649055252774659075347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439064147340732424200925 164649055252774659075347)
                  ·
                    rfl

theorem cell21_721469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_721469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721469 prefixEnd_721469 := by exact prefixLift 721469
  have htrace : WordTrace (prefixWord ++ tailWord_721469) baseStart_721469 baseEnd_721469 := by
    simpa [prefixWord, tailWord_721469, baseEnd_721469] using wordTrace_append hprefix tailTrace_721469
  have hstable : (prefixWord ++ tailWord_721469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721469).length < 2 ^ (prefixWord ++ tailWord_721469).sum := by decide
  have hdescent : baseEnd_721469 < baseStart_721469 := by decide
  rcases family_descends (prefixWord ++ tailWord_721469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721511 : List Nat := [1, 1, 5, 1, 1, 1, 1, 7, 3]
def baseStart_721511 : Nat := 118140960795 + 721511 * 2 ^ 59
def prefixEnd_721511 : Nat := 4983230072969 + 3 ^ 40 * 721511 * 2
def baseEnd_721511 : Nat := 164658640224991919375261

theorem tailTrace_721511 : CollatzResearch.WordTrace tailWord_721511 prefixEnd_721511 164658640224991919375261 := by
  unfold tailWord_721511
  simp only [CollatzResearch.WordTrace]
  refine ⟨26315668089096346113524387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17543778726064230742349591 26315668089096346113524387)
  ·
    refine ⟨39473502133644519170286581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26315668089096346113524387 39473502133644519170286581)
    ·
      refine ⟨3700640825029173672214367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39473502133644519170286581 3700640825029173672214367)
      ·
        refine ⟨5550961237543760508321551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3700640825029173672214367 5550961237543760508321551)
        ·
          refine ⟨8326441856315640762482327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5550961237543760508321551 8326441856315640762482327)
          ·
            refine ⟨12489662784473461143723491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8326441856315640762482327 12489662784473461143723491)
            ·
              refine ⟨18734494176710191715585237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12489662784473461143723491 18734494176710191715585237)
              ·
                refine ⟨439089707266645118334029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18734494176710191715585237 439089707266645118334029)
                ·
                  refine ⟨164658640224991919375261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439089707266645118334029 164658640224991919375261)
                  ·
                    rfl

theorem cell21_721511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 3].length) (baseStart_721511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721511 prefixEnd_721511 := by exact prefixLift 721511
  have htrace : WordTrace (prefixWord ++ tailWord_721511) baseStart_721511 baseEnd_721511 := by
    simpa [prefixWord, tailWord_721511, baseEnd_721511] using wordTrace_append hprefix tailTrace_721511
  have hstable : (prefixWord ++ tailWord_721511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721511).length < 2 ^ (prefixWord ++ tailWord_721511).sum := by decide
  have hdescent : baseEnd_721511 < baseStart_721511 := by decide
  rcases family_descends (prefixWord ++ tailWord_721511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721539 : List Nat := [1, 1, 1, 3, 3, 1, 5, 6]
def baseStart_721539 : Nat := 118140960795 + 721539 * 2 ^ 59
def prefixEnd_721539 : Nat := 4983230072969 + 3 ^ 40 * 721539 * 2
def baseEnd_721539 : Nat := 54888343402156697636179

theorem tailTrace_721539 : CollatzResearch.WordTrace tailWord_721539 prefixEnd_721539 54888343402156697636179 := by
  unfold tailWord_721539
  simp only [CollatzResearch.WordTrace]
  refine ⟨26316689332994906895543671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17544459555329937930362447 26316689332994906895543671)
  ·
    refine ⟨39475033999492360343315507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26316689332994906895543671 39475033999492360343315507)
    ·
      refine ⟨59212550999238540514973261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39475033999492360343315507 59212550999238540514973261)
      ·
        refine ⟨22204706624714452693114973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59212550999238540514973261 22204706624714452693114973)
        ·
          refine ⟨8326764984267919759918115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22204706624714452693114973 8326764984267919759918115)
          ·
            refine ⟨12490147476401879639877173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8326764984267919759918115 12490147476401879639877173)
            ·
              refine ⟨1170951325912676216238485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12490147476401879639877173 1170951325912676216238485)
              ·
                refine ⟨54888343402156697636179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1170951325912676216238485 54888343402156697636179)
                ·
                  rfl

theorem cell21_721539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 6].length) (baseStart_721539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721539 prefixEnd_721539 := by exact prefixLift 721539
  have htrace : WordTrace (prefixWord ++ tailWord_721539) baseStart_721539 baseEnd_721539 := by
    simpa [prefixWord, tailWord_721539, baseEnd_721539] using wordTrace_append hprefix tailTrace_721539
  have hstable : (prefixWord ++ tailWord_721539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721539).length < 2 ^ (prefixWord ++ tailWord_721539).sum := by decide
  have hdescent : baseEnd_721539 < baseStart_721539 := by decide
  rcases family_descends (prefixWord ++ tailWord_721539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721587 : List Nat := [1, 1, 1, 2, 3, 4, 2, 4, 3]
def baseStart_721587 : Nat := 118140960795 + 721587 * 2 ^ 59
def prefixEnd_721587 : Nat := 4983230072969 + 3 ^ 40 * 721587 * 2
def baseEnd_721587 : Nat := 164675984460432676108439

theorem tailTrace_721587 : CollatzResearch.WordTrace tailWord_721587 prefixEnd_721587 164675984460432676108439 := by
  unfold tailWord_721587
  simp only [CollatzResearch.WordTrace]
  refine ⟨26318440036821011093291015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17545626691214007395527343 26318440036821011093291015)
  ·
    refine ⟨39477660055231516639936523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26318440036821011093291015 39477660055231516639936523)
    ·
      refine ⟨59216490082847274959904785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39477660055231516639936523 59216490082847274959904785)
      ·
        refine ⟨44412367562135456219928589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59216490082847274959904785 44412367562135456219928589)
        ·
          refine ⟨16654637835800796082473221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44412367562135456219928589 16654637835800796082473221)
          ·
            refine ⟨3122744594212649265463729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16654637835800796082473221 3122744594212649265463729)
            ·
              refine ⟨2342058445659486949097797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3122744594212649265463729 2342058445659486949097797)
              ·
                refine ⟨439135958561153802955837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2342058445659486949097797 439135958561153802955837)
                ·
                  refine ⟨164675984460432676108439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439135958561153802955837 164675984460432676108439)
                  ·
                    rfl

theorem cell21_721587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 3].length) (baseStart_721587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721587 prefixEnd_721587 := by exact prefixLift 721587
  have htrace : WordTrace (prefixWord ++ tailWord_721587) baseStart_721587 baseEnd_721587 := by
    simpa [prefixWord, tailWord_721587, baseEnd_721587] using wordTrace_append hprefix tailTrace_721587
  have hstable : (prefixWord ++ tailWord_721587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721587).length < 2 ^ (prefixWord ++ tailWord_721587).sum := by decide
  have hdescent : baseEnd_721587 < baseStart_721587 := by decide
  rcases family_descends (prefixWord ++ tailWord_721587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721652 : List Nat := [2, 6, 1, 1, 2, 1, 1, 3, 4]
def baseStart_721652 : Nat := 118140960795 + 721652 * 2 ^ 59
def prefixEnd_721652 : Nat := 4983230072969 + 3 ^ 40 * 721652 * 2
def baseEnd_721652 : Nat := 164690818346007007524973

theorem tailTrace_721652 : CollatzResearch.WordTrace tailWord_721652 prefixEnd_721652 164690818346007007524973 := by
  unfold tailWord_721652
  simp only [CollatzResearch.WordTrace]
  refine ⟨13160405390792763597203605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17547207187723684796271473 13160405390792763597203605)
  ·
    refine ⟨616894002693410793618919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13160405390792763597203605 616894002693410793618919)
    ·
      refine ⟨925341004040116190428379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 616894002693410793618919 925341004040116190428379)
      ·
        refine ⟨1388011506060174285642569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 925341004040116190428379 1388011506060174285642569)
        ·
          refine ⟨1041008629545130714231927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1388011506060174285642569 1041008629545130714231927)
          ·
            refine ⟨1561512944317696071347891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041008629545130714231927 1561512944317696071347891)
            ·
              refine ⟨2342269416476544107021837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561512944317696071347891 2342269416476544107021837)
              ·
                refine ⟨878351031178704040133189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2342269416476544107021837 878351031178704040133189)
                ·
                  refine ⟨164690818346007007524973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 878351031178704040133189 164690818346007007524973)
                  ·
                    rfl

theorem cell21_721652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_721652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721652 prefixEnd_721652 := by exact prefixLift 721652
  have htrace : WordTrace (prefixWord ++ tailWord_721652) baseStart_721652 baseEnd_721652 := by
    simpa [prefixWord, tailWord_721652, baseEnd_721652] using wordTrace_append hprefix tailTrace_721652
  have hstable : (prefixWord ++ tailWord_721652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721652).length < 2 ^ (prefixWord ++ tailWord_721652).sum := by decide
  have hdescent : baseEnd_721652 < baseStart_721652 := by decide
  rcases family_descends (prefixWord ++ tailWord_721652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721725 : List Nat := [1, 4, 1, 4, 2, 1, 3, 5]
def baseStart_721725 : Nat := 118140960795 + 721725 * 2 ^ 59
def prefixEnd_721725 : Nat := 4983230072969 + 3 ^ 40 * 721725 * 2
def baseEnd_721725 : Nat := 54902492646858367602719

theorem tailTrace_721725 : CollatzResearch.WordTrace tailWord_721725 prefixEnd_721725 54902492646858367602719 := by
  unfold tailWord_721725
  simp only [CollatzResearch.WordTrace]
  refine ⟨26323473310321060661814629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17548982206880707107876419 26323473310321060661814629)
  ·
    refine ⟨4935651245685198874090243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26323473310321060661814629 4935651245685198874090243)
    ·
      refine ⟨7403476868527798311135365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4935651245685198874090243 7403476868527798311135365)
      ·
        refine ⟨1388151912848962183337881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7403476868527798311135365 1388151912848962183337881)
        ·
          refine ⟨1041113934636721637503411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1388151912848962183337881 1041113934636721637503411)
          ·
            refine ⟨1561670901955082456255117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041113934636721637503411 1561670901955082456255117)
            ·
              refine ⟨585626588233155921095669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1561670901955082456255117 585626588233155921095669)
              ·
                refine ⟨54902492646858367602719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 585626588233155921095669 54902492646858367602719)
                ·
                  rfl

theorem cell21_721725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 5].length) (baseStart_721725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721725 prefixEnd_721725 := by exact prefixLift 721725
  have htrace : WordTrace (prefixWord ++ tailWord_721725) baseStart_721725 baseEnd_721725 := by
    simpa [prefixWord, tailWord_721725, baseEnd_721725] using wordTrace_append hprefix tailTrace_721725
  have hstable : (prefixWord ++ tailWord_721725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721725).length < 2 ^ (prefixWord ++ tailWord_721725).sum := by decide
  have hdescent : baseEnd_721725 < baseStart_721725 := by decide
  rcases family_descends (prefixWord ++ tailWord_721725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721736 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 6]
def baseStart_721736 : Nat := 118140960795 + 721736 * 2 ^ 59
def prefixEnd_721736 : Nat := 4983230072969 + 3 ^ 40 * 721736 * 2
def baseEnd_721736 : Nat := 164709988290441528124801

theorem tailTrace_721736 : CollatzResearch.WordTrace tailWord_721736 prefixEnd_721736 164709988290441528124801 := by
  unfold tailWord_721736
  simp only [CollatzResearch.WordTrace]
  refine ⟨13161937256640604770232531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17549249675520806360310041 13161937256640604770232531)
  ·
    refine ⟨19742905884960907155348797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13161937256640604770232531 19742905884960907155348797)
    ·
      refine ⟨7403589706860340183255799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19742905884960907155348797 7403589706860340183255799)
      ·
        refine ⟨11105384560290510274883699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7403589706860340183255799 11105384560290510274883699)
        ·
          refine ⟨16658076840435765412325549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11105384560290510274883699 16658076840435765412325549)
          ·
            refine ⟨6246778815163412029622081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16658076840435765412325549 6246778815163412029622081)
            ·
              refine ⟨4685084111372559022216561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6246778815163412029622081 4685084111372559022216561)
              ·
                refine ⟨3513813083529419266662421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4685084111372559022216561 3513813083529419266662421)
                ·
                  refine ⟨164709988290441528124801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3513813083529419266662421 164709988290441528124801)
                  ·
                    rfl

theorem cell21_721736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_721736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721736 prefixEnd_721736 := by exact prefixLift 721736
  have htrace : WordTrace (prefixWord ++ tailWord_721736) baseStart_721736 baseEnd_721736 := by
    simpa [prefixWord, tailWord_721736, baseEnd_721736] using wordTrace_append hprefix tailTrace_721736
  have hstable : (prefixWord ++ tailWord_721736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721736).length < 2 ^ (prefixWord ++ tailWord_721736).sum := by decide
  have hdescent : baseEnd_721736 < baseStart_721736 := by decide
  rcases family_descends (prefixWord ++ tailWord_721736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721753 : List Nat := [1, 2, 1, 2, 2, 4, 3, 2, 4]
def baseStart_721753 : Nat := 118140960795 + 721753 * 2 ^ 59
def prefixEnd_721753 : Nat := 4983230072969 + 3 ^ 40 * 721753 * 2
def baseEnd_721753 : Nat := 164713867922053276341433

theorem tailTrace_721753 : CollatzResearch.WordTrace tailWord_721753 prefixEnd_721753 164713867922053276341433 := by
  unfold tailWord_721753
  simp only [CollatzResearch.WordTrace]
  refine ⟨26324494554219621443833913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17549663036146414295889275 26324494554219621443833913)
  ·
    refine ⟨19743370915664716082875435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26324494554219621443833913 19743370915664716082875435)
    ·
      refine ⟨29615056373497074124313153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19743370915664716082875435 29615056373497074124313153)
      ·
        refine ⟨22211292280122805593234865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29615056373497074124313153 22211292280122805593234865)
        ·
          refine ⟨16658469210092104194926149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22211292280122805593234865 16658469210092104194926149)
          ·
            refine ⟨3123462976892269536548653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16658469210092104194926149 3123462976892269536548653)
            ·
              refine ⟨1171298616334601076205745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3123462976892269536548653 1171298616334601076205745)
              ·
                refine ⟨878473962250950807154309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1171298616334601076205745 878473962250950807154309)
                ·
                  refine ⟨164713867922053276341433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 878473962250950807154309 164713867922053276341433)
                  ·
                    rfl

theorem cell21_721753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_721753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721753 prefixEnd_721753 := by exact prefixLift 721753
  have htrace : WordTrace (prefixWord ++ tailWord_721753) baseStart_721753 baseEnd_721753 := by
    simpa [prefixWord, tailWord_721753, baseEnd_721753] using wordTrace_append hprefix tailTrace_721753
  have hstable : (prefixWord ++ tailWord_721753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721753).length < 2 ^ (prefixWord ++ tailWord_721753).sum := by decide
  have hdescent : baseEnd_721753 < baseStart_721753 := by decide
  rcases family_descends (prefixWord ++ tailWord_721753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721756 : List Nat := [2, 2, 4, 2, 1, 1, 2, 4, 3]
def baseStart_721756 : Nat := 118140960795 + 721756 * 2 ^ 59
def prefixEnd_721756 : Nat := 4983230072969 + 3 ^ 40 * 721756 * 2
def baseEnd_721756 : Nat := 164714552562925937791427

theorem tailTrace_721756 : CollatzResearch.WordTrace tailWord_721756 prefixEnd_721756 164714552562925937791427 := by
  unfold tailWord_721756
  simp only [CollatzResearch.WordTrace]
  refine ⟨13162301986604376478096561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17549735982139168637462081 13162301986604376478096561)
  ·
    refine ⟨9871726489953282358572421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13162301986604376478096561 9871726489953282358572421)
    ·
      refine ⟨1850948716866240442232329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9871726489953282358572421 1850948716866240442232329)
      ·
        refine ⟨1388211537649680331674247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1850948716866240442232329 1388211537649680331674247)
        ·
          refine ⟨2082317306474520497511371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1388211537649680331674247 2082317306474520497511371)
          ·
            refine ⟨3123475959711780746267057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082317306474520497511371 3123475959711780746267057)
            ·
              refine ⟨2342606969783835559700293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3123475959711780746267057 2342606969783835559700293)
              ·
                refine ⟨439238806834469167443805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2342606969783835559700293 439238806834469167443805)
                ·
                  refine ⟨164714552562925937791427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439238806834469167443805 164714552562925937791427)
                  ·
                    rfl

theorem cell21_721756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_721756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721756 prefixEnd_721756 := by exact prefixLift 721756
  have htrace : WordTrace (prefixWord ++ tailWord_721756) baseStart_721756 baseEnd_721756 := by
    simpa [prefixWord, tailWord_721756, baseEnd_721756] using wordTrace_append hprefix tailTrace_721756
  have hstable : (prefixWord ++ tailWord_721756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721756).length < 2 ^ (prefixWord ++ tailWord_721756).sum := by decide
  have hdescent : baseEnd_721756 < baseStart_721756 := by decide
  rcases family_descends (prefixWord ++ tailWord_721756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721790 : List Nat := [4, 2, 3, 1, 2, 2, 1, 3, 3]
def baseStart_721790 : Nat := 118140960795 + 721790 * 2 ^ 59
def prefixEnd_721790 : Nat := 4983230072969 + 3 ^ 40 * 721790 * 2
def baseEnd_721790 : Nat := 164722311826149434224691

theorem tailTrace_721790 : CollatzResearch.WordTrace tailWord_721790 prefixEnd_721790 164722311826149434224691 := by
  unfold tailWord_721790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3290730506885697095366353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17550562703390384508620549 3290730506885697095366353)
  ·
    refine ⟨2468047880164272821524765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3290730506885697095366353 2468047880164272821524765)
    ·
      refine ⟨925517955061602308071787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2468047880164272821524765 925517955061602308071787)
      ·
        refine ⟨1388276932592403462107681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 925517955061602308071787 1388276932592403462107681)
        ·
          refine ⟨1041207699444302596580761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1388276932592403462107681 1041207699444302596580761)
          ·
            refine ⟨780905774583226947435571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1041207699444302596580761 780905774583226947435571)
            ·
              refine ⟨1171358661874840421153357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 780905774583226947435571 1171358661874840421153357)
              ·
                refine ⟨439259498203065157932509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1171358661874840421153357 439259498203065157932509)
                ·
                  refine ⟨164722311826149434224691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439259498203065157932509 164722311826149434224691)
                  ·
                    rfl

theorem cell21_721790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_721790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721790 prefixEnd_721790 := by exact prefixLift 721790
  have htrace : WordTrace (prefixWord ++ tailWord_721790) baseStart_721790 baseEnd_721790 := by
    simpa [prefixWord, tailWord_721790, baseEnd_721790] using wordTrace_append hprefix tailTrace_721790
  have hstable : (prefixWord ++ tailWord_721790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721790).length < 2 ^ (prefixWord ++ tailWord_721790).sum := by decide
  have hdescent : baseEnd_721790 < baseStart_721790 := by decide
  rcases family_descends (prefixWord ++ tailWord_721790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721860 : List Nat := [2, 3, 3, 3, 1, 9]
def baseStart_721860 : Nat := 118140960795 + 721860 * 2 ^ 59
def prefixEnd_721860 : Nat := 4983230072969 + 3 ^ 40 * 721860 * 2
def baseEnd_721860 : Nat := 6101418028883143261403

theorem tailTrace_721860 : CollatzResearch.WordTrace tailWord_721860 prefixEnd_721860 6101418028883143261403 := by
  unfold tailWord_721860
  simp only [CollatzResearch.WordTrace]
  refine ⟨13164198582415989358989517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17552264776554652478652689 13164198582415989358989517)
  ·
    refine ⟨4936574468405996009621069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13164198582415989358989517 4936574468405996009621069)
    ·
      refine ⟨1851215425652248503607901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4936574468405996009621069 1851215425652248503607901)
      ·
        refine ⟨694205784619593188852963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1851215425652248503607901 694205784619593188852963)
        ·
          refine ⟨1041308676929389783279445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694205784619593188852963 1041308676929389783279445)
          ·
            refine ⟨6101418028883143261403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1041308676929389783279445 6101418028883143261403)
            ·
              rfl

theorem cell21_721860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 9].length) (baseStart_721860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721860 prefixEnd_721860 := by exact prefixLift 721860
  have htrace : WordTrace (prefixWord ++ tailWord_721860) baseStart_721860 baseEnd_721860 := by
    simpa [prefixWord, tailWord_721860, baseEnd_721860] using wordTrace_append hprefix tailTrace_721860
  have hstable : (prefixWord ++ tailWord_721860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721860).length < 2 ^ (prefixWord ++ tailWord_721860).sum := by decide
  have hdescent : baseEnd_721860 < baseStart_721860 := by decide
  rcases family_descends (prefixWord ++ tailWord_721860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721877 : List Nat := [1, 3, 2, 3, 4, 1, 1, 6]
def baseStart_721877 : Nat := 118140960795 + 721877 * 2 ^ 59
def prefixEnd_721877 : Nat := 4983230072969 + 3 ^ 40 * 721877 * 2
def baseEnd_721877 : Nat := 54914055470485538758171

theorem tailTrace_721877 : CollatzResearch.WordTrace tailWord_721877 prefixEnd_721877 54914055470485538758171 := by
  unfold tailWord_721877
  simp only [CollatzResearch.WordTrace]
  refine ⟨26329017205770390621347885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17552678137180260414231923 26329017205770390621347885)
  ·
    refine ⟨9873381452163896483005457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26329017205770390621347885 9873381452163896483005457)
    ·
      refine ⟨7405036089122922362254093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9873381452163896483005457 7405036089122922362254093)
      ·
        refine ⟨2776888533421095885845285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7405036089122922362254093 2776888533421095885845285)
        ·
          refine ⟨520666600016455478595991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2776888533421095885845285 520666600016455478595991)
          ·
            refine ⟨780999900024683217893987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520666600016455478595991 780999900024683217893987)
            ·
              refine ⟨1171499850037024826840981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 780999900024683217893987 1171499850037024826840981)
              ·
                refine ⟨54914055470485538758171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1171499850037024826840981 54914055470485538758171)
                ·
                  rfl

theorem cell21_721877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 6].length) (baseStart_721877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721877 prefixEnd_721877 := by exact prefixLift 721877
  have htrace : WordTrace (prefixWord ++ tailWord_721877) baseStart_721877 baseEnd_721877 := by
    simpa [prefixWord, tailWord_721877, baseEnd_721877] using wordTrace_append hprefix tailTrace_721877
  have hstable : (prefixWord ++ tailWord_721877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721877).length < 2 ^ (prefixWord ++ tailWord_721877).sum := by decide
  have hdescent : baseEnd_721877 < baseStart_721877 := by decide
  rcases family_descends (prefixWord ++ tailWord_721877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721978 : List Nat := [3, 1, 1, 1, 3, 1, 11]
def baseStart_721978 : Nat := 118140960795 + 721978 * 2 ^ 59
def prefixEnd_721978 : Nat := 4983230072969 + 3 ^ 40 * 721978 * 2
def baseEnd_721978 : Nat := 18307246220833653898997

theorem tailTrace_721978 : CollatzResearch.WordTrace tailWord_721978 prefixEnd_721978 18307246220833653898997 := by
  unfold tailWord_721978
  simp only [CollatzResearch.WordTrace]
  refine ⟨6583175244601121217693647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17555133985602989913849725 6583175244601121217693647)
  ·
    refine ⟨9874762866901681826540471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6583175244601121217693647 9874762866901681826540471)
    ·
      refine ⟨14812144300352522739810707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9874762866901681826540471 14812144300352522739810707)
      ·
        refine ⟨22218216450528784109716061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14812144300352522739810707 22218216450528784109716061)
        ·
          refine ⟨8331831168948294041143523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22218216450528784109716061 8331831168948294041143523)
          ·
            refine ⟨12497746753422441061715285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8331831168948294041143523 12497746753422441061715285)
            ·
              refine ⟨18307246220833653898997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12497746753422441061715285 18307246220833653898997)
              ·
                rfl

theorem cell21_721978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 11].length) (baseStart_721978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_721978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_721978 prefixEnd_721978 := by exact prefixLift 721978
  have htrace : WordTrace (prefixWord ++ tailWord_721978) baseStart_721978 baseEnd_721978 := by
    simpa [prefixWord, tailWord_721978, baseEnd_721978] using wordTrace_append hprefix tailTrace_721978
  have hstable : (prefixWord ++ tailWord_721978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721978).length < 2 ^ (prefixWord ++ tailWord_721978).sum := by decide
  have hdescent : baseEnd_721978 < baseStart_721978 := by decide
  rcases family_descends (prefixWord ++ tailWord_721978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722040 : List Nat := [2, 1, 2, 1, 1, 1, 5, 4, 4]
def baseStart_722040 : Nat := 118140960795 + 722040 * 2 ^ 59
def prefixEnd_722040 : Nat := 4983230072969 + 3 ^ 40 * 722040 * 2
def baseEnd_722040 : Nat := 164779365232204555057513

theorem tailTrace_722040 : CollatzResearch.WordTrace tailWord_722040 prefixEnd_722040 164779365232204555057513 := by
  unfold tailWord_722040
  simp only [CollatzResearch.WordTrace]
  refine ⟨13167481152089934729765787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17556641536119912973021049 13167481152089934729765787)
  ·
    refine ⟨19751221728134902094648681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13167481152089934729765787 19751221728134902094648681)
    ·
      refine ⟨14813416296101176570986511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19751221728134902094648681 14813416296101176570986511)
      ·
        refine ⟨22220124444151764856479767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14813416296101176570986511 22220124444151764856479767)
        ·
          refine ⟨33330186666227647284719651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22220124444151764856479767 33330186666227647284719651)
          ·
            refine ⟨49995279999341470927079477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33330186666227647284719651 49995279999341470927079477)
            ·
              refine ⟨4687057499938262899413701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49995279999341470927079477 4687057499938262899413701)
              ·
                refine ⟨878823281238424293640069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4687057499938262899413701 878823281238424293640069)
                ·
                  refine ⟨164779365232204555057513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 878823281238424293640069 164779365232204555057513)
                  ·
                    rfl

theorem cell21_722040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_722040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_722040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_722040 prefixEnd_722040 := by exact prefixLift 722040
  have htrace : WordTrace (prefixWord ++ tailWord_722040) baseStart_722040 baseEnd_722040 := by
    simpa [prefixWord, tailWord_722040, baseEnd_722040] using wordTrace_append hprefix tailTrace_722040
  have hstable : (prefixWord ++ tailWord_722040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722040).length < 2 ^ (prefixWord ++ tailWord_722040).sum := by decide
  have hdescent : baseEnd_722040 < baseStart_722040 := by decide
  rcases family_descends (prefixWord ++ tailWord_722040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722136 : List Nat := [2, 1, 2, 2, 5, 2, 1, 3, 3]
def baseStart_722136 : Nat := 118140960795 + 722136 * 2 ^ 59
def prefixEnd_722136 : Nat := 4983230072969 + 3 ^ 40 * 722136 * 2
def baseEnd_722136 : Nat := 164801273740129721457317

theorem tailTrace_722136 : CollatzResearch.WordTrace tailWord_722136 prefixEnd_722136 164801273740129721457317 := by
  unfold tailWord_722136
  simp only [CollatzResearch.WordTrace]
  refine ⟨13169231855916038927513131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17558975807888051903350841 13169231855916038927513131)
  ·
    refine ⟨19753847783874058391269697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13169231855916038927513131 19753847783874058391269697)
    ·
      refine ⟨14815385837905543793452273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19753847783874058391269697 14815385837905543793452273)
      ·
        refine ⟨11111539378429157845089205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14815385837905543793452273 11111539378429157845089205)
        ·
          refine ⟨1041706816727733547977113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11111539378429157845089205 1041706816727733547977113)
          ·
            refine ⟨781280112545800160982835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1041706816727733547977113 781280112545800160982835)
            ·
              refine ⟨1171920168818700241474253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 781280112545800160982835 1171920168818700241474253)
              ·
                refine ⟨439470063307012590552845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1171920168818700241474253 439470063307012590552845)
                ·
                  refine ⟨164801273740129721457317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439470063307012590552845 164801273740129721457317)
                  ·
                    rfl

theorem cell21_722136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 3].length) (baseStart_722136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_722136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_722136 prefixEnd_722136 := by exact prefixLift 722136
  have htrace : WordTrace (prefixWord ++ tailWord_722136) baseStart_722136 baseEnd_722136 := by
    simpa [prefixWord, tailWord_722136, baseEnd_722136] using wordTrace_append hprefix tailTrace_722136
  have hstable : (prefixWord ++ tailWord_722136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722136).length < 2 ^ (prefixWord ++ tailWord_722136).sum := by decide
  have hdescent : baseEnd_722136 < baseStart_722136 := by decide
  rcases family_descends (prefixWord ++ tailWord_722136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722246 : List Nat := [6, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_722246 : Nat := 118140960795 + 722246 * 2 ^ 59
def prefixEnd_722246 : Nat := 4983230072969 + 3 ^ 40 * 722246 * 2
def baseEnd_722246 : Nat := 164826377238793974623759

theorem tailTrace_722246 : CollatzResearch.WordTrace tailWord_722246 prefixEnd_722246 164826377238793974623759 := by
  unfold tailWord_722246
  simp only [CollatzResearch.WordTrace]
  refine ⟨823202366919798957547831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17561650494289044427687061 823202366919798957547831)
  ·
    refine ⟨1234803550379698436321747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 823202366919798957547831 1234803550379698436321747)
    ·
      refine ⟨1852205325569547654482621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1234803550379698436321747 1852205325569547654482621)
      ·
        refine ⟨694576997088580370430983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1852205325569547654482621 694576997088580370430983)
        ·
          refine ⟨1041865495632870555646475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694576997088580370430983 1041865495632870555646475)
          ·
            refine ⟨1562798243449305833469713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041865495632870555646475 1562798243449305833469713)
            ·
              refine ⟨1172098682586979375102285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1562798243449305833469713 1172098682586979375102285)
              ·
                refine ⟨439537005970117265663357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1172098682586979375102285 439537005970117265663357)
                ·
                  refine ⟨164826377238793974623759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439537005970117265663357 164826377238793974623759)
                  ·
                    rfl

theorem cell21_722246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_722246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_722246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_722246 prefixEnd_722246 := by exact prefixLift 722246
  have htrace : WordTrace (prefixWord ++ tailWord_722246) baseStart_722246 baseEnd_722246 := by
    simpa [prefixWord, tailWord_722246, baseEnd_722246] using wordTrace_append hprefix tailTrace_722246
  have hstable : (prefixWord ++ tailWord_722246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722246).length < 2 ^ (prefixWord ++ tailWord_722246).sum := by decide
  have hdescent : baseEnd_722246 < baseStart_722246 := by decide
  rcases family_descends (prefixWord ++ tailWord_722246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722305 : List Nat := [1, 2, 4, 3, 3, 1, 1, 3, 3]
def baseStart_722305 : Nat := 118140960795 + 722305 * 2 ^ 59
def prefixEnd_722305 : Nat := 4983230072969 + 3 ^ 40 * 722305 * 2
def baseEnd_722305 : Nat := 164839841842622983140305

theorem tailTrace_722305 : CollatzResearch.WordTrace tailWord_722305 prefixEnd_722305 164839841842622983140305 := by
  unfold tailWord_722305
  simp only [CollatzResearch.WordTrace]
  refine ⟨26344627648219819717928369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17563085098813213145285579 26344627648219819717928369)
  ·
    refine ⟨19758470736164864788446277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26344627648219819717928369 19758470736164864788446277)
    ·
      refine ⟨3704713263030912147833677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19758470736164864788446277 3704713263030912147833677)
      ·
        refine ⟨1389267473636592055437629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3704713263030912147833677 1389267473636592055437629)
        ·
          refine ⟨520975302613722020789111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1389267473636592055437629 520975302613722020789111)
          ·
            refine ⟨781462953920583031183667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520975302613722020789111 781462953920583031183667)
            ·
              refine ⟨1172194430880874546775501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 781462953920583031183667 1172194430880874546775501)
              ·
                refine ⟨439572911580327955040813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1172194430880874546775501 439572911580327955040813)
                ·
                  refine ⟨164839841842622983140305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439572911580327955040813 164839841842622983140305)
                  ·
                    rfl

theorem cell21_722305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 3].length) (baseStart_722305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_722305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_722305 prefixEnd_722305 := by exact prefixLift 722305
  have htrace : WordTrace (prefixWord ++ tailWord_722305) baseStart_722305 baseEnd_722305 := by
    simpa [prefixWord, tailWord_722305, baseEnd_722305] using wordTrace_append hprefix tailTrace_722305
  have hstable : (prefixWord ++ tailWord_722305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722305).length < 2 ^ (prefixWord ++ tailWord_722305).sum := by decide
  have hdescent : baseEnd_722305 < baseStart_722305 := by decide
  rcases family_descends (prefixWord ++ tailWord_722305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722389 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 5]
def baseStart_722389 : Nat := 118140960795 + 722389 * 2 ^ 59
def prefixEnd_722389 : Nat := 4983230072969 + 3 ^ 40 * 722389 * 2
def baseEnd_722389 : Nat := 164859011787057503740133

theorem tailTrace_722389 : CollatzResearch.WordTrace tailWord_722389 prefixEnd_722389 164859011787057503740133 := by
  unfold tailWord_722389
  simp only [CollatzResearch.WordTrace]
  refine ⟨26347691379915502063986221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17565127586610334709324147 26347691379915502063986221)
  ·
    refine ⟨9880384267468313273994833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26347691379915502063986221 9880384267468313273994833)
    ·
      refine ⟨7410288200601234955496125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9880384267468313273994833 7410288200601234955496125)
      ·
        refine ⟨2778858075225463108311047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7410288200601234955496125 2778858075225463108311047)
        ·
          refine ⟨4168287112838194662466571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2778858075225463108311047 4168287112838194662466571)
          ·
            refine ⟨6252430669257291993699857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4168287112838194662466571 6252430669257291993699857)
            ·
              refine ⟨4689323001942968995274893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6252430669257291993699857 4689323001942968995274893)
              ·
                refine ⟨1758496125728613373228085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4689323001942968995274893 1758496125728613373228085)
                ·
                  refine ⟨164859011787057503740133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1758496125728613373228085 164859011787057503740133)
                  ·
                    rfl

theorem cell21_722389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_722389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_722389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_722389 prefixEnd_722389 := by exact prefixLift 722389
  have htrace : WordTrace (prefixWord ++ tailWord_722389) baseStart_722389 baseEnd_722389 := by
    simpa [prefixWord, tailWord_722389, baseEnd_722389] using wordTrace_append hprefix tailTrace_722389
  have hstable : (prefixWord ++ tailWord_722389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722389).length < 2 ^ (prefixWord ++ tailWord_722389).sum := by decide
  have hdescent : baseEnd_722389 < baseStart_722389 := by decide
  rcases family_descends (prefixWord ++ tailWord_722389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722465 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 5]
def baseStart_722465 : Nat := 118140960795 + 722465 * 2 ^ 59
def prefixEnd_722465 : Nat := 4983230072969 + 3 ^ 40 * 722465 * 2
def baseEnd_722465 : Nat := 164876356022498260473311

theorem tailTrace_722465 : CollatzResearch.WordTrace tailWord_722465 prefixEnd_722465 164876356022498260473311 := by
  unfold tailWord_722465
  simp only [CollatzResearch.WordTrace]
  refine ⟨26350463327640167043752849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17566975551760111362501899 26350463327640167043752849)
  ·
    refine ⟨19762847495730125282814637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26350463327640167043752849 19762847495730125282814637)
    ·
      refine ⟨7411067810898796981055489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19762847495730125282814637 7411067810898796981055489)
      ·
        refine ⟨5558300858174097735791617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7411067810898796981055489 5558300858174097735791617)
        ·
          refine ⟨4168725643630573301843713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5558300858174097735791617 4168725643630573301843713)
          ·
            refine ⟨3126544232722929976382785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4168725643630573301843713 3126544232722929976382785)
            ·
              refine ⟨2344908174542197482287089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3126544232722929976382785 2344908174542197482287089)
              ·
                refine ⟨1758681130906648111715317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2344908174542197482287089 1758681130906648111715317)
                ·
                  refine ⟨164876356022498260473311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1758681130906648111715317 164876356022498260473311)
                  ·
                    rfl

theorem cell21_722465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_722465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_722465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_722465 prefixEnd_722465 := by exact prefixLift 722465
  have htrace : WordTrace (prefixWord ++ tailWord_722465) baseStart_722465 baseEnd_722465 := by
    simpa [prefixWord, tailWord_722465, baseEnd_722465] using wordTrace_append hprefix tailTrace_722465
  have hstable : (prefixWord ++ tailWord_722465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722465).length < 2 ^ (prefixWord ++ tailWord_722465).sum := by decide
  have hdescent : baseEnd_722465 < baseStart_722465 := by decide
  rcases family_descends (prefixWord ++ tailWord_722465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722637 : List Nat := [1, 6, 2, 1, 1, 3, 2, 5]
def baseStart_722637 : Nat := 118140960795 + 722637 * 2 ^ 59
def prefixEnd_722637 : Nat := 4983230072969 + 3 ^ 40 * 722637 * 2
def baseEnd_722637 : Nat := 54971869588621394535431

theorem tailTrace_722637 : CollatzResearch.WordTrace tailWord_722637 prefixEnd_722637 54971869588621394535431 := by
  unfold tailWord_722637
  simp only [CollatzResearch.WordTrace]
  refine ⟨26356736683017040419014165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17571157788678026946009443 26356736683017040419014165)
  ·
    refine ⟨1235472032016423769641289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26356736683017040419014165 1235472032016423769641289)
    ·
      refine ⟨926604024012317827230967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1235472032016423769641289 926604024012317827230967)
      ·
        refine ⟨1389906036018476740846451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 926604024012317827230967 1389906036018476740846451)
        ·
          refine ⟨2084859054027715111269677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1389906036018476740846451 2084859054027715111269677)
          ·
            refine ⟨781822145260393166726129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2084859054027715111269677 781822145260393166726129)
            ·
              refine ⟨586366608945294875044597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781822145260393166726129 586366608945294875044597)
              ·
                refine ⟨54971869588621394535431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 586366608945294875044597 54971869588621394535431)
                ·
                  rfl

theorem cell21_722637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 5].length) (baseStart_722637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_722637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_722637 prefixEnd_722637 := by exact prefixLift 722637
  have htrace : WordTrace (prefixWord ++ tailWord_722637) baseStart_722637 baseEnd_722637 := by
    simpa [prefixWord, tailWord_722637, baseEnd_722637] using wordTrace_append hprefix tailTrace_722637
  have hstable : (prefixWord ++ tailWord_722637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722637).length < 2 ^ (prefixWord ++ tailWord_722637).sum := by decide
  have hdescent : baseEnd_722637 < baseStart_722637 := by decide
  rcases family_descends (prefixWord ++ tailWord_722637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722721 : List Nat := [1, 2, 3, 2, 1, 12]
def baseStart_722721 : Nat := 118140960795 + 722721 * 2 ^ 59
def prefixEnd_722721 : Nat := 4983230072969 + 3 ^ 40 * 722721 * 2
def baseEnd_722721 : Nat := 6108695507788840896523

theorem tailTrace_722721 : CollatzResearch.WordTrace tailWord_722721 prefixEnd_722721 6108695507788840896523 := by
  unfold tailWord_722721
  simp only [CollatzResearch.WordTrace]
  refine ⟨26359800414712722765072017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17573200276475148510048011 26359800414712722765072017)
  ·
    refine ⟨19769850311034542073804013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26359800414712722765072017 19769850311034542073804013)
    ·
      refine ⟨7413693866637953277676505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19769850311034542073804013 7413693866637953277676505)
      ·
        refine ⟨5560270399978464958257379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7413693866637953277676505 5560270399978464958257379)
        ·
          refine ⟨8340405599967697437386069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5560270399978464958257379 8340405599967697437386069)
          ·
            refine ⟨6108695507788840896523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8340405599967697437386069 6108695507788840896523)
            ·
              rfl

theorem cell21_722721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 12].length) (baseStart_722721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_722721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_722721 prefixEnd_722721 := by exact prefixLift 722721
  have htrace : WordTrace (prefixWord ++ tailWord_722721) baseStart_722721 baseEnd_722721 := by
    simpa [prefixWord, tailWord_722721, baseEnd_722721] using wordTrace_append hprefix tailTrace_722721
  have hstable : (prefixWord ++ tailWord_722721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722721).length < 2 ^ (prefixWord ++ tailWord_722721).sum := by decide
  have hdescent : baseEnd_722721 < baseStart_722721 := by decide
  rcases family_descends (prefixWord ++ tailWord_722721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722724 : List Nat := [2, 3, 1, 3, 2, 1, 1, 4, 4]
def baseStart_722724 : Nat := 118140960795 + 722724 * 2 ^ 59
def prefixEnd_722724 : Nat := 4983230072969 + 3 ^ 40 * 722724 * 2
def baseEnd_722724 : Nat := 164935463351171365656115

theorem tailTrace_722724 : CollatzResearch.WordTrace tailWord_722724 prefixEnd_722724 164935463351171365656115 := by
  unfold tailWord_722724
  simp only [CollatzResearch.WordTrace]
  refine ⟨13179954916850927138715613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17573273222467902851620817 13179954916850927138715613)
  ·
    refine ⟨4942483093819097677018355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13179954916850927138715613 4942483093819097677018355)
    ·
      refine ⟨7413724640728646515527533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4942483093819097677018355 7413724640728646515527533)
      ·
        refine ⟨2780146740273242443322825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7413724640728646515527533 2780146740273242443322825)
        ·
          refine ⟨2085110055204931832492119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2780146740273242443322825 2085110055204931832492119)
          ·
            refine ⟨3127665082807397748738179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085110055204931832492119 3127665082807397748738179)
            ·
              refine ⟨4691497624211096623107269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127665082807397748738179 4691497624211096623107269)
              ·
                refine ⟨879655804539580616832613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4691497624211096623107269 879655804539580616832613)
                ·
                  refine ⟨164935463351171365656115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 879655804539580616832613 164935463351171365656115)
                  ·
                    rfl

theorem cell21_722724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_722724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_722724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_722724 prefixEnd_722724 := by exact prefixLift 722724
  have htrace : WordTrace (prefixWord ++ tailWord_722724) baseStart_722724 baseEnd_722724 := by
    simpa [prefixWord, tailWord_722724, baseEnd_722724] using wordTrace_append hprefix tailTrace_722724
  have hstable : (prefixWord ++ tailWord_722724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722724).length < 2 ^ (prefixWord ++ tailWord_722724).sum := by decide
  have hdescent : baseEnd_722724 < baseStart_722724 := by decide
  rcases family_descends (prefixWord ++ tailWord_722724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722738 : List Nat := [3, 2, 1, 1, 3, 2, 3, 6]
def baseStart_722738 : Nat := 118140960795 + 722738 * 2 ^ 59
def prefixEnd_722738 : Nat := 4983230072969 + 3 ^ 40 * 722738 * 2
def baseEnd_722738 : Nat := 54979552780636817474251

theorem tailTrace_722738 : CollatzResearch.WordTrace tailWord_722738 prefixEnd_722738 54979552780636817474251 := by
  unfold tailWord_722738
  simp only [CollatzResearch.WordTrace]
  refine ⟨6590105113912783667110217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17573613637100756445627245 6590105113912783667110217)
  ·
    refine ⟨4942578835434587750332663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6590105113912783667110217 4942578835434587750332663)
    ·
      refine ⟨7413868253151881625498995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4942578835434587750332663 7413868253151881625498995)
      ·
        refine ⟨11120802379727822438248493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7413868253151881625498995 11120802379727822438248493)
        ·
          refine ⟨4170300892397933414343185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11120802379727822438248493 4170300892397933414343185)
          ·
            refine ⟨3127725669298450060757389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4170300892397933414343185 3127725669298450060757389)
            ·
              refine ⟨1172897125986918772784021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3127725669298450060757389 1172897125986918772784021)
              ·
                refine ⟨54979552780636817474251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1172897125986918772784021 54979552780636817474251)
                ·
                  rfl

theorem cell21_722738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_722738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_722738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_722738 prefixEnd_722738 := by exact prefixLift 722738
  have htrace : WordTrace (prefixWord ++ tailWord_722738) baseStart_722738 baseEnd_722738 := by
    simpa [prefixWord, tailWord_722738, baseEnd_722738] using wordTrace_append hprefix tailTrace_722738
  have hstable : (prefixWord ++ tailWord_722738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722738).length < 2 ^ (prefixWord ++ tailWord_722738).sum := by decide
  have hdescent : baseEnd_722738 < baseStart_722738 := by decide
  rcases family_descends (prefixWord ++ tailWord_722738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722783 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 6]
def baseStart_722783 : Nat := 118140960795 + 722783 * 2 ^ 59
def prefixEnd_722783 : Nat := 4983230072969 + 3 ^ 40 * 722783 * 2
def baseEnd_722783 : Nat := 164948927955000374172661

theorem tailTrace_722783 : CollatzResearch.WordTrace tailWord_722783 prefixEnd_722783 164948927955000374172661 := by
  unfold tailWord_722783
  simp only [CollatzResearch.WordTrace]
  refine ⟨26362061740488107353829003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17574707826992071569219335 26362061740488107353829003)
  ·
    refine ⟨39543092610732161030743505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26362061740488107353829003 39543092610732161030743505)
    ·
      refine ⟨29657319458049120773057629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39543092610732161030743505 29657319458049120773057629)
      ·
        refine ⟨11121494796768420289896611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29657319458049120773057629 11121494796768420289896611)
        ·
          refine ⟨16682242195152630434844917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11121494796768420289896611 16682242195152630434844917)
          ·
            refine ⟨1563960205795559103266711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16682242195152630434844917 1563960205795559103266711)
            ·
              refine ⟨2345940308693338654900067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563960205795559103266711 2345940308693338654900067)
              ·
                refine ⟨3518910463040007982350101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2345940308693338654900067 3518910463040007982350101)
                ·
                  refine ⟨164948927955000374172661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3518910463040007982350101 164948927955000374172661)
                  ·
                    rfl

theorem cell21_722783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 6].length) (baseStart_722783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_722783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_722783 prefixEnd_722783 := by exact prefixLift 722783
  have htrace : WordTrace (prefixWord ++ tailWord_722783) baseStart_722783 baseEnd_722783 := by
    simpa [prefixWord, tailWord_722783, baseEnd_722783] using wordTrace_append hprefix tailTrace_722783
  have hstable : (prefixWord ++ tailWord_722783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722783).length < 2 ^ (prefixWord ++ tailWord_722783).sum := by decide
  have hdescent : baseEnd_722783 < baseStart_722783 := by decide
  rcases family_descends (prefixWord ++ tailWord_722783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722786 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 5]
def baseStart_722786 : Nat := 118140960795 + 722786 * 2 ^ 59
def prefixEnd_722786 : Nat := 4983230072969 + 3 ^ 40 * 722786 * 2
def baseEnd_722786 : Nat := 164949612595873035622655

theorem tailTrace_722786 : CollatzResearch.WordTrace tailWord_722786 prefixEnd_722786 164949612595873035622655 := by
  unfold tailWord_722786
  simp only [CollatzResearch.WordTrace]
  refine ⟨6590542789869309716547053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17574780772984825910792141 6590542789869309716547053)
  ·
    refine ⟨2471453546200991143705145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6590542789869309716547053 2471453546200991143705145)
    ·
      refine ⟨1853590159650743357778859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2471453546200991143705145 1853590159650743357778859)
      ·
        refine ⟨2780385239476115036668289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1853590159650743357778859 2780385239476115036668289)
        ·
          refine ⟨2085288929607086277501217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2780385239476115036668289 2085288929607086277501217)
          ·
            refine ⟨1563966697205314708125913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2085288929607086277501217 1563966697205314708125913)
            ·
              refine ⟨1172975022903986031094435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1563966697205314708125913 1172975022903986031094435)
              ·
                refine ⟨1759462534355979046641653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172975022903986031094435 1759462534355979046641653)
                ·
                  refine ⟨164949612595873035622655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1759462534355979046641653 164949612595873035622655)
                  ·
                    rfl

theorem cell21_722786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_722786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_722786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_722786 prefixEnd_722786 := by exact prefixLift 722786
  have htrace : WordTrace (prefixWord ++ tailWord_722786) baseStart_722786 baseEnd_722786 := by
    simpa [prefixWord, tailWord_722786, baseEnd_722786] using wordTrace_append hprefix tailTrace_722786
  have hstable : (prefixWord ++ tailWord_722786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722786).length < 2 ^ (prefixWord ++ tailWord_722786).sum := by decide
  have hdescent : baseEnd_722786 < baseStart_722786 := by decide
  rcases family_descends (prefixWord ++ tailWord_722786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722845 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 5]
def baseStart_722845 : Nat := 118140960795 + 722845 * 2 ^ 59
def prefixEnd_722845 : Nat := 4983230072969 + 3 ^ 40 * 722845 * 2
def baseEnd_722845 : Nat := 164963077199702044139201

theorem tailTrace_722845 : CollatzResearch.WordTrace tailWord_722845 prefixEnd_722845 164963077199702044139201 := by
  unfold tailWord_722845
  simp only [CollatzResearch.WordTrace]
  refine ⟨26364323066263491942585989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17576215377508994628390659 26364323066263491942585989)
  ·
    refine ⟨4943310574924404739234873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26364323066263491942585989 4943310574924404739234873)
    ·
      refine ⟨3707482931193303554426155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4943310574924404739234873 3707482931193303554426155)
      ·
        refine ⟨5561224396789955331639233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3707482931193303554426155 5561224396789955331639233)
        ·
          refine ⟨4170918297592466498729425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5561224396789955331639233 4170918297592466498729425)
          ·
            refine ⟨3128188723194349874047069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4170918297592466498729425 3128188723194349874047069)
            ·
              refine ⟨1173070771197881202767651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3128188723194349874047069 1173070771197881202767651)
              ·
                refine ⟨1759606156796821804151477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173070771197881202767651 1759606156796821804151477)
                ·
                  refine ⟨164963077199702044139201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1759606156796821804151477 164963077199702044139201)
                  ·
                    rfl

theorem cell21_722845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_722845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_722845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_722845 prefixEnd_722845 := by exact prefixLift 722845
  have htrace : WordTrace (prefixWord ++ tailWord_722845) baseStart_722845 baseEnd_722845 := by
    simpa [prefixWord, tailWord_722845, baseEnd_722845] using wordTrace_append hprefix tailTrace_722845
  have hstable : (prefixWord ++ tailWord_722845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722845).length < 2 ^ (prefixWord ++ tailWord_722845).sum := by decide
  have hdescent : baseEnd_722845 < baseStart_722845 := by decide
  rcases family_descends (prefixWord ++ tailWord_722845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722873 : List Nat := [1, 2, 1, 4, 2, 1, 1, 9]
def baseStart_722873 : Nat := 118140960795 + 722873 * 2 ^ 59
def prefixEnd_722873 : Nat := 4983230072969 + 3 ^ 40 * 722873 * 2
def baseEnd_722873 : Nat := 54989822393726739224159

theorem tailTrace_722873 : CollatzResearch.WordTrace tailWord_722873 prefixEnd_722873 54989822393726739224159 := by
  unfold tailWord_722873
  simp only [CollatzResearch.WordTrace]
  refine ⟨26365344310162052724605273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17576896206774701816403515 26365344310162052724605273)
  ·
    refine ⟨19774008232621539543453955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26365344310162052724605273 19774008232621539543453955)
    ·
      refine ⟨29661012348932309315180933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19774008232621539543453955 29661012348932309315180933)
      ·
        refine ⟨5561439815424807996596425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29661012348932309315180933 5561439815424807996596425)
        ·
          refine ⟨4171079861568605997447319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5561439815424807996596425 4171079861568605997447319)
          ·
            refine ⟨6256619792352908996170979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4171079861568605997447319 6256619792352908996170979)
            ·
              refine ⟨9384929688529363494256469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6256619792352908996170979 9384929688529363494256469)
              ·
                refine ⟨54989822393726739224159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9384929688529363494256469 54989822393726739224159)
                ·
                  rfl

theorem cell21_722873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 9].length) (baseStart_722873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_722873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_722873 prefixEnd_722873 := by exact prefixLift 722873
  have htrace : WordTrace (prefixWord ++ tailWord_722873) baseStart_722873 baseEnd_722873 := by
    simpa [prefixWord, tailWord_722873, baseEnd_722873] using wordTrace_append hprefix tailTrace_722873
  have hstable : (prefixWord ++ tailWord_722873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722873).length < 2 ^ (prefixWord ++ tailWord_722873).sum := by decide
  have hdescent : baseEnd_722873 < baseStart_722873 := by decide
  rcases family_descends (prefixWord ++ tailWord_722873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722904 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 5]
def baseStart_722904 : Nat := 118140960795 + 722904 * 2 ^ 59
def prefixEnd_722904 : Nat := 4983230072969 + 3 ^ 40 * 722904 * 2
def baseEnd_722904 : Nat := 164976541803531052655747

theorem tailTrace_722904 : CollatzResearch.WordTrace tailWord_722904 prefixEnd_722904 164976541803531052655747 := by
  unfold tailWord_722904
  simp only [CollatzResearch.WordTrace]
  refine ⟨13183237486524872509491883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17577649982033163345989177 13183237486524872509491883)
  ·
    refine ⟨19774856229787308764237825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13183237486524872509491883 19774856229787308764237825)
    ·
      refine ⟨14831142172340481573178369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19774856229787308764237825 14831142172340481573178369)
      ·
        refine ⟨11123356629255361179883777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14831142172340481573178369 11123356629255361179883777)
        ·
          refine ⟨8342517471941520884912833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11123356629255361179883777 8342517471941520884912833)
          ·
            refine ⟨6256888103956140663684625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8342517471941520884912833 6256888103956140663684625)
            ·
              refine ⟨4692666077967105497763469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6256888103956140663684625 4692666077967105497763469)
              ·
                refine ⟨1759749779237664561661301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4692666077967105497763469 1759749779237664561661301)
                ·
                  refine ⟨164976541803531052655747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1759749779237664561661301 164976541803531052655747)
                  ·
                    rfl

theorem cell21_722904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_722904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_722904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_722904 prefixEnd_722904 := by exact prefixLift 722904
  have htrace : WordTrace (prefixWord ++ tailWord_722904) baseStart_722904 baseEnd_722904 := by
    simpa [prefixWord, tailWord_722904, baseEnd_722904] using wordTrace_append hprefix tailTrace_722904
  have hstable : (prefixWord ++ tailWord_722904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722904).length < 2 ^ (prefixWord ++ tailWord_722904).sum := by decide
  have hdescent : baseEnd_722904 < baseStart_722904 := by decide
  rcases family_descends (prefixWord ++ tailWord_722904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722949 : List Nat := [1, 3, 1, 1, 2, 5, 8]
def baseStart_722949 : Nat := 118140960795 + 722949 * 2 ^ 59
def prefixEnd_722949 : Nat := 4983230072969 + 3 ^ 40 * 722949 * 2
def baseEnd_722949 : Nat := 18331867935180108267295

theorem tailTrace_722949 : CollatzResearch.WordTrace tailWord_722949 prefixEnd_722949 18331867935180108267295 := by
  unfold tailWord_722949
  simp only [CollatzResearch.WordTrace]
  refine ⟨26368116257886717704371901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17578744171924478469581267 26368116257886717704371901)
  ·
    refine ⟨9888043596707519139139463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26368116257886717704371901 9888043596707519139139463)
    ·
      refine ⟨14832065395061278708709195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9888043596707519139139463 14832065395061278708709195)
      ·
        refine ⟨22248098092591918063063793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14832065395061278708709195 22248098092591918063063793)
        ·
          refine ⟨16686073569443938547297845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22248098092591918063063793 16686073569443938547297845)
          ·
            refine ⟨1564319397135369238809173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16686073569443938547297845 1564319397135369238809173)
            ·
              refine ⟨18331867935180108267295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1564319397135369238809173 18331867935180108267295)
              ·
                rfl

theorem cell21_722949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 8].length) (baseStart_722949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_722949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_722949 prefixEnd_722949 := by exact prefixLift 722949
  have htrace : WordTrace (prefixWord ++ tailWord_722949) baseStart_722949 baseEnd_722949 := by
    simpa [prefixWord, tailWord_722949, baseEnd_722949] using wordTrace_append hprefix tailTrace_722949
  have hstable : (prefixWord ++ tailWord_722949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722949).length < 2 ^ (prefixWord ++ tailWord_722949).sum := by decide
  have hdescent : baseEnd_722949 < baseStart_722949 := by decide
  rcases family_descends (prefixWord ++ tailWord_722949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722983 : List Nat := [1, 1, 7, 1, 2, 1, 1, 7]
def baseStart_722983 : Nat := 118140960795 + 722983 * 2 ^ 59
def prefixEnd_722983 : Nat := 4983230072969 + 3 ^ 40 * 722983 * 2
def baseEnd_722983 : Nat := 54998190226614823612973

theorem tailTrace_722983 : CollatzResearch.WordTrace tailWord_722983 prefixEnd_722983 54998190226614823612973 := by
  unfold tailWord_722983
  simp only [CollatzResearch.WordTrace]
  refine ⟨26369356339763541511109603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17579570893175694340739735 26369356339763541511109603)
  ·
    refine ⟨39554034509645312266664405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26369356339763541511109603 39554034509645312266664405)
    ·
      refine ⟨927047683819812006249947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 39554034509645312266664405 927047683819812006249947)
      ·
        refine ⟨1390571525729718009374921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 927047683819812006249947 1390571525729718009374921)
        ·
          refine ⟨1042928644297288507031191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1390571525729718009374921 1042928644297288507031191)
          ·
            refine ⟨1564392966445932760546787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042928644297288507031191 1564392966445932760546787)
            ·
              refine ⟨2346589449668899140820181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564392966445932760546787 2346589449668899140820181)
              ·
                refine ⟨54998190226614823612973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2346589449668899140820181 54998190226614823612973)
                ·
                  rfl

theorem cell21_722983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 7].length) (baseStart_722983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_722983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_722983 prefixEnd_722983 := by exact prefixLift 722983
  have htrace : WordTrace (prefixWord ++ tailWord_722983) baseStart_722983 baseEnd_722983 := by
    simpa [prefixWord, tailWord_722983, baseEnd_722983] using wordTrace_append hprefix tailTrace_722983
  have hstable : (prefixWord ++ tailWord_722983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722983).length < 2 ^ (prefixWord ++ tailWord_722983).sum := by decide
  have hdescent : baseEnd_722983 < baseStart_722983 := by decide
  rcases family_descends (prefixWord ++ tailWord_722983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723121 : List Nat := [1, 2, 2, 5, 2, 2, 1, 2, 4]
def baseStart_723121 : Nat := 118140960795 + 723121 * 2 ^ 59
def prefixEnd_723121 : Nat := 4983230072969 + 3 ^ 40 * 723121 * 2
def baseEnd_723121 : Nat := 165026064159986897538637

theorem tailTrace_723121 : CollatzResearch.WordTrace tailWord_723121 prefixEnd_723121 165026064159986897538637 := by
  unfold tailWord_723121
  simp only [CollatzResearch.WordTrace]
  refine ⟨26374389613263591079633217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17582926408842394053088811 26374389613263591079633217)
  ·
    refine ⟨19780792209947693309724913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26374389613263591079633217 19780792209947693309724913)
    ·
      refine ⟨14835594157460769982293685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19780792209947693309724913 14835594157460769982293685)
      ·
        refine ⟨1390836952261947185840033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14835594157460769982293685 1390836952261947185840033)
        ·
          refine ⟨1043127714196460389380025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1390836952261947185840033 1043127714196460389380025)
          ·
            refine ⟨782345785647345292035019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1043127714196460389380025 782345785647345292035019)
            ·
              refine ⟨1173518678471017938052529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782345785647345292035019 1173518678471017938052529)
              ·
                refine ⟨880139008853263453539397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1173518678471017938052529 880139008853263453539397)
                ·
                  refine ⟨165026064159986897538637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 880139008853263453539397 165026064159986897538637)
                  ·
                    rfl

theorem cell21_723121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_723121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723121 prefixEnd_723121 := by exact prefixLift 723121
  have htrace : WordTrace (prefixWord ++ tailWord_723121) baseStart_723121 baseEnd_723121 := by
    simpa [prefixWord, tailWord_723121, baseEnd_723121] using wordTrace_append hprefix tailTrace_723121
  have hstable : (prefixWord ++ tailWord_723121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723121).length < 2 ^ (prefixWord ++ tailWord_723121).sum := by decide
  have hdescent : baseEnd_723121 < baseStart_723121 := by decide
  rcases family_descends (prefixWord ++ tailWord_723121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723124 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 5]
def baseStart_723124 : Nat := 118140960795 + 723124 * 2 ^ 59
def prefixEnd_723124 : Nat := 4983230072969 + 3 ^ 40 * 723124 * 2
def baseEnd_723124 : Nat := 165026748800859558988631

theorem tailTrace_723124 : CollatzResearch.WordTrace tailWord_723124 prefixEnd_723124 165026748800859558988631 := by
  unfold tailWord_723124
  simp only [CollatzResearch.WordTrace]
  refine ⟨13187249516126361295996213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17582999354835148394661617 13187249516126361295996213)
  ·
    refine ⟨1236304642136846371499645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13187249516126361295996213 1236304642136846371499645)
    ·
      refine ⟨463614240801317389312367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1236304642136846371499645 463614240801317389312367)
      ·
        refine ⟨695421361201976083968551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463614240801317389312367 695421361201976083968551)
        ·
          refine ⟨1043132041802964125952827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695421361201976083968551 1043132041802964125952827)
          ·
            refine ⟨1564698062704446188929241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043132041802964125952827 1564698062704446188929241)
            ·
              refine ⟨1173523547028334641696931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1564698062704446188929241 1173523547028334641696931)
              ·
                refine ⟨1760285320542501962545397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173523547028334641696931 1760285320542501962545397)
                ·
                  refine ⟨165026748800859558988631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1760285320542501962545397 165026748800859558988631)
                  ·
                    rfl

theorem cell21_723124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_723124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723124 prefixEnd_723124 := by exact prefixLift 723124
  have htrace : WordTrace (prefixWord ++ tailWord_723124) baseStart_723124 baseEnd_723124 := by
    simpa [prefixWord, tailWord_723124, baseEnd_723124] using wordTrace_append hprefix tailTrace_723124
  have hstable : (prefixWord ++ tailWord_723124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723124).length < 2 ^ (prefixWord ++ tailWord_723124).sum := by decide
  have hdescent : baseEnd_723124 < baseStart_723124 := by decide
  rcases family_descends (prefixWord ++ tailWord_723124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723267 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 7]
def baseStart_723267 : Nat := 118140960795 + 723267 * 2 ^ 59
def prefixEnd_723267 : Nat := 4983230072969 + 3 ^ 40 * 723267 * 2
def baseEnd_723267 : Nat := 165059383349123088105005

theorem tailTrace_723267 : CollatzResearch.WordTrace tailWord_723267 prefixEnd_723267 165059383349123088105005 := by
  unfold tailWord_723267
  simp only [CollatzResearch.WordTrace]
  refine ⟨26379714670734658014448055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17586476447156438676298703 26379714670734658014448055)
  ·
    refine ⟨39569572006101987021672083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26379714670734658014448055 39569572006101987021672083)
    ·
      refine ⟨59354358009152980532508125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39569572006101987021672083 59354358009152980532508125)
      ·
        refine ⟨22257884253432367699690547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59354358009152980532508125 22257884253432367699690547)
        ·
          refine ⟨33386826380148551549535821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22257884253432367699690547 33386826380148551549535821)
          ·
            refine ⟨12520059892555706831075933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33386826380148551549535821 12520059892555706831075933)
            ·
              refine ⟨4695022459708390061653475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12520059892555706831075933 4695022459708390061653475)
              ·
                refine ⟨7042533689562585092480213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4695022459708390061653475 7042533689562585092480213)
                ·
                  refine ⟨165059383349123088105005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7042533689562585092480213 165059383349123088105005)
                  ·
                    rfl

theorem cell21_723267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 7].length) (baseStart_723267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723267 prefixEnd_723267 := by exact prefixLift 723267
  have htrace : WordTrace (prefixWord ++ tailWord_723267) baseStart_723267 baseEnd_723267 := by
    simpa [prefixWord, tailWord_723267, baseEnd_723267] using wordTrace_append hprefix tailTrace_723267
  have hstable : (prefixWord ++ tailWord_723267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723267).length < 2 ^ (prefixWord ++ tailWord_723267).sum := by decide
  have hdescent : baseEnd_723267 < baseStart_723267 := by decide
  rcases family_descends (prefixWord ++ tailWord_723267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723301 : List Nat := [1, 3, 1, 3, 1, 3, 2, 4, 3]
def baseStart_723301 : Nat := 118140960795 + 723301 * 2 ^ 59
def prefixEnd_723301 : Nat := 4983230072969 + 3 ^ 40 * 723301 * 2
def baseEnd_723301 : Nat := 165067142612346584538269

theorem tailTrace_723301 : CollatzResearch.WordTrace tailWord_723301 prefixEnd_723301 165067142612346584538269 := by
  unfold tailWord_723301
  simp only [CollatzResearch.WordTrace]
  refine ⟨26380954752611481821185757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17587303168407654547457171 26380954752611481821185757)
  ·
    refine ⟨9892858032229305682944659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26380954752611481821185757 9892858032229305682944659)
    ·
      refine ⟨14839287048343958524416989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9892858032229305682944659 14839287048343958524416989)
      ·
        refine ⟨5564732643128984446656371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14839287048343958524416989 5564732643128984446656371)
        ·
          refine ⟨8347098964693476669984557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5564732643128984446656371 8347098964693476669984557)
          ·
            refine ⟨3130162111760053751244209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8347098964693476669984557 3130162111760053751244209)
            ·
              refine ⟨2347621583820040313433157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3130162111760053751244209 2347621583820040313433157)
              ·
                refine ⟨440179046966257558768717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2347621583820040313433157 440179046966257558768717)
                ·
                  refine ⟨165067142612346584538269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 440179046966257558768717 165067142612346584538269)
                  ·
                    rfl

theorem cell21_723301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_723301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723301 prefixEnd_723301 := by exact prefixLift 723301
  have htrace : WordTrace (prefixWord ++ tailWord_723301) baseStart_723301 baseEnd_723301 := by
    simpa [prefixWord, tailWord_723301, baseEnd_723301] using wordTrace_append hprefix tailTrace_723301
  have hstable : (prefixWord ++ tailWord_723301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723301).length < 2 ^ (prefixWord ++ tailWord_723301).sum := by decide
  have hdescent : baseEnd_723301 < baseStart_723301 := by decide
  rcases family_descends (prefixWord ++ tailWord_723301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723360 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 5]
def baseStart_723360 : Nat := 118140960795 + 723360 * 2 ^ 59
def prefixEnd_723360 : Nat := 4983230072969 + 3 ^ 40 * 723360 * 2
def baseEnd_723360 : Nat := 165080607216175593054815

theorem tailTrace_723360 : CollatzResearch.WordTrace tailWord_723360 prefixEnd_723360 165080607216175593054815 := by
  unfold tailWord_723360
  simp only [CollatzResearch.WordTrace]
  refine ⟨13191553329698867448791767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17588737772931823265055689 13191553329698867448791767)
  ·
    refine ⟨19787329994548301173187651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13191553329698867448791767 19787329994548301173187651)
    ·
      refine ⟨29680994991822451759781477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19787329994548301173187651 29680994991822451759781477)
      ·
        refine ⟨5565186560966709704959027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29680994991822451759781477 5565186560966709704959027)
        ·
          refine ⟨8347779841450064557438541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5565186560966709704959027 8347779841450064557438541)
          ·
            refine ⟨3130417440543774209039453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8347779841450064557438541 3130417440543774209039453)
            ·
              refine ⟨1173906540203915328389795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3130417440543774209039453 1173906540203915328389795)
              ·
                refine ⟨1760859810305872992584693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173906540203915328389795 1760859810305872992584693)
                ·
                  refine ⟨165080607216175593054815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1760859810305872992584693 165080607216175593054815)
                  ·
                    rfl

theorem cell21_723360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_723360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723360 prefixEnd_723360 := by exact prefixLift 723360
  have htrace : WordTrace (prefixWord ++ tailWord_723360) baseStart_723360 baseEnd_723360 := by
    simpa [prefixWord, tailWord_723360, baseEnd_723360] using wordTrace_append hprefix tailTrace_723360
  have hstable : (prefixWord ++ tailWord_723360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723360).length < 2 ^ (prefixWord ++ tailWord_723360).sum := by decide
  have hdescent : baseEnd_723360 < baseStart_723360 := by decide
  rcases family_descends (prefixWord ++ tailWord_723360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723453 : List Nat := [1, 4, 1, 1, 1, 3, 4, 3, 3]
def baseStart_723453 : Nat := 118140960795 + 723453 * 2 ^ 59
def prefixEnd_723453 : Nat := 4983230072969 + 3 ^ 40 * 723453 * 2
def baseEnd_723453 : Nat := 165101831083228098004625

theorem tailTrace_723453 : CollatzResearch.WordTrace tailWord_723453 prefixEnd_723453 165101831083228098004625 := by
  unfold tailWord_723453
  simp only [CollatzResearch.WordTrace]
  refine ⟨26386498648060811780719013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17590999098707207853812675 26386498648060811780719013)
  ·
    refine ⟨4947468496511402208884815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26386498648060811780719013 4947468496511402208884815)
    ·
      refine ⟨7421202744767103313327223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4947468496511402208884815 7421202744767103313327223)
      ·
        refine ⟨11131804117150654969990835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7421202744767103313327223 11131804117150654969990835)
        ·
          refine ⟨16697706175725982454986253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11131804117150654969990835 16697706175725982454986253)
          ·
            refine ⟨6261639815897243420619845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16697706175725982454986253 6261639815897243420619845)
            ·
              refine ⟨1174057465480733141366221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6261639815897243420619845 1174057465480733141366221)
              ·
                refine ⟨440271549555274928012333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1174057465480733141366221 440271549555274928012333)
                ·
                  refine ⟨165101831083228098004625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 440271549555274928012333 165101831083228098004625)
                  ·
                    rfl

theorem cell21_723453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_723453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723453 prefixEnd_723453 := by exact prefixLift 723453
  have htrace : WordTrace (prefixWord ++ tailWord_723453) baseStart_723453 baseEnd_723453 := by
    simpa [prefixWord, tailWord_723453, baseEnd_723453] using wordTrace_append hprefix tailTrace_723453
  have hstable : (prefixWord ++ tailWord_723453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723453).length < 2 ^ (prefixWord ++ tailWord_723453).sum := by decide
  have hdescent : baseEnd_723453 < baseStart_723453 := by decide
  rcases family_descends (prefixWord ++ tailWord_723453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723467 : List Nat := [1, 1, 1, 1, 7, 1, 3, 2, 4]
def baseStart_723467 : Nat := 118140960795 + 723467 * 2 ^ 59
def prefixEnd_723467 : Nat := 4983230072969 + 3 ^ 40 * 723467 * 2
def baseEnd_723467 : Nat := 165105026073967184771263

theorem tailTrace_723467 : CollatzResearch.WordTrace tailWord_723467 prefixEnd_723467 165105026073967184771263 := by
  unfold tailWord_723467
  simp only [CollatzResearch.WordTrace]
  refine ⟨26387009270010092171728655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17591339513340061447819103 26387009270010092171728655)
  ·
    refine ⟨39580513905015138257592983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26387009270010092171728655 39580513905015138257592983)
    ·
      refine ⟨59370770857522707386389475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39580513905015138257592983 59370770857522707386389475)
      ·
        refine ⟨89056156286284061079584213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59370770857522707386389475 89056156286284061079584213)
        ·
          refine ⟨2087253662959782681552755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 89056156286284061079584213 2087253662959782681552755)
          ·
            refine ⟨3130880494439674022329133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087253662959782681552755 3130880494439674022329133)
            ·
              refine ⟨1174080185414877758373425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3130880494439674022329133 1174080185414877758373425)
              ·
                refine ⟨880560139061158318780069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1174080185414877758373425 880560139061158318780069)
                ·
                  refine ⟨165105026073967184771263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 880560139061158318780069 165105026073967184771263)
                  ·
                    rfl

theorem cell21_723467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 4].length) (baseStart_723467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723467 prefixEnd_723467 := by exact prefixLift 723467
  have htrace : WordTrace (prefixWord ++ tailWord_723467) baseStart_723467 baseEnd_723467 := by
    simpa [prefixWord, tailWord_723467, baseEnd_723467] using wordTrace_append hprefix tailTrace_723467
  have hstable : (prefixWord ++ tailWord_723467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723467).length < 2 ^ (prefixWord ++ tailWord_723467).sum := by decide
  have hdescent : baseEnd_723467 < baseStart_723467 := by decide
  rcases family_descends (prefixWord ++ tailWord_723467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723484 : List Nat := [2, 2, 3, 1, 2, 3, 3, 1, 4]
def baseStart_723484 : Nat := 118140960795 + 723484 * 2 ^ 59
def prefixEnd_723484 : Nat := 4983230072969 + 3 ^ 40 * 723484 * 2
def baseEnd_723484 : Nat := 165108905705578932987895

theorem tailTrace_723484 : CollatzResearch.WordTrace tailWord_723484 prefixEnd_723484 165108905705578932987895 := by
  unfold tailWord_723484
  simp only [CollatzResearch.WordTrace]
  refine ⟨13193814655474252037548753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17591752873965669383398337 13193814655474252037548753)
  ·
    refine ⟨9895360991605689028161565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13193814655474252037548753 9895360991605689028161565)
    ·
      refine ⟨3710760371852133385560587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9895360991605689028161565 3710760371852133385560587)
      ·
        refine ⟨5566140557778200078340881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3710760371852133385560587 5566140557778200078340881)
        ·
          refine ⟨4174605418333650058755661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5566140557778200078340881 4174605418333650058755661)
          ·
            refine ⟨1565477031875118772033373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4174605418333650058755661 1565477031875118772033373)
            ·
              refine ⟨587053886953169539512515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1565477031875118772033373 587053886953169539512515)
              ·
                refine ⟨880580830429754309268773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587053886953169539512515 880580830429754309268773)
                ·
                  refine ⟨165108905705578932987895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 880580830429754309268773 165108905705578932987895)
                  ·
                    rfl

theorem cell21_723484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_723484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723484 prefixEnd_723484 := by exact prefixLift 723484
  have htrace : WordTrace (prefixWord ++ tailWord_723484) baseStart_723484 baseEnd_723484 := by
    simpa [prefixWord, tailWord_723484, baseEnd_723484] using wordTrace_append hprefix tailTrace_723484
  have hstable : (prefixWord ++ tailWord_723484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723484).length < 2 ^ (prefixWord ++ tailWord_723484).sum := by decide
  have hdescent : baseEnd_723484 < baseStart_723484 := by decide
  rcases family_descends (prefixWord ++ tailWord_723484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723498 : List Nat := [3, 1, 4, 1, 1, 2, 4, 5]
def baseStart_723498 : Nat := 118140960795 + 723498 * 2 ^ 59
def prefixEnd_723498 : Nat := 4983230072969 + 3 ^ 40 * 723498 * 2
def baseEnd_723498 : Nat := 55037366898772673251511

theorem tailTrace_723498 : CollatzResearch.WordTrace tailWord_723498 prefixEnd_723498 55037366898772673251511 := by
  unfold tailWord_723498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6597034983224446116526787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17592093288598522977404765 6597034983224446116526787)
  ·
    refine ⟨9895552474836669174790181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6597034983224446116526787 9895552474836669174790181)
    ·
      refine ⟨1855416089031875470273159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9895552474836669174790181 1855416089031875470273159)
      ·
        refine ⟨2783124133547813205409739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855416089031875470273159 2783124133547813205409739)
        ·
          refine ⟨4174686200321719808114609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783124133547813205409739 4174686200321719808114609)
          ·
            refine ⟨3131014650241289856085957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4174686200321719808114609 3131014650241289856085957)
            ·
              refine ⟨587065246920241848016117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3131014650241289856085957 587065246920241848016117)
              ·
                refine ⟨55037366898772673251511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 587065246920241848016117 55037366898772673251511)
                ·
                  rfl

theorem cell21_723498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_723498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723498 prefixEnd_723498 := by exact prefixLift 723498
  have htrace : WordTrace (prefixWord ++ tailWord_723498) baseStart_723498 baseEnd_723498 := by
    simpa [prefixWord, tailWord_723498, baseEnd_723498] using wordTrace_append hprefix tailTrace_723498
  have hstable : (prefixWord ++ tailWord_723498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723498).length < 2 ^ (prefixWord ++ tailWord_723498).sum := by decide
  have hdescent : baseEnd_723498 < baseStart_723498 := by decide
  rcases family_descends (prefixWord ++ tailWord_723498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723574 : List Nat := [5, 1, 1, 2, 4, 8]
def baseStart_723574 : Nat := 118140960795 + 723574 * 2 ^ 59
def prefixEnd_723574 : Nat := 4983230072969 + 3 ^ 40 * 723574 * 2
def baseEnd_723574 : Nat := 6115905367842917647693

theorem tailTrace_723574 : CollatzResearch.WordTrace tailWord_723574 prefixEnd_723574 6115905367842917647693 := by
  unfold tailWord_723574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1649431992538903090367111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17593941253748299630582517 1649431992538903090367111)
  ·
    refine ⟨2474147988808354635550667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1649431992538903090367111 2474147988808354635550667)
    ·
      refine ⟨3711221983212531953326001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2474147988808354635550667 3711221983212531953326001)
      ·
        refine ⟨2783416487409398964994501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3711221983212531953326001 2783416487409398964994501)
        ·
          refine ⟨521890591389262305936469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2783416487409398964994501 521890591389262305936469)
          ·
            refine ⟨6115905367842917647693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 521890591389262305936469 6115905367842917647693)
            ·
              rfl

theorem cell21_723574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 8].length) (baseStart_723574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723574 prefixEnd_723574 := by exact prefixLift 723574
  have htrace : WordTrace (prefixWord ++ tailWord_723574) baseStart_723574 baseEnd_723574 := by
    simpa [prefixWord, tailWord_723574, baseEnd_723574] using wordTrace_append hprefix tailTrace_723574
  have hstable : (prefixWord ++ tailWord_723574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723574).length < 2 ^ (prefixWord ++ tailWord_723574).sum := by decide
  have hdescent : baseEnd_723574 < baseStart_723574 := by decide
  rcases family_descends (prefixWord ++ tailWord_723574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723647 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 5]
def baseStart_723647 : Nat := 118140960795 + 723647 * 2 ^ 59
def prefixEnd_723647 : Nat := 4983230072969 + 3 ^ 40 * 723647 * 2
def baseEnd_723647 : Nat := 165146104526326871770895

theorem tailTrace_723647 : CollatzResearch.WordTrace tailWord_723647 prefixEnd_723647 165146104526326871770895 := by
  unfold tailWord_723647
  simp only [CollatzResearch.WordTrace]
  refine ⟨26393574409357982913281195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17595716272905321942187463 26393574409357982913281195)
  ·
    refine ⟨39590361614036974369921793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26393574409357982913281195 39590361614036974369921793)
    ·
      refine ⟨29692771210527730777441345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39590361614036974369921793 29692771210527730777441345)
      ·
        refine ⟨22269578407895798083081009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29692771210527730777441345 22269578407895798083081009)
        ·
          refine ⟨16702183805921848562310757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22269578407895798083081009 16702183805921848562310757)
          ·
            refine ⟨3131659463610346605433267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16702183805921848562310757 3131659463610346605433267)
            ·
              refine ⟨4697489195415519908149901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3131659463610346605433267 4697489195415519908149901)
              ·
                refine ⟨1761558448280819965556213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4697489195415519908149901 1761558448280819965556213)
                ·
                  refine ⟨165146104526326871770895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1761558448280819965556213 165146104526326871770895)
                  ·
                    rfl

theorem cell21_723647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 5].length) (baseStart_723647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723647 prefixEnd_723647 := by exact prefixLift 723647
  have htrace : WordTrace (prefixWord ++ tailWord_723647) baseStart_723647 baseEnd_723647 := by
    simpa [prefixWord, tailWord_723647, baseEnd_723647] using wordTrace_append hprefix tailTrace_723647
  have hstable : (prefixWord ++ tailWord_723647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723647).length < 2 ^ (prefixWord ++ tailWord_723647).sum := by decide
  have hdescent : baseEnd_723647 < baseStart_723647 := by decide
  rcases family_descends (prefixWord ++ tailWord_723647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723681 : List Nat := [1, 2, 3, 1, 4, 1, 3, 3, 3]
def baseStart_723681 : Nat := 118140960795 + 723681 * 2 ^ 59
def prefixEnd_723681 : Nat := 4983230072969 + 3 ^ 40 * 723681 * 2
def baseEnd_723681 : Nat := 165153863789550368204159

theorem tailTrace_723681 : CollatzResearch.WordTrace tailWord_723681 prefixEnd_723681 165153863789550368204159 := by
  unfold tailWord_723681
  simp only [CollatzResearch.WordTrace]
  refine ⟨26394814491234806720018897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17596542994156537813345931 26394814491234806720018897)
  ·
    refine ⟨19796110868426105040014173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26394814491234806720018897 19796110868426105040014173)
    ·
      refine ⟨7423541575659789390005315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19796110868426105040014173 7423541575659789390005315)
      ·
        refine ⟨11135312363489684085007973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7423541575659789390005315 11135312363489684085007973)
        ·
          refine ⟨2087871068154315765938995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11135312363489684085007973 2087871068154315765938995)
          ·
            refine ⟨3131806602231473648908493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087871068154315765938995 3131806602231473648908493)
            ·
              refine ⟨1174427475836802618340685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3131806602231473648908493 1174427475836802618340685)
              ·
                refine ⟨440410303438800981877757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1174427475836802618340685 440410303438800981877757)
                ·
                  refine ⟨165153863789550368204159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 440410303438800981877757 165153863789550368204159)
                  ·
                    rfl

theorem cell21_723681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 3].length) (baseStart_723681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723681 prefixEnd_723681 := by exact prefixLift 723681
  have htrace : WordTrace (prefixWord ++ tailWord_723681) baseStart_723681 baseEnd_723681 := by
    simpa [prefixWord, tailWord_723681, baseEnd_723681] using wordTrace_append hprefix tailTrace_723681
  have hstable : (prefixWord ++ tailWord_723681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723681).length < 2 ^ (prefixWord ++ tailWord_723681).sum := by decide
  have hdescent : baseEnd_723681 < baseStart_723681 := by decide
  rcases family_descends (prefixWord ++ tailWord_723681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723698 : List Nat := [3, 2, 1, 3, 1, 3, 3, 2, 3]
def baseStart_723698 : Nat := 118140960795 + 723698 * 2 ^ 59
def prefixEnd_723698 : Nat := 4983230072969 + 3 ^ 40 * 723698 * 2
def baseEnd_723698 : Nat := 165157743421162116420791

theorem tailTrace_723698 : CollatzResearch.WordTrace tailWord_723698 prefixEnd_723698 165157743421162116420791 := by
  unfold tailWord_723698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6598858633043304655846937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17596956354782145748925165 6598858633043304655846937)
  ·
    refine ⟨4949143974782478491885203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6598858633043304655846937 4949143974782478491885203)
    ·
      refine ⟨7423715962173717737827805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4949143974782478491885203 7423715962173717737827805)
      ·
        refine ⟨2783893485815144151685427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7423715962173717737827805 2783893485815144151685427)
        ·
          refine ⟨4175840228722716227528141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783893485815144151685427 4175840228722716227528141)
          ·
            refine ⟨1565940085771018585323053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4175840228722716227528141 1565940085771018585323053)
            ·
              refine ⟨587227532164131969496145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1565940085771018585323053 587227532164131969496145)
              ·
                refine ⟨440420649123098977122109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 587227532164131969496145 440420649123098977122109)
                ·
                  refine ⟨165157743421162116420791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 440420649123098977122109 165157743421162116420791)
                  ·
                    rfl

theorem cell21_723698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_723698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723698 prefixEnd_723698 := by exact prefixLift 723698
  have htrace : WordTrace (prefixWord ++ tailWord_723698) baseStart_723698 baseEnd_723698 := by
    simpa [prefixWord, tailWord_723698, baseEnd_723698] using wordTrace_append hprefix tailTrace_723698
  have hstable : (prefixWord ++ tailWord_723698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723698).length < 2 ^ (prefixWord ++ tailWord_723698).sum := by decide
  have hdescent : baseEnd_723698 < baseStart_723698 := by decide
  rcases family_descends (prefixWord ++ tailWord_723698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723737 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 6]
def baseStart_723737 : Nat := 118140960795 + 723737 * 2 ^ 59
def prefixEnd_723737 : Nat := 4983230072969 + 3 ^ 40 * 723737 * 2
def baseEnd_723737 : Nat := 165166643752506715270711

theorem tailTrace_723737 : CollatzResearch.WordTrace tailWord_723737 prefixEnd_723737 165166643752506715270711 := by
  unfold tailWord_723737
  simp only [CollatzResearch.WordTrace]
  refine ⟨26396856979031928284057465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17597904652687952189371643 26396856979031928284057465)
  ·
    refine ⟨19797642734273946213043099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26396856979031928284057465 19797642734273946213043099)
    ·
      refine ⟨29696464101410919319564649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19797642734273946213043099 29696464101410919319564649)
      ·
        refine ⟨22272348076058189489673487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29696464101410919319564649 22272348076058189489673487)
        ·
          refine ⟨33408522114087284234510231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22272348076058189489673487 33408522114087284234510231)
          ·
            refine ⟨50112783171130926351765347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33408522114087284234510231 50112783171130926351765347)
            ·
              refine ⟨75169174756696389527648021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50112783171130926351765347 75169174756696389527648021)
              ·
                refine ⟨3523555066720143259108501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75169174756696389527648021 3523555066720143259108501)
                ·
                  refine ⟨165166643752506715270711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3523555066720143259108501 165166643752506715270711)
                  ·
                    rfl

theorem cell21_723737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_723737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723737 prefixEnd_723737 := by exact prefixLift 723737
  have htrace : WordTrace (prefixWord ++ tailWord_723737) baseStart_723737 baseEnd_723737 := by
    simpa [prefixWord, tailWord_723737, baseEnd_723737] using wordTrace_append hprefix tailTrace_723737
  have hstable : (prefixWord ++ tailWord_723737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723737).length < 2 ^ (prefixWord ++ tailWord_723737).sum := by decide
  have hdescent : baseEnd_723737 < baseStart_723737 := by decide
  rcases family_descends (prefixWord ++ tailWord_723737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723785 : List Nat := [1, 2, 1, 1, 2, 6, 3, 5]
def baseStart_723785 : Nat := 118140960795 + 723785 * 2 ^ 59
def prefixEnd_723785 : Nat := 4983230072969 + 3 ^ 40 * 723785 * 2
def baseEnd_723785 : Nat := 55059199335489766156871

theorem tailTrace_723785 : CollatzResearch.WordTrace tailWord_723785 prefixEnd_723785 55059199335489766156871 := by
  unfold tailWord_723785
  simp only [CollatzResearch.WordTrace]
  refine ⟨26398607682858032481804809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17599071788572021654536539 26398607682858032481804809)
  ·
    refine ⟨19798955762143524361353607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26398607682858032481804809 19798955762143524361353607)
    ·
      refine ⟨29698433643215286542030411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19798955762143524361353607 29698433643215286542030411)
      ·
        refine ⟨44547650464822929813045617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29698433643215286542030411 44547650464822929813045617)
        ·
          refine ⟨33410737848617197359784213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44547650464822929813045617 33410737848617197359784213)
          ·
            refine ⟨1566128336653931126239885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33410737848617197359784213 1566128336653931126239885)
            ·
              refine ⟨587298126245224172339957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1566128336653931126239885 587298126245224172339957)
              ·
                refine ⟨55059199335489766156871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 587298126245224172339957 55059199335489766156871)
                ·
                  rfl

theorem cell21_723785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 5].length) (baseStart_723785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723785 prefixEnd_723785 := by exact prefixLift 723785
  have htrace : WordTrace (prefixWord ++ tailWord_723785) baseStart_723785 baseEnd_723785 := by
    simpa [prefixWord, tailWord_723785, baseEnd_723785] using wordTrace_append hprefix tailTrace_723785
  have hstable : (prefixWord ++ tailWord_723785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723785).length < 2 ^ (prefixWord ++ tailWord_723785).sum := by decide
  have hdescent : baseEnd_723785 < baseStart_723785 := by decide
  rcases family_descends (prefixWord ++ tailWord_723785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723816 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 5]
def baseStart_723816 : Nat := 118140960795 + 723816 * 2 ^ 59
def prefixEnd_723816 : Nat := 4983230072969 + 3 ^ 40 * 723816 * 2
def baseEnd_723816 : Nat := 165184672628820133453883

theorem tailTrace_723816 : CollatzResearch.WordTrace tailWord_723816 prefixEnd_723816 165184672628820133453883 := by
  unfold tailWord_723816
  simp only [CollatzResearch.WordTrace]
  refine ⟨13199869172872862388091651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17599825563830483184122201 13199869172872862388091651)
  ·
    refine ⟨19799803759309293582137477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13199869172872862388091651 19799803759309293582137477)
    ·
      refine ⟨3712463204870492546650777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19799803759309293582137477 3712463204870492546650777)
      ·
        refine ⟨2784347403652869409988083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3712463204870492546650777 2784347403652869409988083)
        ·
          refine ⟨4176521105479304114982125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2784347403652869409988083 4176521105479304114982125)
          ·
            refine ⟨1566195414554739043118297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4176521105479304114982125 1566195414554739043118297)
            ·
              refine ⟨1174646560916054282338723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1566195414554739043118297 1174646560916054282338723)
              ·
                refine ⟨1761969841374081423508085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1174646560916054282338723 1761969841374081423508085)
                ·
                  refine ⟨165184672628820133453883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1761969841374081423508085 165184672628820133453883)
                  ·
                    rfl

theorem cell21_723816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_723816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723816 prefixEnd_723816 := by exact prefixLift 723816
  have htrace : WordTrace (prefixWord ++ tailWord_723816) baseStart_723816 baseEnd_723816 := by
    simpa [prefixWord, tailWord_723816, baseEnd_723816] using wordTrace_append hprefix tailTrace_723816
  have hstable : (prefixWord ++ tailWord_723816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723816).length < 2 ^ (prefixWord ++ tailWord_723816).sum := by decide
  have hdescent : baseEnd_723816 < baseStart_723816 := by decide
  rcases family_descends (prefixWord ++ tailWord_723816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723850 : List Nat := [3, 1, 2, 4, 1, 3, 1, 3, 3]
def baseStart_723850 : Nat := 118140960795 + 723850 * 2 ^ 59
def prefixEnd_723850 : Nat := 4983230072969 + 3 ^ 40 * 723850 * 2
def baseEnd_723850 : Nat := 165192431892043629887147

theorem tailTrace_723850 : CollatzResearch.WordTrace tailWord_723850 prefixEnd_723850 165192431892043629887147 := by
  unfold tailWord_723850
  simp only [CollatzResearch.WordTrace]
  refine ⟨6600244606905637145730251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17600652285081699055280669 6600244606905637145730251)
  ·
    refine ⟨9900366910358455718595377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6600244606905637145730251 9900366910358455718595377)
    ·
      refine ⟨7425275182768841788946533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9900366910358455718595377 7425275182768841788946533)
      ·
        refine ⟨1392239096769157835427475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7425275182768841788946533 1392239096769157835427475)
        ·
          refine ⟨2088358645153736753141213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1392239096769157835427475 2088358645153736753141213)
          ·
            refine ⟨783134491932651282427955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2088358645153736753141213 783134491932651282427955)
            ·
              refine ⟨1174701737898976923641933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783134491932651282427955 1174701737898976923641933)
              ·
                refine ⟨440513151712116346365725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1174701737898976923641933 440513151712116346365725)
                ·
                  refine ⟨165192431892043629887147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 440513151712116346365725 165192431892043629887147)
                  ·
                    rfl

theorem cell21_723850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_723850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723850 prefixEnd_723850 := by exact prefixLift 723850
  have htrace : WordTrace (prefixWord ++ tailWord_723850) baseStart_723850 baseEnd_723850 := by
    simpa [prefixWord, tailWord_723850, baseEnd_723850] using wordTrace_append hprefix tailTrace_723850
  have hstable : (prefixWord ++ tailWord_723850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723850).length < 2 ^ (prefixWord ++ tailWord_723850).sum := by decide
  have hdescent : baseEnd_723850 < baseStart_723850 := by decide
  rcases family_descends (prefixWord ++ tailWord_723850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723875 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 5]
def baseStart_723875 : Nat := 118140960795 + 723875 * 2 ^ 59
def prefixEnd_723875 : Nat := 4983230072969 + 3 ^ 40 * 723875 * 2
def baseEnd_723875 : Nat := 165198137232649141970429

theorem tailTrace_723875 : CollatzResearch.WordTrace tailWord_723875 prefixEnd_723875 165198137232649141970429 := by
  unfold tailWord_723875
  simp only [CollatzResearch.WordTrace]
  refine ⟨26401890252531977852581079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17601260168354651901720719 26401890252531977852581079)
  ·
    refine ⟨39602835378797966778871619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26401890252531977852581079 39602835378797966778871619)
    ·
      refine ⟨59404253068196950168307429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39602835378797966778871619 59404253068196950168307429)
      ·
        refine ⟨11138297450286928156557643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59404253068196950168307429 11138297450286928156557643)
        ·
          refine ⟨16707446175430392234836465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11138297450286928156557643 16707446175430392234836465)
          ·
            refine ⟨12530584631572794176127349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16707446175430392234836465 12530584631572794176127349)
            ·
              refine ⟨1174742309209949454011939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12530584631572794176127349 1174742309209949454011939)
              ·
                refine ⟨1762113463814924181017909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1174742309209949454011939 1762113463814924181017909)
                ·
                  refine ⟨165198137232649141970429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1762113463814924181017909 165198137232649141970429)
                  ·
                    rfl

theorem cell21_723875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 5].length) (baseStart_723875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723875 prefixEnd_723875 := by exact prefixLift 723875
  have htrace : WordTrace (prefixWord ++ tailWord_723875) baseStart_723875 baseEnd_723875 := by
    simpa [prefixWord, tailWord_723875, baseEnd_723875] using wordTrace_append hprefix tailTrace_723875
  have hstable : (prefixWord ++ tailWord_723875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723875).length < 2 ^ (prefixWord ++ tailWord_723875).sum := by decide
  have hdescent : baseEnd_723875 < baseStart_723875 := by decide
  rcases family_descends (prefixWord ++ tailWord_723875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723926 : List Nat := [5, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_723926 : Nat := 118140960795 + 723926 * 2 ^ 59
def prefixEnd_723926 : Nat := 4983230072969 + 3 ^ 40 * 723926 * 2
def baseEnd_723926 : Nat := 165209776127484386620325

theorem tailTrace_723926 : CollatzResearch.WordTrace tailWord_723926 prefixEnd_723926 165209776127484386620325 := by
  unfold tailWord_723926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1650234398459200847667977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17602500250231475708458421 1650234398459200847667977)
  ·
    refine ⟨1237675798844400635750983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1650234398459200847667977 1237675798844400635750983)
    ·
      refine ⟨1856513698266600953626475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1237675798844400635750983 1856513698266600953626475)
      ·
        refine ⟨2784770547399901430439713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1856513698266600953626475 2784770547399901430439713)
        ·
          refine ⟨2088577910549926072829785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2784770547399901430439713 2088577910549926072829785)
          ·
            refine ⟨1566433432912444554622339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2088577910549926072829785 1566433432912444554622339)
            ·
              refine ⟨2349650149368666831933509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566433432912444554622339 2349650149368666831933509)
              ·
                refine ⟨440559403006625030987533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2349650149368666831933509 440559403006625030987533)
                ·
                  refine ⟨165209776127484386620325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 440559403006625030987533 165209776127484386620325)
                  ·
                    rfl

theorem cell21_723926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_723926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723926 prefixEnd_723926 := by exact prefixLift 723926
  have htrace : WordTrace (prefixWord ++ tailWord_723926) baseStart_723926 baseEnd_723926 := by
    simpa [prefixWord, tailWord_723926, baseEnd_723926] using wordTrace_append hprefix tailTrace_723926
  have hstable : (prefixWord ++ tailWord_723926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723926).length < 2 ^ (prefixWord ++ tailWord_723926).sum := by decide
  have hdescent : baseEnd_723926 < baseStart_723926 := by decide
  rcases family_descends (prefixWord ++ tailWord_723926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723951 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 5]
def baseStart_723951 : Nat := 118140960795 + 723951 * 2 ^ 59
def prefixEnd_723951 : Nat := 4983230072969 + 3 ^ 40 * 723951 * 2
def baseEnd_723951 : Nat := 165215481468089898703607

theorem tailTrace_723951 : CollatzResearch.WordTrace tailWord_723951 prefixEnd_723951 165215481468089898703607 := by
  unfold tailWord_723951
  simp only [CollatzResearch.WordTrace]
  refine ⟨26404662200256642832347707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17603108133504428554898471 26404662200256642832347707)
  ·
    refine ⟨39606993300384964248521561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26404662200256642832347707 39606993300384964248521561)
    ·
      refine ⟨29705244975288723186391171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39606993300384964248521561 29705244975288723186391171)
      ·
        refine ⟨44557867462933084779586757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29705244975288723186391171 44557867462933084779586757)
        ·
          refine ⟨8354600149299953396172517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44557867462933084779586757 8354600149299953396172517)
          ·
            refine ⟨1566487527993741261782347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8354600149299953396172517 1566487527993741261782347)
            ·
              refine ⟨2349731291990611892673521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566487527993741261782347 2349731291990611892673521)
              ·
                refine ⟨1762298468992958919505141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2349731291990611892673521 1762298468992958919505141)
                ·
                  refine ⟨165215481468089898703607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1762298468992958919505141 165215481468089898703607)
                  ·
                    rfl

theorem cell21_723951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 5].length) (baseStart_723951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723951 prefixEnd_723951 := by exact prefixLift 723951
  have htrace : WordTrace (prefixWord ++ tailWord_723951) baseStart_723951 baseEnd_723951 := by
    simpa [prefixWord, tailWord_723951, baseEnd_723951] using wordTrace_append hprefix tailTrace_723951
  have hstable : (prefixWord ++ tailWord_723951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723951).length < 2 ^ (prefixWord ++ tailWord_723951).sum := by decide
  have hdescent : baseEnd_723951 < baseStart_723951 := by decide
  rcases family_descends (prefixWord ++ tailWord_723951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723965 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 6]
def baseStart_723965 : Nat := 118140960795 + 723965 * 2 ^ 59
def prefixEnd_723965 : Nat := 4983230072969 + 3 ^ 40 * 723965 * 2
def baseEnd_723965 : Nat := 165218676458828985470245

theorem tailTrace_723965 : CollatzResearch.WordTrace tailWord_723965 prefixEnd_723965 165218676458828985470245 := by
  unfold tailWord_723965
  simp only [CollatzResearch.WordTrace]
  refine ⟨26405172822205923223357349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17603448548137282148904899 26405172822205923223357349)
  ·
    refine ⟨4950969904163610604379503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26405172822205923223357349 4950969904163610604379503)
    ·
      refine ⟨7426454856245415906569255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4950969904163610604379503 7426454856245415906569255)
      ·
        refine ⟨11139682284368123859853883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7426454856245415906569255 11139682284368123859853883)
        ·
          refine ⟨16709523426552185789780825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11139682284368123859853883 16709523426552185789780825)
          ·
            refine ⟨12532142569914139342335619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16709523426552185789780825 12532142569914139342335619)
            ·
              refine ⟨18798213854871209013503429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12532142569914139342335619 18798213854871209013503429)
              ·
                refine ⟨3524665097788351690031893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18798213854871209013503429 3524665097788351690031893)
                ·
                  refine ⟨165218676458828985470245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3524665097788351690031893 165218676458828985470245)
                  ·
                    rfl

theorem cell21_723965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_723965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723965 prefixEnd_723965 := by exact prefixLift 723965
  have htrace : WordTrace (prefixWord ++ tailWord_723965) baseStart_723965 baseEnd_723965 := by
    simpa [prefixWord, tailWord_723965, baseEnd_723965] using wordTrace_append hprefix tailTrace_723965
  have hstable : (prefixWord ++ tailWord_723965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723965).length < 2 ^ (prefixWord ++ tailWord_723965).sum := by decide
  have hdescent : baseEnd_723965 < baseStart_723965 := by decide
  rcases family_descends (prefixWord ++ tailWord_723965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723982 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_723982 : Nat := 118140960795 + 723982 * 2 ^ 59
def prefixEnd_723982 : Nat := 4983230072969 + 3 ^ 40 * 723982 * 2
def baseEnd_723982 : Nat := 165222556090440733686877

theorem tailTrace_723982 : CollatzResearch.WordTrace tailWord_723982 prefixEnd_723982 165222556090440733686877 := by
  unfold tailWord_723982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3300724107893041890840775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17603861908762890084484133 3300724107893041890840775)
  ·
    refine ⟨4951086161839562836261163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3300724107893041890840775 4951086161839562836261163)
    ·
      refine ⟨7426629242759344254391745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4951086161839562836261163 7426629242759344254391745)
      ·
        refine ⟨5569971932069508190793809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7426629242759344254391745 5569971932069508190793809)
        ·
          refine ⟨4177478949052131143095357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5569971932069508190793809 4177478949052131143095357)
          ·
            refine ⟨1566554605894549178660759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4177478949052131143095357 1566554605894549178660759)
            ·
              refine ⟨2349831908841823767991139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566554605894549178660759 2349831908841823767991139)
              ·
                refine ⟨3524747863262735651986709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2349831908841823767991139 3524747863262735651986709)
                ·
                  refine ⟨165222556090440733686877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3524747863262735651986709 165222556090440733686877)
                  ·
                    rfl

theorem cell21_723982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_723982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723982 prefixEnd_723982 := by exact prefixLift 723982
  have htrace : WordTrace (prefixWord ++ tailWord_723982) baseStart_723982 baseEnd_723982 := by
    simpa [prefixWord, tailWord_723982, baseEnd_723982] using wordTrace_append hprefix tailTrace_723982
  have hstable : (prefixWord ++ tailWord_723982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723982).length < 2 ^ (prefixWord ++ tailWord_723982).sum := by decide
  have hdescent : baseEnd_723982 < baseStart_723982 := by decide
  rcases family_descends (prefixWord ++ tailWord_723982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723999 : List Nat := [1, 1, 2, 4, 1, 4, 3, 1, 4]
def baseStart_723999 : Nat := 118140960795 + 723999 * 2 ^ 59
def prefixEnd_723999 : Nat := 4983230072969 + 3 ^ 40 * 723999 * 2
def baseEnd_723999 : Nat := 165226435722052481903509

theorem tailTrace_723999 : CollatzResearch.WordTrace tailWord_723999 prefixEnd_723999 165226435722052481903509 := by
  unfold tailWord_723999
  simp only [CollatzResearch.WordTrace]
  refine ⟨26406412904082747030095051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17604275269388498020063367 26406412904082747030095051)
  ·
    refine ⟨39609619356124120545142577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26406412904082747030095051 39609619356124120545142577)
    ·
      refine ⟨29707214517093090408856933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39609619356124120545142577 29707214517093090408856933)
      ·
        refine ⟨5570102721954954451660675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29707214517093090408856933 5570102721954954451660675)
        ·
          refine ⟨8355154082932431677491013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5570102721954954451660675 8355154082932431677491013)
          ·
            refine ⟨1566591390549830939529565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8355154082932431677491013 1566591390549830939529565)
            ·
              refine ⟨587471771456186602323587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1566591390549830939529565 587471771456186602323587)
              ·
                refine ⟨881207657184279903485381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587471771456186602323587 881207657184279903485381)
                ·
                  refine ⟨165226435722052481903509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 881207657184279903485381 165226435722052481903509)
                  ·
                    rfl

theorem cell21_723999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 4].length) (baseStart_723999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_723999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_723999 prefixEnd_723999 := by exact prefixLift 723999
  have htrace : WordTrace (prefixWord ++ tailWord_723999) baseStart_723999 baseEnd_723999 := by
    simpa [prefixWord, tailWord_723999, baseEnd_723999] using wordTrace_append hprefix tailTrace_723999
  have hstable : (prefixWord ++ tailWord_723999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723999).length < 2 ^ (prefixWord ++ tailWord_723999).sum := by decide
  have hdescent : baseEnd_723999 < baseStart_723999 := by decide
  rcases family_descends (prefixWord ++ tailWord_723999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724131 : List Nat := [1, 1, 1, 4, 1, 1, 1, 11]
def baseStart_724131 : Nat := 118140960795 + 724131 * 2 ^ 59
def prefixEnd_724131 : Nat := 4983230072969 + 3 ^ 40 * 724131 * 2
def baseEnd_724131 : Nat := 55085519973483195234413

theorem tailTrace_724131 : CollatzResearch.WordTrace tailWord_724131 prefixEnd_724131 55085519973483195234413 := by
  unfold tailWord_724131
  simp only [CollatzResearch.WordTrace]
  refine ⟨26411227339604533573900247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17607484893069689049266831 26411227339604533573900247)
  ·
    refine ⟨39616841009406800360850371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26411227339604533573900247 39616841009406800360850371)
    ·
      refine ⟨59425261514110200541275557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39616841009406800360850371 59425261514110200541275557)
      ·
        refine ⟨11142236533895662601489167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59425261514110200541275557 11142236533895662601489167)
        ·
          refine ⟨16713354800843493902233751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11142236533895662601489167 16713354800843493902233751)
          ·
            refine ⟨25070032201265240853350627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16713354800843493902233751 25070032201265240853350627)
            ·
              refine ⟨37605048301897861280025941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25070032201265240853350627 37605048301897861280025941)
              ·
                refine ⟨55085519973483195234413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 37605048301897861280025941 55085519973483195234413)
                ·
                  rfl

theorem cell21_724131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 11].length) (baseStart_724131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724131 prefixEnd_724131 := by exact prefixLift 724131
  have htrace : WordTrace (prefixWord ++ tailWord_724131) baseStart_724131 baseEnd_724131 := by
    simpa [prefixWord, tailWord_724131, baseEnd_724131] using wordTrace_append hprefix tailTrace_724131
  have hstable : (prefixWord ++ tailWord_724131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724131).length < 2 ^ (prefixWord ++ tailWord_724131).sum := by decide
  have hdescent : baseEnd_724131 < baseStart_724131 := by decide
  rcases family_descends (prefixWord ++ tailWord_724131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724182 : List Nat := [5, 2, 1, 2, 2, 1, 1, 7]
def baseStart_724182 : Nat := 118140960795 + 724182 * 2 ^ 59
def prefixEnd_724182 : Nat := 4983230072969 + 3 ^ 40 * 724182 * 2
def baseEnd_724182 : Nat := 55089399605094943451045

theorem tailTrace_724182 : CollatzResearch.WordTrace tailWord_724182 prefixEnd_724182 55089399605094943451045 := by
  unfold tailWord_724182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1650817966401235580250425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17608724974946512856004533 1650817966401235580250425)
  ·
    refine ⟨1238113474800926685187819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1650817966401235580250425 1238113474800926685187819)
    ·
      refine ⟨1857170212201390027781729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1238113474800926685187819 1857170212201390027781729)
      ·
        refine ⟨1392877659151042520836297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1857170212201390027781729 1392877659151042520836297)
        ·
          refine ⟨1044658244363281890627223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1392877659151042520836297 1044658244363281890627223)
          ·
            refine ⟨1566987366544922835940835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1044658244363281890627223 1566987366544922835940835)
            ·
              refine ⟨2350481049817384253911253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566987366544922835940835 2350481049817384253911253)
              ·
                refine ⟨55089399605094943451045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2350481049817384253911253 55089399605094943451045)
                ·
                  rfl

theorem cell21_724182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_724182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724182 prefixEnd_724182 := by exact prefixLift 724182
  have htrace : WordTrace (prefixWord ++ tailWord_724182) baseStart_724182 baseEnd_724182 := by
    simpa [prefixWord, tailWord_724182, baseEnd_724182] using wordTrace_append hprefix tailTrace_724182
  have hstable : (prefixWord ++ tailWord_724182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724182).length < 2 ^ (prefixWord ++ tailWord_724182).sum := by decide
  have hdescent : baseEnd_724182 < baseStart_724182 := by decide
  rcases family_descends (prefixWord ++ tailWord_724182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724193 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 6]
def baseStart_724193 : Nat := 118140960795 + 724193 * 2 ^ 59
def prefixEnd_724193 : Nat := 4983230072969 + 3 ^ 40 * 724193 * 2
def baseEnd_724193 : Nat := 165270709165151255669779

theorem tailTrace_724193 : CollatzResearch.WordTrace tailWord_724193 prefixEnd_724193 165270709165151255669779 := by
  unfold tailWord_724193
  simp only [CollatzResearch.WordTrace]
  refine ⟨26413488665379918162657233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17608992443586612108438155 26413488665379918162657233)
  ·
    refine ⟨19810116499034938621992925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26413488665379918162657233 19810116499034938621992925)
    ·
      refine ⟨7428793687138101983247347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19810116499034938621992925 7428793687138101983247347)
      ·
        refine ⟨11143190530707152974871021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7428793687138101983247347 11143190530707152974871021)
        ·
          refine ⟨4178696449015182365576633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11143190530707152974871021 4178696449015182365576633)
          ·
            refine ⟨3134022336761386774182475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4178696449015182365576633 3134022336761386774182475)
            ·
              refine ⟨4701033505142080161273713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3134022336761386774182475 4701033505142080161273713)
              ·
                refine ⟨3525775128856560120955285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4701033505142080161273713 3525775128856560120955285)
                ·
                  refine ⟨165270709165151255669779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3525775128856560120955285 165270709165151255669779)
                  ·
                    rfl

theorem cell21_724193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_724193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724193 prefixEnd_724193 := by exact prefixLift 724193
  have htrace : WordTrace (prefixWord ++ tailWord_724193) baseStart_724193 baseEnd_724193 := by
    simpa [prefixWord, tailWord_724193, baseEnd_724193] using wordTrace_append hprefix tailTrace_724193
  have hstable : (prefixWord ++ tailWord_724193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724193).length < 2 ^ (prefixWord ++ tailWord_724193).sum := by decide
  have hdescent : baseEnd_724193 < baseStart_724193 := by decide
  rcases family_descends (prefixWord ++ tailWord_724193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724196 : List Nat := [2, 3, 1, 1, 1, 2, 5, 3, 3]
def baseStart_724196 : Nat := 118140960795 + 724196 * 2 ^ 59
def prefixEnd_724196 : Nat := 4983230072969 + 3 ^ 40 * 724196 * 2
def baseEnd_724196 : Nat := 165271393806023917119773

theorem tailTrace_724196 : CollatzResearch.WordTrace tailWord_724196 prefixEnd_724196 165271393806023917119773 := by
  unfold tailWord_724196
  simp only [CollatzResearch.WordTrace]
  refine ⟨13206799042184524837508221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17609065389579366450010961 13206799042184524837508221)
  ·
    refine ⟨4952549640819196814065583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13206799042184524837508221 4952549640819196814065583)
    ·
      refine ⟨7428824461228795221098375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4952549640819196814065583 7428824461228795221098375)
      ·
        refine ⟨11143236691843192831647563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7428824461228795221098375 11143236691843192831647563)
        ·
          refine ⟨16714855037764789247471345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11143236691843192831647563 16714855037764789247471345)
          ·
            refine ⟨12536141278323591935603509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16714855037764789247471345 12536141278323591935603509)
            ·
              refine ⟨1175263244842836743962829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12536141278323591935603509 1175263244842836743962829)
              ·
                refine ⟨440723716816063778986061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1175263244842836743962829 440723716816063778986061)
                ·
                  refine ⟨165271393806023917119773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 440723716816063778986061 165271393806023917119773)
                  ·
                    rfl

theorem cell21_724196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_724196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724196 prefixEnd_724196 := by exact prefixLift 724196
  have htrace : WordTrace (prefixWord ++ tailWord_724196) baseStart_724196 baseEnd_724196 := by
    simpa [prefixWord, tailWord_724196, baseEnd_724196] using wordTrace_append hprefix tailTrace_724196
  have hstable : (prefixWord ++ tailWord_724196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724196).length < 2 ^ (prefixWord ++ tailWord_724196).sum := by decide
  have hdescent : baseEnd_724196 < baseStart_724196 := by decide
  rcases family_descends (prefixWord ++ tailWord_724196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724227 : List Nat := [1, 1, 1, 3, 2, 6, 2, 1, 4]
def baseStart_724227 : Nat := 118140960795 + 724227 * 2 ^ 59
def prefixEnd_724227 : Nat := 4983230072969 + 3 ^ 40 * 724227 * 2
def baseEnd_724227 : Nat := 165278468428374752103043

theorem tailTrace_724227 : CollatzResearch.WordTrace tailWord_724227 prefixEnd_724227 165278468428374752103043 := by
  unfold tailWord_724227
  simp only [CollatzResearch.WordTrace]
  refine ⟨26414728747256741969394935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17609819164837827979596623 26414728747256741969394935)
  ·
    refine ⟨39622093120885112954092403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26414728747256741969394935 39622093120885112954092403)
    ·
      refine ⟨59433139681327669431138605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39622093120885112954092403 59433139681327669431138605)
      ·
        refine ⟨22287427380497876036676977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59433139681327669431138605 22287427380497876036676977)
        ·
          refine ⟨16715570535373407027507733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22287427380497876036676977 16715570535373407027507733)
          ·
            refine ⟨783542368845628454414425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16715570535373407027507733 783542368845628454414425)
            ·
              refine ⟨587656776634221340810819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 783542368845628454414425 587656776634221340810819)
              ·
                refine ⟨881485164951332011216229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587656776634221340810819 881485164951332011216229)
                ·
                  refine ⟨165278468428374752103043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 881485164951332011216229 165278468428374752103043)
                  ·
                    rfl

theorem cell21_724227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 4].length) (baseStart_724227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724227 prefixEnd_724227 := by exact prefixLift 724227
  have htrace : WordTrace (prefixWord ++ tailWord_724227) baseStart_724227 baseEnd_724227 := by
    simpa [prefixWord, tailWord_724227, baseEnd_724227] using wordTrace_append hprefix tailTrace_724227
  have hstable : (prefixWord ++ tailWord_724227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724227).length < 2 ^ (prefixWord ++ tailWord_724227).sum := by decide
  have hdescent : baseEnd_724227 < baseStart_724227 := by decide
  rcases family_descends (prefixWord ++ tailWord_724227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724286 : List Nat := [4, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_724286 : Nat := 118140960795 + 724286 * 2 ^ 59
def prefixEnd_724286 : Nat := 4983230072969 + 3 ^ 40 * 724286 * 2
def baseEnd_724286 : Nat := 165291933032203760619589

theorem tailTrace_724286 : CollatzResearch.WordTrace tailWord_724286 prefixEnd_724286 165291933032203760619589 := by
  unfold tailWord_724286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3302110081755374380724089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17611253769361996697195141 3302110081755374380724089)
  ·
    refine ⟨2476582561316530785543067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3302110081755374380724089 2476582561316530785543067)
    ·
      refine ⟨3714873841974796178314601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2476582561316530785543067 3714873841974796178314601)
      ·
        refine ⟨2786155381481097133735951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3714873841974796178314601 2786155381481097133735951)
        ·
          refine ⟨4179233072221645700603927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786155381481097133735951 4179233072221645700603927)
          ·
            refine ⟨6268849608332468550905891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4179233072221645700603927 6268849608332468550905891)
            ·
              refine ⟨9403274412498702826358837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6268849608332468550905891 9403274412498702826358837)
              ·
                refine ⟨881556976171753389971141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9403274412498702826358837 881556976171753389971141)
                ·
                  refine ⟨165291933032203760619589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 881556976171753389971141 165291933032203760619589)
                  ·
                    rfl

theorem cell21_724286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_724286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724286 prefixEnd_724286 := by exact prefixLift 724286
  have htrace : WordTrace (prefixWord ++ tailWord_724286) baseStart_724286 baseEnd_724286 := by
    simpa [prefixWord, tailWord_724286, baseEnd_724286] using wordTrace_append hprefix tailTrace_724286
  have hstable : (prefixWord ++ tailWord_724286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724286).length < 2 ^ (prefixWord ++ tailWord_724286).sum := by decide
  have hdescent : baseEnd_724286 < baseStart_724286 := by decide
  rcases family_descends (prefixWord ++ tailWord_724286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724345 : List Nat := [1, 2, 1, 3, 2, 1, 2, 5, 4]
def baseStart_724345 : Nat := 118140960795 + 724345 * 2 ^ 59
def prefixEnd_724345 : Nat := 4983230072969 + 3 ^ 40 * 724345 * 2
def baseEnd_724345 : Nat := 165305397636032769136135

theorem tailTrace_724345 : CollatzResearch.WordTrace tailWord_724345 prefixEnd_724345 165305397636032769136135 := by
  unfold tailWord_724345
  simp only [CollatzResearch.WordTrace]
  refine ⟨26419032560829248122190489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17612688373886165414793659 26419032560829248122190489)
  ·
    refine ⟨19814274420621936091642867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26419032560829248122190489 19814274420621936091642867)
    ·
      refine ⟨29721411630932904137464301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19814274420621936091642867 29721411630932904137464301)
      ·
        refine ⟨11145529361599839051549113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29721411630932904137464301 11145529361599839051549113)
        ·
          refine ⟨8359147021199879288661835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11145529361599839051549113 8359147021199879288661835)
          ·
            refine ⟨12538720531799818932992753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8359147021199879288661835 12538720531799818932992753)
            ·
              refine ⟨9404040398849864199744565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12538720531799818932992753 9404040398849864199744565)
              ·
                refine ⟨881628787392174768726053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9404040398849864199744565 881628787392174768726053)
                ·
                  refine ⟨165305397636032769136135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 881628787392174768726053 165305397636032769136135)
                  ·
                    rfl

theorem cell21_724345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_724345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724345 prefixEnd_724345 := by exact prefixLift 724345
  have htrace : WordTrace (prefixWord ++ tailWord_724345) baseStart_724345 baseEnd_724345 := by
    simpa [prefixWord, tailWord_724345, baseEnd_724345] using wordTrace_append hprefix tailTrace_724345
  have hstable : (prefixWord ++ tailWord_724345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724345).length < 2 ^ (prefixWord ++ tailWord_724345).sum := by decide
  have hdescent : baseEnd_724345 < baseStart_724345 := by decide
  rcases family_descends (prefixWord ++ tailWord_724345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724382 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 5]
def baseStart_724382 : Nat := 118140960795 + 724382 * 2 ^ 59
def prefixEnd_724382 : Nat := 4983230072969 + 3 ^ 40 * 724382 * 2
def baseEnd_724382 : Nat := 165313841540128927019393

theorem tailTrace_724382 : CollatzResearch.WordTrace tailWord_724382 prefixEnd_724382 165313841540128927019393 := by
  unfold tailWord_724382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3302547757711900430160925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17613588041130135627524933 3302547757711900430160925)
  ·
    refine ⟨1238455409141962661310347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3302547757711900430160925 1238455409141962661310347)
    ·
      refine ⟨1857683113712943991965521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1238455409141962661310347 1857683113712943991965521)
      ·
        refine ⟨1393262335284707993974141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1857683113712943991965521 1393262335284707993974141)
        ·
          refine ⟨522473375731765497740303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1393262335284707993974141 522473375731765497740303)
          ·
            refine ⟨783710063597648246610455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522473375731765497740303 783710063597648246610455)
            ·
              refine ⟨1175565095396472369915683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783710063597648246610455 1175565095396472369915683)
              ·
                refine ⟨1763347643094708554873525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1175565095396472369915683 1763347643094708554873525)
                ·
                  refine ⟨165313841540128927019393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1763347643094708554873525 165313841540128927019393)
                  ·
                    rfl

theorem cell21_724382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_724382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724382 prefixEnd_724382 := by exact prefixLift 724382
  have htrace : WordTrace (prefixWord ++ tailWord_724382) baseStart_724382 baseEnd_724382 := by
    simpa [prefixWord, tailWord_724382, baseEnd_724382] using wordTrace_append hprefix tailTrace_724382
  have hstable : (prefixWord ++ tailWord_724382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724382).length < 2 ^ (prefixWord ++ tailWord_724382).sum := by decide
  have hdescent : baseEnd_724382 < baseStart_724382 := by decide
  rcases family_descends (prefixWord ++ tailWord_724382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724441 : List Nat := [1, 2, 1, 2, 4, 4, 2, 2, 3]
def baseStart_724441 : Nat := 118140960795 + 724441 * 2 ^ 59
def prefixEnd_724441 : Nat := 4983230072969 + 3 ^ 40 * 724441 * 2
def baseEnd_724441 : Nat := 165327306143957935535939

theorem tailTrace_724441 : CollatzResearch.WordTrace tailWord_724441 prefixEnd_724441 165327306143957935535939 := by
  unfold tailWord_724441
  simp only [CollatzResearch.WordTrace]
  refine ⟨26422533968481456517685177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17615022645654304345123451 26422533968481456517685177)
  ·
    refine ⟨19816900476361092388263883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26422533968481456517685177 19816900476361092388263883)
    ·
      refine ⟨29725350714541638582395825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19816900476361092388263883 29725350714541638582395825)
      ·
        refine ⟨22294013035906228936796869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29725350714541638582395825 22294013035906228936796869)
        ·
          refine ⟨4180127444232417925649413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22294013035906228936796869 4180127444232417925649413)
          ·
            refine ⟨783773895793578361059265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4180127444232417925649413 783773895793578361059265)
            ·
              refine ⟨587830421845183770794449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 783773895793578361059265 587830421845183770794449)
              ·
                refine ⟨440872816383887828095837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 587830421845183770794449 440872816383887828095837)
                ·
                  refine ⟨165327306143957935535939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 440872816383887828095837 165327306143957935535939)
                  ·
                    rfl

theorem cell21_724441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 3].length) (baseStart_724441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724441 prefixEnd_724441 := by exact prefixLift 724441
  have htrace : WordTrace (prefixWord ++ tailWord_724441) baseStart_724441 baseEnd_724441 := by
    simpa [prefixWord, tailWord_724441, baseEnd_724441] using wordTrace_append hprefix tailTrace_724441
  have hstable : (prefixWord ++ tailWord_724441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724441).length < 2 ^ (prefixWord ++ tailWord_724441).sum := by decide
  have hdescent : baseEnd_724441 < baseStart_724441 := by decide
  rcases family_descends (prefixWord ++ tailWord_724441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724534 : List Nat := [5, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_724534 : Nat := 118140960795 + 724534 * 2 ^ 59
def prefixEnd_724534 : Nat := 4983230072969 + 3 ^ 40 * 724534 * 2
def baseEnd_724534 : Nat := 165348530011010440485749

theorem tailTrace_724534 : CollatzResearch.WordTrace tailWord_724534 prefixEnd_724534 165348530011010440485749 := by
  unfold tailWord_724534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1651620372321533337551291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17617283971429688933880437 1651620372321533337551291)
  ·
    refine ⟨2477430558482300006326937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1651620372321533337551291 2477430558482300006326937)
    ·
      refine ⟨1858072918861725004745203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2477430558482300006326937 1858072918861725004745203)
      ·
        refine ⟨2787109378292587507117805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1858072918861725004745203 2787109378292587507117805)
        ·
          refine ⟨1045166016859720315169177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2787109378292587507117805 1045166016859720315169177)
          ·
            refine ⟨783874512644790236376883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1045166016859720315169177 783874512644790236376883)
            ·
              refine ⟨1175811768967185354565325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783874512644790236376883 1175811768967185354565325)
              ·
                refine ⟨440929413362694507961997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1175811768967185354565325 440929413362694507961997)
                ·
                  refine ⟨165348530011010440485749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 440929413362694507961997 165348530011010440485749)
                  ·
                    rfl

theorem cell21_724534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_724534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724534 prefixEnd_724534 := by exact prefixLift 724534
  have htrace : WordTrace (prefixWord ++ tailWord_724534) baseStart_724534 baseEnd_724534 := by
    simpa [prefixWord, tailWord_724534, baseEnd_724534] using wordTrace_append hprefix tailTrace_724534
  have hstable : (prefixWord ++ tailWord_724534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724534).length < 2 ^ (prefixWord ++ tailWord_724534).sum := by decide
  have hdescent : baseEnd_724534 < baseStart_724534 := by decide
  rcases family_descends (prefixWord ++ tailWord_724534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724663 : List Nat := [1, 1, 3, 1, 5, 2, 8]
def baseStart_724663 : Nat := 118140960795 + 724663 * 2 ^ 59
def prefixEnd_724663 : Nat := 4983230072969 + 3 ^ 40 * 724663 * 2
def baseEnd_724663 : Nat := 18375329952059431426165

theorem tailTrace_724663 : CollatzResearch.WordTrace tailWord_724663 prefixEnd_724663 18375329952059431426165 := by
  unfold tailWord_724663
  simp only [CollatzResearch.WordTrace]
  refine ⟨26430630973677188432266643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17620420649118125621511095 26430630973677188432266643)
  ·
    refine ⟨39645946460515782648399965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26430630973677188432266643 39645946460515782648399965)
    ·
      refine ⟨14867229922693418493149987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39645946460515782648399965 14867229922693418493149987)
      ·
        refine ⟨22300844884040127739724981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14867229922693418493149987 22300844884040127739724981)
        ·
          refine ⟨2090704207878761975599217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22300844884040127739724981 2090704207878761975599217)
          ·
            refine ⟨1568028155909071481699413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2090704207878761975599217 1568028155909071481699413)
            ·
              refine ⟨18375329952059431426165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1568028155909071481699413 18375329952059431426165)
              ·
                rfl

theorem cell21_724663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 8].length) (baseStart_724663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724663 prefixEnd_724663 := by exact prefixLift 724663
  have htrace : WordTrace (prefixWord ++ tailWord_724663) baseStart_724663 baseEnd_724663 := by
    simpa [prefixWord, tailWord_724663, baseEnd_724663] using wordTrace_append hprefix tailTrace_724663
  have hstable : (prefixWord ++ tailWord_724663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724663).length < 2 ^ (prefixWord ++ tailWord_724663).sum := by decide
  have hdescent : baseEnd_724663 < baseStart_724663 := by decide
  rcases family_descends (prefixWord ++ tailWord_724663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724666 : List Nat := [3, 1, 1, 1, 2, 6, 1, 2, 4]
def baseStart_724666 : Nat := 118140960795 + 724666 * 2 ^ 59
def prefixEnd_724666 : Nat := 4983230072969 + 3 ^ 40 * 724666 * 2
def baseEnd_724666 : Nat := 165378654209407544285479

theorem tailTrace_724666 : CollatzResearch.WordTrace tailWord_724666 prefixEnd_724666 165378654209407544285479 := by
  unfold tailWord_724666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6607685098166579986156463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17620493595110879963083901 6607685098166579986156463)
  ·
    refine ⟨9911527647249869979234695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6607685098166579986156463 9911527647249869979234695)
    ·
      refine ⟨14867291470874804968852043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9911527647249869979234695 14867291470874804968852043)
      ·
        refine ⟨22300937206312207453278065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14867291470874804968852043 22300937206312207453278065)
        ·
          refine ⟨16725702904734155589958549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22300937206312207453278065 16725702904734155589958549)
          ·
            refine ⟨784017323659413543279307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16725702904734155589958549 784017323659413543279307)
            ·
              refine ⟨1176025985489120314918961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784017323659413543279307 1176025985489120314918961)
              ·
                refine ⟨882019489116840236189221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1176025985489120314918961 882019489116840236189221)
                ·
                  refine ⟨165378654209407544285479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 882019489116840236189221 165378654209407544285479)
                  ·
                    rfl

theorem cell21_724666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_724666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724666 prefixEnd_724666 := by exact prefixLift 724666
  have htrace : WordTrace (prefixWord ++ tailWord_724666) baseStart_724666 baseEnd_724666 := by
    simpa [prefixWord, tailWord_724666, baseEnd_724666] using wordTrace_append hprefix tailTrace_724666
  have hstable : (prefixWord ++ tailWord_724666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724666).length < 2 ^ (prefixWord ++ tailWord_724666).sum := by decide
  have hdescent : baseEnd_724666 < baseStart_724666 := by decide
  rcases family_descends (prefixWord ++ tailWord_724666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724677 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 9]
def baseStart_724677 : Nat := 118140960795 + 724677 * 2 ^ 59
def prefixEnd_724677 : Nat := 4983230072969 + 3 ^ 40 * 724677 * 2
def baseEnd_724677 : Nat := 165381164559273969602123

theorem tailTrace_724677 : CollatzResearch.WordTrace tailWord_724677 prefixEnd_724677 165381164559273969602123 := by
  unfold tailWord_724677
  simp only [CollatzResearch.WordTrace]
  refine ⟨26431141595626468823276285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17620761063750979215517523 26431141595626468823276285)
  ·
    refine ⟨9911678098359925808728607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26431141595626468823276285 9911678098359925808728607)
    ·
      refine ⟨14867517147539888713092911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9911678098359925808728607 14867517147539888713092911)
      ·
        refine ⟨22301275721309833069639367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14867517147539888713092911 22301275721309833069639367)
        ·
          refine ⟨33451913581964749604459051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22301275721309833069639367 33451913581964749604459051)
          ·
            refine ⟨50177870372947124406688577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33451913581964749604459051 50177870372947124406688577)
            ·
              refine ⟨37633402779710343305016433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50177870372947124406688577 37633402779710343305016433)
              ·
                refine ⟨28225052084782757478762325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37633402779710343305016433 28225052084782757478762325)
                ·
                  refine ⟨165381164559273969602123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28225052084782757478762325 165381164559273969602123)
                  ·
                    rfl

theorem cell21_724677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_724677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724677 prefixEnd_724677 := by exact prefixLift 724677
  have htrace : WordTrace (prefixWord ++ tailWord_724677) baseStart_724677 baseEnd_724677 := by
    simpa [prefixWord, tailWord_724677, baseEnd_724677] using wordTrace_append hprefix tailTrace_724677
  have hstable : (prefixWord ++ tailWord_724677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724677).length < 2 ^ (prefixWord ++ tailWord_724677).sum := by decide
  have hdescent : baseEnd_724677 < baseStart_724677 := by decide
  rcases family_descends (prefixWord ++ tailWord_724677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724708 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 8]
def baseStart_724708 : Nat := 118140960795 + 724708 * 2 ^ 59
def prefixEnd_724708 : Nat := 4983230072969 + 3 ^ 40 * 724708 * 2
def baseEnd_724708 : Nat := 165388239181624804585393

theorem tailTrace_724708 : CollatzResearch.WordTrace tailWord_724708 prefixEnd_724708 165388239181624804585393 := by
  unfold tailWord_724708
  simp only [CollatzResearch.WordTrace]
  refine ⟨13216136129257080558827389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17621514839009440745103185 13216136129257080558827389)
  ·
    refine ⟨4956051048471405209560271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13216136129257080558827389 4956051048471405209560271)
    ·
      refine ⟨7434076572707107814340407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4956051048471405209560271 7434076572707107814340407)
      ·
        refine ⟨11151114859060661721510611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7434076572707107814340407 11151114859060661721510611)
        ·
          refine ⟨16726672288590992582265917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11151114859060661721510611 16726672288590992582265917)
          ·
            refine ⟨6272502108221622218349719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16726672288590992582265917 6272502108221622218349719)
            ·
              refine ⟨9408753162332433327524579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6272502108221622218349719 9408753162332433327524579)
              ·
                refine ⟨14113129743498649991286869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9408753162332433327524579 14113129743498649991286869)
                ·
                  refine ⟨165388239181624804585393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14113129743498649991286869 165388239181624804585393)
                  ·
                    rfl

theorem cell21_724708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_724708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724708 prefixEnd_724708 := by exact prefixLift 724708
  have htrace : WordTrace (prefixWord ++ tailWord_724708) baseStart_724708 baseEnd_724708 := by
    simpa [prefixWord, tailWord_724708, baseEnd_724708] using wordTrace_append hprefix tailTrace_724708
  have hstable : (prefixWord ++ tailWord_724708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724708).length < 2 ^ (prefixWord ++ tailWord_724708).sum := by decide
  have hdescent : baseEnd_724708 < baseStart_724708 := by decide
  rcases family_descends (prefixWord ++ tailWord_724708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724753 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 7]
def baseStart_724753 : Nat := 118140960795 + 724753 * 2 ^ 59
def prefixEnd_724753 : Nat := 4983230072969 + 3 ^ 40 * 724753 * 2
def baseEnd_724753 : Nat := 165398508794714726335301

theorem tailTrace_724753 : CollatzResearch.WordTrace tailWord_724753 prefixEnd_724753 165398508794714726335301 := by
  unfold tailWord_724753
  simp only [CollatzResearch.WordTrace]
  refine ⟨26433913543351133803042913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17622609028900755868695275 26433913543351133803042913)
  ·
    refine ⟨19825435157513350352282185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26433913543351133803042913 19825435157513350352282185)
    ·
      refine ⟨14869076368135012764211639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19825435157513350352282185 14869076368135012764211639)
      ·
        refine ⟨22303614552202519146317459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14869076368135012764211639 22303614552202519146317459)
        ·
          refine ⟨33455421828303778719476189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22303614552202519146317459 33455421828303778719476189)
          ·
            refine ⟨12545783185613917019803571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33455421828303778719476189 12545783185613917019803571)
            ·
              refine ⟨18818674778420875529705357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12545783185613917019803571 18818674778420875529705357)
              ·
                refine ⟨7057003041907828323639509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18818674778420875529705357 7057003041907828323639509)
                ·
                  refine ⟨165398508794714726335301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7057003041907828323639509 165398508794714726335301)
                  ·
                    rfl

theorem cell21_724753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_724753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724753 prefixEnd_724753 := by exact prefixLift 724753
  have htrace : WordTrace (prefixWord ++ tailWord_724753) baseStart_724753 baseEnd_724753 := by
    simpa [prefixWord, tailWord_724753, baseEnd_724753] using wordTrace_append hprefix tailTrace_724753
  have hstable : (prefixWord ++ tailWord_724753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724753).length < 2 ^ (prefixWord ++ tailWord_724753).sum := by decide
  have hdescent : baseEnd_724753 < baseStart_724753 := by decide
  rcases family_descends (prefixWord ++ tailWord_724753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724835 : List Nat := [1, 1, 1, 5, 5, 1, 1, 2, 4]
def baseStart_724835 : Nat := 118140960795 + 724835 * 2 ^ 59
def prefixEnd_724835 : Nat := 4983230072969 + 3 ^ 40 * 724835 * 2
def baseEnd_724835 : Nat := 165417222311900805968467

theorem tailTrace_724835 : CollatzResearch.WordTrace tailWord_724835 prefixEnd_724835 165417222311900805968467 := by
  unfold tailWord_724835
  simp only [CollatzResearch.WordTrace]
  refine ⟨26436904329054061807527959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17624602886036041205018639 26436904329054061807527959)
  ·
    refine ⟨39655356493581092711291939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26436904329054061807527959 39655356493581092711291939)
    ·
      refine ⟨59483034740371639066937909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39655356493581092711291939 59483034740371639066937909)
      ·
        refine ⟨5576534506909841162525429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59483034740371639066937909 5576534506909841162525429)
        ·
          refine ⟨522800110022797608986759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5576534506909841162525429 522800110022797608986759)
          ·
            refine ⟨784200165034196413480139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522800110022797608986759 784200165034196413480139)
            ·
              refine ⟨1176300247551294620220209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784200165034196413480139 1176300247551294620220209)
              ·
                refine ⟨882225185663470965165157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1176300247551294620220209 882225185663470965165157)
                ·
                  refine ⟨165417222311900805968467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 882225185663470965165157 165417222311900805968467)
                  ·
                    rfl

theorem cell21_724835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 4].length) (baseStart_724835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724835 prefixEnd_724835 := by exact prefixLift 724835
  have htrace : WordTrace (prefixWord ++ tailWord_724835) baseStart_724835 baseEnd_724835 := by
    simpa [prefixWord, tailWord_724835, baseEnd_724835] using wordTrace_append hprefix tailTrace_724835
  have hstable : (prefixWord ++ tailWord_724835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724835).length < 2 ^ (prefixWord ++ tailWord_724835).sum := by decide
  have hdescent : baseEnd_724835 < baseStart_724835 := by decide
  rcases family_descends (prefixWord ++ tailWord_724835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724897 : List Nat := [1, 2, 3, 4, 2, 1, 3, 2, 3]
def baseStart_724897 : Nat := 118140960795 + 724897 * 2 ^ 59
def prefixEnd_724897 : Nat := 4983230072969 + 3 ^ 40 * 724897 * 2
def baseEnd_724897 : Nat := 165431371556602475935007

theorem tailTrace_724897 : CollatzResearch.WordTrace tailWord_724897 prefixEnd_724897 165431371556602475935007 := by
  unfold tailWord_724897
  simp only [CollatzResearch.WordTrace]
  refine ⟨26439165654829446396284945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17626110436552964264189963 26439165654829446396284945)
  ·
    refine ⟨19829374241122084797213709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26439165654829446396284945 19829374241122084797213709)
    ·
      refine ⟨7436015340420781798955141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19829374241122084797213709 7436015340420781798955141)
      ·
        refine ⟨1394252876328896587304089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7436015340420781798955141 1394252876328896587304089)
        ·
          refine ⟨1045689657246672440478067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1394252876328896587304089 1045689657246672440478067)
          ·
            refine ⟨1568534485870008660717101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045689657246672440478067 1568534485870008660717101)
            ·
              refine ⟨588200432201253247768913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1568534485870008660717101 588200432201253247768913)
              ·
                refine ⟨441150324150939935826685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588200432201253247768913 441150324150939935826685)
                ·
                  refine ⟨165431371556602475935007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 441150324150939935826685 165431371556602475935007)
                  ·
                    rfl

theorem cell21_724897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 3].length) (baseStart_724897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724897 prefixEnd_724897 := by exact prefixLift 724897
  have htrace : WordTrace (prefixWord ++ tailWord_724897) baseStart_724897 baseEnd_724897 := by
    simpa [prefixWord, tailWord_724897, baseEnd_724897] using wordTrace_append hprefix tailTrace_724897
  have hstable : (prefixWord ++ tailWord_724897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724897).length < 2 ^ (prefixWord ++ tailWord_724897).sum := by decide
  have hdescent : baseEnd_724897 < baseStart_724897 := by decide
  rcases family_descends (prefixWord ++ tailWord_724897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724905 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 5]
def baseStart_724905 : Nat := 118140960795 + 724905 * 2 ^ 59
def prefixEnd_724905 : Nat := 4983230072969 + 3 ^ 40 * 724905 * 2
def baseEnd_724905 : Nat := 165433197265596239801657

theorem tailTrace_724905 : CollatzResearch.WordTrace tailWord_724905 prefixEnd_724905 165433197265596239801657 := by
  unfold tailWord_724905
  simp only [CollatzResearch.WordTrace]
  refine ⟨26439457438800463762576169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17626304959200309175050779 26439457438800463762576169)
  ·
    refine ⟨19829593079100347821932127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26439457438800463762576169 19829593079100347821932127)
    ·
      refine ⟨29744389618650521732898191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19829593079100347821932127 29744389618650521732898191)
      ·
        refine ⟨44616584427975782599347287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29744389618650521732898191 44616584427975782599347287)
        ·
          refine ⟨66924876641963673899020931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44616584427975782599347287 66924876641963673899020931)
          ·
            refine ⟨100387314962945510848531397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66924876641963673899020931 100387314962945510848531397)
            ·
              refine ⟨18822621555552283284099637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100387314962945510848531397 18822621555552283284099637)
              ·
                refine ⟨1764620770833026557884341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18822621555552283284099637 1764620770833026557884341)
                ·
                  refine ⟨165433197265596239801657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1764620770833026557884341 165433197265596239801657)
                  ·
                    rfl

theorem cell21_724905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_724905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_724905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_724905 prefixEnd_724905 := by exact prefixLift 724905
  have htrace : WordTrace (prefixWord ++ tailWord_724905) baseStart_724905 baseEnd_724905 := by
    simpa [prefixWord, tailWord_724905, baseEnd_724905] using wordTrace_append hprefix tailTrace_724905
  have hstable : (prefixWord ++ tailWord_724905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724905).length < 2 ^ (prefixWord ++ tailWord_724905).sum := by decide
  have hdescent : baseEnd_724905 < baseStart_724905 := by decide
  rcases family_descends (prefixWord ++ tailWord_724905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725015 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 5]
def baseStart_725015 : Nat := 118140960795 + 725015 * 2 ^ 59
def prefixEnd_725015 : Nat := 4983230072969 + 3 ^ 40 * 725015 * 2
def baseEnd_725015 : Nat := 165458300764260492968099

theorem tailTrace_725015 : CollatzResearch.WordTrace tailWord_725015 prefixEnd_725015 165458300764260492968099 := by
  unfold tailWord_725015
  simp only [CollatzResearch.WordTrace]
  refine ⟨26443469468401952549080499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17628979645601301699386999 26443469468401952549080499)
  ·
    refine ⟨39665204202602928823620749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26443469468401952549080499 39665204202602928823620749)
    ·
      refine ⟨14874451575976098308857781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39665204202602928823620749 14874451575976098308857781)
      ·
        refine ⟨1394479835247759216455417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14874451575976098308857781 1394479835247759216455417)
        ·
          refine ⟨1045859876435819412341563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1394479835247759216455417 1045859876435819412341563)
          ·
            refine ⟨1568789814653729118512345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045859876435819412341563 1568789814653729118512345)
            ·
              refine ⟨1176592360990296838884259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1568789814653729118512345 1176592360990296838884259)
              ·
                refine ⟨1764888541485445258326389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1176592360990296838884259 1764888541485445258326389)
                ·
                  refine ⟨165458300764260492968099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1764888541485445258326389 165458300764260492968099)
                  ·
                    rfl

theorem cell21_725015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 5].length) (baseStart_725015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725015 prefixEnd_725015 := by exact prefixLift 725015
  have htrace : WordTrace (prefixWord ++ tailWord_725015) baseStart_725015 baseEnd_725015 := by
    simpa [prefixWord, tailWord_725015, baseEnd_725015] using wordTrace_append hprefix tailTrace_725015
  have hstable : (prefixWord ++ tailWord_725015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725015).length < 2 ^ (prefixWord ++ tailWord_725015).sum := by decide
  have hdescent : baseEnd_725015 < baseStart_725015 := by decide
  rcases family_descends (prefixWord ++ tailWord_725015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725043 : List Nat := [1, 1, 1, 2, 4, 1, 6, 5]
def baseStart_725043 : Nat := 118140960795 + 725043 * 2 ^ 59
def prefixEnd_725043 : Nat := 4983230072969 + 3 ^ 40 * 725043 * 2
def baseEnd_725043 : Nat := 55154896915246222167125

theorem tailTrace_725043 : CollatzResearch.WordTrace tailWord_725043 prefixEnd_725043 55154896915246222167125 := by
  unfold tailWord_725043
  simp only [CollatzResearch.WordTrace]
  refine ⟨26444490712300513331099783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17629660474867008887399855 26444490712300513331099783)
  ·
    refine ⟨39666736068450769996649675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26444490712300513331099783 39666736068450769996649675)
    ·
      refine ⟨59500104102676154994974513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39666736068450769996649675 59500104102676154994974513)
      ·
        refine ⟨44625078077007116246230885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59500104102676154994974513 44625078077007116246230885)
        ·
          refine ⟨8367202139438834296168291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44625078077007116246230885 8367202139438834296168291)
          ·
            refine ⟨12550803209158251444252437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8367202139438834296168291 12550803209158251444252437)
            ·
              refine ⟨588318900429293036449333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12550803209158251444252437 588318900429293036449333)
              ·
                refine ⟨55154896915246222167125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 588318900429293036449333 55154896915246222167125)
                ·
                  rfl

theorem cell21_725043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 5].length) (baseStart_725043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725043 prefixEnd_725043 := by exact prefixLift 725043
  have htrace : WordTrace (prefixWord ++ tailWord_725043) baseStart_725043 baseEnd_725043 := by
    simpa [prefixWord, tailWord_725043, baseEnd_725043] using wordTrace_append hprefix tailTrace_725043
  have hstable : (prefixWord ++ tailWord_725043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725043).length < 2 ^ (prefixWord ++ tailWord_725043).sum := by decide
  have hdescent : baseEnd_725043 < baseStart_725043 := by decide
  rcases family_descends (prefixWord ++ tailWord_725043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725049 : List Nat := [1, 2, 1, 5, 4, 1, 1, 3, 3]
def baseStart_725049 : Nat := 118140960795 + 725049 * 2 ^ 59
def prefixEnd_725049 : Nat := 4983230072969 + 3 ^ 40 * 725049 * 2
def baseEnd_725049 : Nat := 165466060027483989401363

theorem tailTrace_725049 : CollatzResearch.WordTrace tailWord_725049 prefixEnd_725049 165466060027483989401363 := by
  unfold tailWord_725049
  simp only [CollatzResearch.WordTrace]
  refine ⟨26444709550278776355818201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17629806366852517570545467 26444709550278776355818201)
  ·
    refine ⟨19833532162709082266863651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26444709550278776355818201 19833532162709082266863651)
    ·
      refine ⟨29750298244063623400295477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19833532162709082266863651 29750298244063623400295477)
      ·
        refine ⟨2789090460380964693777701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29750298244063623400295477 2789090460380964693777701)
        ·
          refine ⟨522954461321430880083319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2789090460380964693777701 522954461321430880083319)
          ·
            refine ⟨784431691982146320124979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522954461321430880083319 784431691982146320124979)
            ·
              refine ⟨1176647537973219480187469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784431691982146320124979 1176647537973219480187469)
              ·
                refine ⟨441242826739957305070301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1176647537973219480187469 441242826739957305070301)
                ·
                  refine ⟨165466060027483989401363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 441242826739957305070301 165466060027483989401363)
                  ·
                    rfl

theorem cell21_725049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 3].length) (baseStart_725049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725049 prefixEnd_725049 := by exact prefixLift 725049
  have htrace : WordTrace (prefixWord ++ tailWord_725049) baseStart_725049 baseEnd_725049 := by
    simpa [prefixWord, tailWord_725049, baseEnd_725049] using wordTrace_append hprefix tailTrace_725049
  have hstable : (prefixWord ++ tailWord_725049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725049).length < 2 ^ (prefixWord ++ tailWord_725049).sum := by decide
  have hdescent : baseEnd_725049 < baseStart_725049 := by decide
  rcases family_descends (prefixWord ++ tailWord_725049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725142 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_725142 : Nat := 118140960795 + 725142 * 2 ^ 59
def prefixEnd_725142 : Nat := 4983230072969 + 3 ^ 40 * 725142 * 2
def baseEnd_725142 : Nat := 165487283894536494351173

theorem tailTrace_725142 : CollatzResearch.WordTrace tailWord_725142 prefixEnd_725142 165487283894536494351173 := by
  unfold tailWord_725142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1653006346183865827434605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17632067692627902159302453 1653006346183865827434605)
  ·
    refine ⟨619877379818949685287977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1653006346183865827434605 619877379818949685287977)
    ·
      refine ⟨464908034864212263965983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 619877379818949685287977 464908034864212263965983)
      ·
        refine ⟨697362052296318395948975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464908034864212263965983 697362052296318395948975)
        ·
          refine ⟨1046043078444477593923463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697362052296318395948975 1046043078444477593923463)
          ·
            refine ⟨1569064617666716390885195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046043078444477593923463 1569064617666716390885195)
            ·
              refine ⟨2353596926500074586327793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569064617666716390885195 2353596926500074586327793)
              ·
                refine ⟨1765197694875055939745845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2353596926500074586327793 1765197694875055939745845)
                ·
                  refine ⟨165487283894536494351173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1765197694875055939745845 165487283894536494351173)
                  ·
                    rfl

theorem cell21_725142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_725142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725142 prefixEnd_725142 := by exact prefixLift 725142
  have htrace : WordTrace (prefixWord ++ tailWord_725142) baseStart_725142 baseEnd_725142 := by
    simpa [prefixWord, tailWord_725142, baseEnd_725142] using wordTrace_append hprefix tailTrace_725142
  have hstable : (prefixWord ++ tailWord_725142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725142).length < 2 ^ (prefixWord ++ tailWord_725142).sum := by decide
  have hdescent : baseEnd_725142 < baseStart_725142 := by decide
  rcases family_descends (prefixWord ++ tailWord_725142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725198 : List Nat := [4, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_725198 : Nat := 118140960795 + 725198 * 2 ^ 59
def prefixEnd_725198 : Nat := 4983230072969 + 3 ^ 40 * 725198 * 2
def baseEnd_725198 : Nat := 165500063857492841417725

theorem tailTrace_725198 : CollatzResearch.WordTrace tailWord_725198 prefixEnd_725198 165500063857492841417725 := by
  unfold tailWord_725198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3306268003342371850374031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17633429351159316535328165 3306268003342371850374031)
  ·
    refine ⟨4959402005013557775561047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3306268003342371850374031 4959402005013557775561047)
    ·
      refine ⟨7439103007520336663341571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4959402005013557775561047 7439103007520336663341571)
      ·
        refine ⟨11158654511280504995012357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7439103007520336663341571 11158654511280504995012357)
        ·
          refine ⟨2092247720865094686564817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11158654511280504995012357 2092247720865094686564817)
          ·
            refine ⟨1569185790648821014923613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2092247720865094686564817 1569185790648821014923613)
            ·
              refine ⟨588444671493307880596355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1569185790648821014923613 588444671493307880596355)
              ·
                refine ⟨882667007239961820894533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588444671493307880596355 882667007239961820894533)
                ·
                  refine ⟨165500063857492841417725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 882667007239961820894533 165500063857492841417725)
                  ·
                    rfl

theorem cell21_725198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_725198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725198 prefixEnd_725198 := by exact prefixLift 725198
  have htrace : WordTrace (prefixWord ++ tailWord_725198) baseStart_725198 baseEnd_725198 := by
    simpa [prefixWord, tailWord_725198, baseEnd_725198] using wordTrace_append hprefix tailTrace_725198
  have hstable : (prefixWord ++ tailWord_725198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725198).length < 2 ^ (prefixWord ++ tailWord_725198).sum := by decide
  have hdescent : baseEnd_725198 < baseStart_725198 := by decide
  rcases family_descends (prefixWord ++ tailWord_725198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725209 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 5]
def baseStart_725209 : Nat := 118140960795 + 725209 * 2 ^ 59
def prefixEnd_725209 : Nat := 4983230072969 + 3 ^ 40 * 725209 * 2
def baseEnd_725209 : Nat := 165502574207359266734369

theorem tailTrace_725209 : CollatzResearch.WordTrace tailWord_725209 prefixEnd_725209 165502574207359266734369 := by
  unfold tailWord_725209
  simp only [CollatzResearch.WordTrace]
  refine ⟨26450545229699123681642681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17633696819799415787761787 26450545229699123681642681)
  ·
    refine ⟨19837908922274342761232011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26450545229699123681642681 19837908922274342761232011)
    ·
      refine ⟨29756863383411514141848017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19837908922274342761232011 29756863383411514141848017)
      ·
        refine ⟨22317647537558635606386013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29756863383411514141848017 22317647537558635606386013)
        ·
          refine ⟨8369117826584488352394755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22317647537558635606386013 8369117826584488352394755)
          ·
            refine ⟨12553676739876732528592133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8369117826584488352394755 12553676739876732528592133)
            ·
              refine ⟨2353814388726887349111025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12553676739876732528592133 2353814388726887349111025)
              ·
                refine ⟨1765360791545165511833269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2353814388726887349111025 1765360791545165511833269)
                ·
                  refine ⟨165502574207359266734369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1765360791545165511833269 165502574207359266734369)
                  ·
                    rfl

theorem cell21_725209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_725209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725209 prefixEnd_725209 := by exact prefixLift 725209
  have htrace : WordTrace (prefixWord ++ tailWord_725209) baseStart_725209 baseEnd_725209 := by
    simpa [prefixWord, tailWord_725209, baseEnd_725209] using wordTrace_append hprefix tailTrace_725209
  have hstable : (prefixWord ++ tailWord_725209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725209).length < 2 ^ (prefixWord ++ tailWord_725209).sum := by decide
  have hdescent : baseEnd_725209 < baseStart_725209 := by decide
  rcases family_descends (prefixWord ++ tailWord_725209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725257 : List Nat := [1, 2, 1, 1, 3, 4, 4, 1, 4]
def baseStart_725257 : Nat := 118140960795 + 725257 * 2 ^ 59
def prefixEnd_725257 : Nat := 4983230072969 + 3 ^ 40 * 725257 * 2
def baseEnd_725257 : Nat := 165513528461321849934271

theorem tailTrace_725257 : CollatzResearch.WordTrace tailWord_725257 prefixEnd_725257 165513528461321849934271 := by
  unfold tailWord_725257
  simp only [CollatzResearch.WordTrace]
  refine ⟨26452295933525227879390025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17634863955683485252926683 26452295933525227879390025)
  ·
    refine ⟨19839221950143920909542519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26452295933525227879390025 19839221950143920909542519)
    ·
      refine ⟨29758832925215881364313779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19839221950143920909542519 29758832925215881364313779)
      ·
        refine ⟨44638249387823822046470669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29758832925215881364313779 44638249387823822046470669)
        ·
          refine ⟨16739343520433933267426501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44638249387823822046470669 16739343520433933267426501)
          ·
            refine ⟨3138626910081362487642469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16739343520433933267426501 3138626910081362487642469)
            ·
              refine ⟨588492545640255466432963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3138626910081362487642469 588492545640255466432963)
              ·
                refine ⟨882738818460383199649445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588492545640255466432963 882738818460383199649445)
                ·
                  refine ⟨165513528461321849934271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 882738818460383199649445 165513528461321849934271)
                  ·
                    rfl

theorem cell21_725257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 4].length) (baseStart_725257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725257 prefixEnd_725257 := by exact prefixLift 725257
  have htrace : WordTrace (prefixWord ++ tailWord_725257) baseStart_725257 baseEnd_725257 := by
    simpa [prefixWord, tailWord_725257, baseEnd_725257] using wordTrace_append hprefix tailTrace_725257
  have hstable : (prefixWord ++ tailWord_725257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725257).length < 2 ^ (prefixWord ++ tailWord_725257).sum := by decide
  have hdescent : baseEnd_725257 < baseStart_725257 := by decide
  rcases family_descends (prefixWord ++ tailWord_725257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725294 : List Nat := [4, 1, 3, 3, 1, 2, 2, 2, 3]
def baseStart_725294 : Nat := 118140960795 + 725294 * 2 ^ 59
def prefixEnd_725294 : Nat := 4983230072969 + 3 ^ 40 * 725294 * 2
def baseEnd_725294 : Nat := 165521972365418007817529

theorem tailTrace_725294 : CollatzResearch.WordTrace tailWord_725294 prefixEnd_725294 165521972365418007817529 := by
  unfold tailWord_725294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3306705679298897899810867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17635763622927455465657957 3306705679298897899810867)
  ·
    refine ⟨4960058518948346849716301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3306705679298897899810867 4960058518948346849716301)
    ·
      refine ⟨1860021944605630068643613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4960058518948346849716301 1860021944605630068643613)
      ·
        refine ⟨697508229227111275741355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1860021944605630068643613 697508229227111275741355)
        ·
          refine ⟨1046262343840666913612033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697508229227111275741355 1046262343840666913612033)
          ·
            refine ⟨784696757880500185209025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1046262343840666913612033 784696757880500185209025)
            ·
              refine ⟨588522568410375138906769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784696757880500185209025 588522568410375138906769)
              ·
                refine ⟨441391926307781354180077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588522568410375138906769 441391926307781354180077)
                ·
                  refine ⟨165521972365418007817529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 441391926307781354180077 165521972365418007817529)
                  ·
                    rfl

theorem cell21_725294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_725294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725294 prefixEnd_725294 := by exact prefixLift 725294
  have htrace : WordTrace (prefixWord ++ tailWord_725294) baseStart_725294 baseEnd_725294 := by
    simpa [prefixWord, tailWord_725294, baseEnd_725294] using wordTrace_append hprefix tailTrace_725294
  have hstable : (prefixWord ++ tailWord_725294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725294).length < 2 ^ (prefixWord ++ tailWord_725294).sum := by decide
  have hdescent : baseEnd_725294 < baseStart_725294 := by decide
  rcases family_descends (prefixWord ++ tailWord_725294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725330 : List Nat := [3, 2, 2, 1, 1, 1, 2, 9]
def baseStart_725330 : Nat := 118140960795 + 725330 * 2 ^ 59
def prefixEnd_725330 : Nat := 4983230072969 + 3 ^ 40 * 725330 * 2
def baseEnd_725330 : Nat := 55176729351963315072485

theorem tailTrace_725330 : CollatzResearch.WordTrace tailWord_725330 prefixEnd_725330 55176729351963315072485 := by
  unfold tailWord_725330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6613739615565190336699361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17636638974840507564531629 6613739615565190336699361)
  ·
    refine ⟨4960304711673892752524521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6613739615565190336699361 4960304711673892752524521)
    ·
      refine ⟨3720228533755419564393391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4960304711673892752524521 3720228533755419564393391)
      ·
        refine ⟨5580342800633129346590087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3720228533755419564393391 5580342800633129346590087)
        ·
          refine ⟨8370514200949694019885131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5580342800633129346590087 8370514200949694019885131)
          ·
            refine ⟨12555771301424541029827697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8370514200949694019885131 12555771301424541029827697)
            ·
              refine ⟨9416828476068405772370773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12555771301424541029827697 9416828476068405772370773)
              ·
                refine ⟨55176729351963315072485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9416828476068405772370773 55176729351963315072485)
                ·
                  rfl

theorem cell21_725330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_725330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725330 prefixEnd_725330 := by exact prefixLift 725330
  have htrace : WordTrace (prefixWord ++ tailWord_725330) baseStart_725330 baseEnd_725330 := by
    simpa [prefixWord, tailWord_725330, baseEnd_725330] using wordTrace_append hprefix tailTrace_725330
  have hstable : (prefixWord ++ tailWord_725330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725330).length < 2 ^ (prefixWord ++ tailWord_725330).sum := by decide
  have hdescent : baseEnd_725330 < baseStart_725330 := by decide
  rcases family_descends (prefixWord ++ tailWord_725330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725342 : List Nat := [4, 4, 2, 1, 2, 1, 1, 2, 4]
def baseStart_725342 : Nat := 118140960795 + 725342 * 2 ^ 59
def prefixEnd_725342 : Nat := 4983230072969 + 3 ^ 40 * 725342 * 2
def baseEnd_725342 : Nat := 165532926619380591017431

theorem tailTrace_725342 : CollatzResearch.WordTrace tailWord_725342 prefixEnd_725342 165532926619380591017431 := by
  unfold tailWord_725342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3306924517277160924529285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17636930758811524930822853 3306924517277160924529285)
  ·
    refine ⟨620048346989467673349241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3306924517277160924529285 620048346989467673349241)
    ·
      refine ⟨465036260242100755011931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 620048346989467673349241 465036260242100755011931)
      ·
        refine ⟨697554390363151132517897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465036260242100755011931 697554390363151132517897)
        ·
          refine ⟨523165792772363349388423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697554390363151132517897 523165792772363349388423)
          ·
            refine ⟨784748689158545024082635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523165792772363349388423 784748689158545024082635)
            ·
              refine ⟨1177123033737817536123953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784748689158545024082635 1177123033737817536123953)
              ·
                refine ⟨882842275303363152092965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1177123033737817536123953 882842275303363152092965)
                ·
                  refine ⟨165532926619380591017431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 882842275303363152092965 165532926619380591017431)
                  ·
                    rfl

theorem cell21_725342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_725342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725342 prefixEnd_725342 := by exact prefixLift 725342
  have htrace : WordTrace (prefixWord ++ tailWord_725342) baseStart_725342 baseEnd_725342 := by
    simpa [prefixWord, tailWord_725342, baseEnd_725342] using wordTrace_append hprefix tailTrace_725342
  have hstable : (prefixWord ++ tailWord_725342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725342).length < 2 ^ (prefixWord ++ tailWord_725342).sum := by decide
  have hdescent : baseEnd_725342 < baseStart_725342 := by decide
  rcases family_descends (prefixWord ++ tailWord_725342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725398 : List Nat := [5, 3, 1, 2, 1, 2, 7]
def baseStart_725398 : Nat := 118140960795 + 725398 * 2 ^ 59
def prefixEnd_725398 : Nat := 4983230072969 + 3 ^ 40 * 725398 * 2
def baseEnd_725398 : Nat := 18393967398037437564887

theorem tailTrace_725398 : CollatzResearch.WordTrace tailWord_725398 prefixEnd_725398 18393967398037437564887 := by
  unfold tailWord_725398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1653589914125900560017053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17638292417342939306848565 1653589914125900560017053)
  ·
    refine ⟨620096217797212710006395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1653589914125900560017053 620096217797212710006395)
    ·
      refine ⟨930144326695819065009593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 620096217797212710006395 930144326695819065009593)
      ·
        refine ⟨697608245021864298757195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 930144326695819065009593 697608245021864298757195)
        ·
          refine ⟨1046412367532796448135793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697608245021864298757195 1046412367532796448135793)
          ·
            refine ⟨784809275649597336101845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1046412367532796448135793 784809275649597336101845)
            ·
              refine ⟨18393967398037437564887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 784809275649597336101845 18393967398037437564887)
              ·
                rfl

theorem cell21_725398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 7].length) (baseStart_725398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725398 prefixEnd_725398 := by exact prefixLift 725398
  have htrace : WordTrace (prefixWord ++ tailWord_725398) baseStart_725398 baseEnd_725398 := by
    simpa [prefixWord, tailWord_725398, baseEnd_725398] using wordTrace_append hprefix tailTrace_725398
  have hstable : (prefixWord ++ tailWord_725398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725398).length < 2 ^ (prefixWord ++ tailWord_725398).sum := by decide
  have hdescent : baseEnd_725398 < baseStart_725398 := by decide
  rcases family_descends (prefixWord ++ tailWord_725398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725454 : List Nat := [4, 1, 1, 1, 2, 1, 1, 7, 3]
def baseStart_725454 : Nat := 118140960795 + 725454 * 2 ^ 59
def prefixEnd_725454 : Nat := 4983230072969 + 3 ^ 40 * 725454 * 2
def baseEnd_725454 : Nat := 165558486545293285150535

theorem tailTrace_725454 : CollatzResearch.WordTrace tailWord_725454 prefixEnd_725454 165558486545293285150535 := by
  unfold tailWord_725454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307435139226441315538927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17639654075874353682874277 3307435139226441315538927)
  ·
    refine ⟨4961152708839661973308391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3307435139226441315538927 4961152708839661973308391)
    ·
      refine ⟨7441729063259492959962587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4961152708839661973308391 7441729063259492959962587)
      ·
        refine ⟨11162593594889239439943881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7441729063259492959962587 11162593594889239439943881)
        ·
          refine ⟨8371945196166929579957911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11162593594889239439943881 8371945196166929579957911)
          ·
            refine ⟨12557917794250394369936867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8371945196166929579957911 12557917794250394369936867)
            ·
              refine ⟨18836876691375591554905301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12557917794250394369936867 18836876691375591554905301)
              ·
                refine ⟨441489297454115427068093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18836876691375591554905301 441489297454115427068093)
                ·
                  refine ⟨165558486545293285150535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 441489297454115427068093 165558486545293285150535)
                  ·
                    rfl

theorem cell21_725454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_725454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725454 prefixEnd_725454 := by exact prefixLift 725454
  have htrace : WordTrace (prefixWord ++ tailWord_725454) baseStart_725454 baseEnd_725454 := by
    simpa [prefixWord, tailWord_725454, baseEnd_725454] using wordTrace_append hprefix tailTrace_725454
  have hstable : (prefixWord ++ tailWord_725454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725454).length < 2 ^ (prefixWord ++ tailWord_725454).sum := by decide
  have hdescent : baseEnd_725454 < baseStart_725454 := by decide
  rcases family_descends (prefixWord ++ tailWord_725454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725471 : List Nat := [1, 1, 2, 3, 3, 2, 4, 2, 3]
def baseStart_725471 : Nat := 118140960795 + 725471 * 2 ^ 59
def prefixEnd_725471 : Nat := 4983230072969 + 3 ^ 40 * 725471 * 2
def baseEnd_725471 : Nat := 165562366176905033367167

theorem tailTrace_725471 : CollatzResearch.WordTrace tailWord_725471 prefixEnd_725471 165562366176905033367167 := by
  unfold tailWord_725471
  simp only [CollatzResearch.WordTrace]
  refine ⟨26460101154749942427680267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17640067436499961618453511 26460101154749942427680267)
  ·
    refine ⟨39690151732124913641520401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26460101154749942427680267 39690151732124913641520401)
    ·
      refine ⟨29767613799093685231140301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39690151732124913641520401 29767613799093685231140301)
      ·
        refine ⟨11162855174660131961677613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29767613799093685231140301 11162855174660131961677613)
        ·
          refine ⟨4186070690497549485629105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11162855174660131961677613 4186070690497549485629105)
          ·
            refine ⟨3139553017873162114221829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4186070690497549485629105 3139553017873162114221829)
            ·
              refine ⟨588666190851217896416593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3139553017873162114221829 588666190851217896416593)
              ·
                refine ⟨441499643138413422312445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588666190851217896416593 441499643138413422312445)
                ·
                  refine ⟨165562366176905033367167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 441499643138413422312445 165562366176905033367167)
                  ·
                    rfl

theorem cell21_725471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 3].length) (baseStart_725471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725471 prefixEnd_725471 := by exact prefixLift 725471
  have htrace : WordTrace (prefixWord ++ tailWord_725471) baseStart_725471 baseEnd_725471 := by
    simpa [prefixWord, tailWord_725471, baseEnd_725471] using wordTrace_append hprefix tailTrace_725471
  have hstable : (prefixWord ++ tailWord_725471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725471).length < 2 ^ (prefixWord ++ tailWord_725471).sum := by decide
  have hdescent : baseEnd_725471 < baseStart_725471 := by decide
  rcases family_descends (prefixWord ++ tailWord_725471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725474 : List Nat := [3, 3, 3, 2, 2, 1, 1, 6]
def baseStart_725474 : Nat := 118140960795 + 725474 * 2 ^ 59
def prefixEnd_725474 : Nat := 4983230072969 + 3 ^ 40 * 725474 * 2
def baseEnd_725474 : Nat := 55187683605925898272387

theorem tailTrace_725474 : CollatzResearch.WordTrace tailWord_725474 prefixEnd_725474 55187683605925898272387 := by
  unfold tailWord_725474
  simp only [CollatzResearch.WordTrace]
  refine ⟨6615052643434768485009869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17640140382492715960026317 6615052643434768485009869)
  ·
    refine ⟨2480644741288038181878701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6615052643434768485009869 2480644741288038181878701)
    ·
      refine ⟨930241777983014318204513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2480644741288038181878701 930241777983014318204513)
      ·
        refine ⟨697681333487260738653385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 930241777983014318204513 697681333487260738653385)
        ·
          refine ⟨523261000115445553990039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697681333487260738653385 523261000115445553990039)
          ·
            refine ⟨784891500173168330985059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523261000115445553990039 784891500173168330985059)
            ·
              refine ⟨1177337250259752496477589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784891500173168330985059 1177337250259752496477589)
              ·
                refine ⟨55187683605925898272387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1177337250259752496477589 55187683605925898272387)
                ·
                  rfl

theorem cell21_725474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_725474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725474 prefixEnd_725474 := by exact prefixLift 725474
  have htrace : WordTrace (prefixWord ++ tailWord_725474) baseStart_725474 baseEnd_725474 := by
    simpa [prefixWord, tailWord_725474, baseEnd_725474] using wordTrace_append hprefix tailTrace_725474
  have hstable : (prefixWord ++ tailWord_725474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725474).length < 2 ^ (prefixWord ++ tailWord_725474).sum := by decide
  have hdescent : baseEnd_725474 < baseStart_725474 := by decide
  rcases family_descends (prefixWord ++ tailWord_725474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725485 : List Nat := [1, 5, 1, 3, 1, 1, 2, 3, 4]
def baseStart_725485 : Nat := 118140960795 + 725485 * 2 ^ 59
def prefixEnd_725485 : Nat := 4983230072969 + 3 ^ 40 * 725485 * 2
def baseEnd_725485 : Nat := 165565561167644120133805

theorem tailTrace_725485 : CollatzResearch.WordTrace tailWord_725485 prefixEnd_725485 165565561167644120133805 := by
  unfold tailWord_725485
  simp only [CollatzResearch.WordTrace]
  refine ⟨26460611776699222818689909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17640407851132815212459939 26460611776699222818689909)
  ·
    refine ⟨2480682354065552139252179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26460611776699222818689909 2480682354065552139252179)
    ·
      refine ⟨3721023531098328208878269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2480682354065552139252179 3721023531098328208878269)
      ·
        refine ⟨1395383824161873078329351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3721023531098328208878269 1395383824161873078329351)
        ·
          refine ⟨2093075736242809617494027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1395383824161873078329351 2093075736242809617494027)
          ·
            refine ⟨3139613604364214426241041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2093075736242809617494027 3139613604364214426241041)
            ·
              refine ⟨2354710203273160819680781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3139613604364214426241041 2354710203273160819680781)
              ·
                refine ⟨883016326227435307380293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2354710203273160819680781 883016326227435307380293)
                ·
                  refine ⟨165565561167644120133805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 883016326227435307380293 165565561167644120133805)
                  ·
                    rfl

theorem cell21_725485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_725485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725485 prefixEnd_725485 := by exact prefixLift 725485
  have htrace : WordTrace (prefixWord ++ tailWord_725485) baseStart_725485 baseEnd_725485 := by
    simpa [prefixWord, tailWord_725485, baseEnd_725485] using wordTrace_append hprefix tailTrace_725485
  have hstable : (prefixWord ++ tailWord_725485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725485).length < 2 ^ (prefixWord ++ tailWord_725485).sum := by decide
  have hdescent : baseEnd_725485 < baseStart_725485 := by decide
  rcases family_descends (prefixWord ++ tailWord_725485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725530 : List Nat := [3, 1, 1, 3, 1, 1, 4, 4, 3]
def baseStart_725530 : Nat := 118140960795 + 725530 * 2 ^ 59
def prefixEnd_725530 : Nat := 4983230072969 + 3 ^ 40 * 725530 * 2
def baseEnd_725530 : Nat := 165575830780734041883713

theorem tailTrace_725530 : CollatzResearch.WordTrace tailWord_725530 prefixEnd_725530 165575830780734041883713 := by
  unfold tailWord_725530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6615563265384048876019511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17641502041024130336052029 6615563265384048876019511)
  ·
    refine ⟨9923344898076073314029267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6615563265384048876019511 9923344898076073314029267)
    ·
      refine ⟨14885017347114109971043901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9923344898076073314029267 14885017347114109971043901)
      ·
        refine ⟨5581881505167791239141463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14885017347114109971043901 5581881505167791239141463)
        ·
          refine ⟨8372822257751686858712195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5581881505167791239141463 8372822257751686858712195)
          ·
            refine ⟨12559233386627530288068293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8372822257751686858712195 12559233386627530288068293)
            ·
              refine ⟨2354856259992661929012805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12559233386627530288068293 2354856259992661929012805)
              ·
                refine ⟨441535548748624111689901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2354856259992661929012805 441535548748624111689901)
                ·
                  refine ⟨165575830780734041883713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 441535548748624111689901 165575830780734041883713)
                  ·
                    rfl

theorem cell21_725530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_725530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725530 prefixEnd_725530 := by exact prefixLift 725530
  have htrace : WordTrace (prefixWord ++ tailWord_725530) baseStart_725530 baseEnd_725530 := by
    simpa [prefixWord, tailWord_725530, baseEnd_725530] using wordTrace_append hprefix tailTrace_725530
  have hstable : (prefixWord ++ tailWord_725530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725530).length < 2 ^ (prefixWord ++ tailWord_725530).sum := by decide
  have hdescent : baseEnd_725530 < baseStart_725530 := by decide
  rcases family_descends (prefixWord ++ tailWord_725530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725589 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 5]
def baseStart_725589 : Nat := 118140960795 + 725589 * 2 ^ 59
def prefixEnd_725589 : Nat := 4983230072969 + 3 ^ 40 * 725589 * 2
def baseEnd_725589 : Nat := 165589295384563050400259

theorem tailTrace_725589 : CollatzResearch.WordTrace tailWord_725589 prefixEnd_725589 165589295384563050400259 := by
  unfold tailWord_725589
  simp only [CollatzResearch.WordTrace]
  refine ⟨26464404968322448580475821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17642936645548299053650547 26464404968322448580475821)
  ·
    refine ⟨9924151863120918217678433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26464404968322448580475821 9924151863120918217678433)
    ·
      refine ⟨7443113897340688663258825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9924151863120918217678433 7443113897340688663258825)
      ·
        refine ⟨5582335423005516497444119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7443113897340688663258825 5582335423005516497444119)
        ·
          refine ⟨8373503134508274746166179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5582335423005516497444119 8373503134508274746166179)
          ·
            refine ⟨12560254701762412119249269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8373503134508274746166179 12560254701762412119249269)
            ·
              refine ⟨1177523878290226136179619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12560254701762412119249269 1177523878290226136179619)
              ·
                refine ⟨1766285817435339204269429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1177523878290226136179619 1766285817435339204269429)
                ·
                  refine ⟨165589295384563050400259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1766285817435339204269429 165589295384563050400259)
                  ·
                    rfl

theorem cell21_725589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_725589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725589 prefixEnd_725589 := by exact prefixLift 725589
  have htrace : WordTrace (prefixWord ++ tailWord_725589) baseStart_725589 baseEnd_725589 := by
    simpa [prefixWord, tailWord_725589, baseEnd_725589] using wordTrace_append hprefix tailTrace_725589
  have hstable : (prefixWord ++ tailWord_725589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725589).length < 2 ^ (prefixWord ++ tailWord_725589).sum := by decide
  have hdescent : baseEnd_725589 < baseStart_725589 := by decide
  rcases family_descends (prefixWord ++ tailWord_725589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725696 : List Nat := [2, 1, 1, 2, 4, 2, 3, 2, 4]
def baseStart_725696 : Nat := 118140960795 + 725696 * 2 ^ 59
def prefixEnd_725696 : Nat := 4983230072969 + 3 ^ 40 * 725696 * 2
def baseEnd_725696 : Nat := 165613714242354642116707

theorem tailTrace_725696 : CollatzResearch.WordTrace tailWord_725696 prefixEnd_725696 165613714242354642116707 := by
  unfold tailWord_725696
  simp only [CollatzResearch.WordTrace]
  refine ⟨13234153789467402927310471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17645538385956537236413961 13234153789467402927310471)
  ·
    refine ⟨19851230684201104390965707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13234153789467402927310471 19851230684201104390965707)
    ·
      refine ⟨29776846026301656586448561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19851230684201104390965707 29776846026301656586448561)
      ·
        refine ⟨22332634519726242439836421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29776846026301656586448561 22332634519726242439836421)
        ·
          refine ⟨4187368972448670457469329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22332634519726242439836421 4187368972448670457469329)
          ·
            refine ⟨3140526729336502843101997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4187368972448670457469329 3140526729336502843101997)
            ·
              refine ⟨1177697523501188566163249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3140526729336502843101997 1177697523501188566163249)
              ·
                refine ⟨883273142625891424622437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1177697523501188566163249 883273142625891424622437)
                ·
                  refine ⟨165613714242354642116707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 883273142625891424622437 165613714242354642116707)
                  ·
                    rfl

theorem cell21_725696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_725696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725696 prefixEnd_725696 := by exact prefixLift 725696
  have htrace : WordTrace (prefixWord ++ tailWord_725696) baseStart_725696 baseEnd_725696 := by
    simpa [prefixWord, tailWord_725696, baseEnd_725696] using wordTrace_append hprefix tailTrace_725696
  have hstable : (prefixWord ++ tailWord_725696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725696).length < 2 ^ (prefixWord ++ tailWord_725696).sum := by decide
  have hdescent : baseEnd_725696 < baseStart_725696 := by decide
  rcases family_descends (prefixWord ++ tailWord_725696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725727 : List Nat := [1, 1, 2, 3, 2, 5, 2, 5]
def baseStart_725727 : Nat := 118140960795 + 725727 * 2 ^ 59
def prefixEnd_725727 : Nat := 4983230072969 + 3 ^ 40 * 725727 * 2
def baseEnd_725727 : Nat := 55206929621568492366659

theorem tailTrace_725727 : CollatzResearch.WordTrace tailWord_725727 prefixEnd_725727 55206929621568492366659 := by
  unfold tailWord_725727
  simp only [CollatzResearch.WordTrace]
  refine ⟨26469438241822498148999435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17646292161214998765999623 26469438241822498148999435)
  ·
    refine ⟨39704157362733747223499153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26469438241822498148999435 39704157362733747223499153)
    ·
      refine ⟨29778118022050310417624365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39704157362733747223499153 29778118022050310417624365)
      ·
        refine ⟨11166794258268866406609137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29778118022050310417624365 11166794258268866406609137)
        ·
          refine ⟨8375095693701649804956853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11166794258268866406609137 8375095693701649804956853)
          ·
            refine ⟨785165221284529669214705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8375095693701649804956853 785165221284529669214705)
            ·
              refine ⟨588873915963397251911029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785165221284529669214705 588873915963397251911029)
              ·
                refine ⟨55206929621568492366659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 588873915963397251911029 55206929621568492366659)
                ·
                  rfl

theorem cell21_725727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 5].length) (baseStart_725727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725727 prefixEnd_725727 := by exact prefixLift 725727
  have htrace : WordTrace (prefixWord ++ tailWord_725727) baseStart_725727 baseEnd_725727 := by
    simpa [prefixWord, tailWord_725727, baseEnd_725727] using wordTrace_append hprefix tailTrace_725727
  have hstable : (prefixWord ++ tailWord_725727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725727).length < 2 ^ (prefixWord ++ tailWord_725727).sum := by decide
  have hdescent : baseEnd_725727 < baseStart_725727 := by decide
  rcases family_descends (prefixWord ++ tailWord_725727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725758 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_725758 : Nat := 118140960795 + 725758 * 2 ^ 59
def prefixEnd_725758 : Nat := 4983230072969 + 3 ^ 40 * 725758 * 2
def baseEnd_725758 : Nat := 165627863487056312083247

theorem tailTrace_725758 : CollatzResearch.WordTrace tailWord_725758 prefixEnd_725758 165627863487056312083247 := by
  unfold tailWord_725758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3308821113088773805422241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17647045936473460295585285 3308821113088773805422241)
  ·
    refine ⟨2481615834816580354066681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3308821113088773805422241 2481615834816580354066681)
    ·
      refine ⟨1861211876112435265550011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2481615834816580354066681 1861211876112435265550011)
      ·
        refine ⟨2791817814168652898325017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1861211876112435265550011 2791817814168652898325017)
        ·
          refine ⟨2093863360626489673743763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2791817814168652898325017 2093863360626489673743763)
          ·
            refine ⟨3140795040939734510615645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2093863360626489673743763 3140795040939734510615645)
            ·
              refine ⟨1177798140352400441480867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3140795040939734510615645 1177798140352400441480867)
              ·
                refine ⟨1766697210528600662221301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1177798140352400441480867 1766697210528600662221301)
                ·
                  refine ⟨165627863487056312083247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1766697210528600662221301 165627863487056312083247)
                  ·
                    rfl

theorem cell21_725758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_725758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725758 prefixEnd_725758 := by exact prefixLift 725758
  have htrace : WordTrace (prefixWord ++ tailWord_725758) baseStart_725758 baseEnd_725758 := by
    simpa [prefixWord, tailWord_725758, baseEnd_725758] using wordTrace_append hprefix tailTrace_725758
  have hstable : (prefixWord ++ tailWord_725758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725758).length < 2 ^ (prefixWord ++ tailWord_725758).sum := by decide
  have hdescent : baseEnd_725758 < baseStart_725758 := by decide
  rcases family_descends (prefixWord ++ tailWord_725758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725769 : List Nat := [1, 2, 1, 1, 3, 2, 3, 8]
def baseStart_725769 : Nat := 118140960795 + 725769 * 2 ^ 59
def prefixEnd_725769 : Nat := 4983230072969 + 3 ^ 40 * 725769 * 2
def baseEnd_725769 : Nat := 55210124612307579133297

theorem tailTrace_725769 : CollatzResearch.WordTrace tailWord_725769 prefixEnd_725769 55210124612307579133297 := by
  unfold tailWord_725769
  simp only [CollatzResearch.WordTrace]
  refine ⟨26470970107670339322028361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17647313405113559548018907 26470970107670339322028361)
  ·
    refine ⟨19853227580752754491521271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26470970107670339322028361 19853227580752754491521271)
    ·
      refine ⟨29779841371129131737281907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19853227580752754491521271 29779841371129131737281907)
      ·
        refine ⟨44669762056693697605922861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29779841371129131737281907 44669762056693697605922861)
        ·
          refine ⟨16751160771260136602221073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44669762056693697605922861 16751160771260136602221073)
          ·
            refine ⟨12563370578445102451665805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16751160771260136602221073 12563370578445102451665805)
            ·
              refine ⟨4711263966916913419374677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12563370578445102451665805 4711263966916913419374677)
              ·
                refine ⟨55210124612307579133297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4711263966916913419374677 55210124612307579133297)
                ·
                  rfl

theorem cell21_725769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 8].length) (baseStart_725769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725769 prefixEnd_725769 := by exact prefixLift 725769
  have htrace : WordTrace (prefixWord ++ tailWord_725769) baseStart_725769 baseEnd_725769 := by
    simpa [prefixWord, tailWord_725769, baseEnd_725769] using wordTrace_append hprefix tailTrace_725769
  have hstable : (prefixWord ++ tailWord_725769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725769).length < 2 ^ (prefixWord ++ tailWord_725769).sum := by decide
  have hdescent : baseEnd_725769 < baseStart_725769 := by decide
  rcases family_descends (prefixWord ++ tailWord_725769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725927 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 5]
def baseStart_725927 : Nat := 118140960795 + 725927 * 2 ^ 59
def prefixEnd_725927 : Nat := 4983230072969 + 3 ^ 40 * 725927 * 2
def baseEnd_725927 : Nat := 165666431589549573766235

theorem tailTrace_725927 : CollatzResearch.WordTrace tailWord_725927 prefixEnd_725927 165666431589549573766235 := by
  unfold tailWord_725927
  simp only [CollatzResearch.WordTrace]
  refine ⟨26476732841097932306280035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17651155227398621537520023 26476732841097932306280035)
  ·
    refine ⟨39715099261646898459420053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26476732841097932306280035 39715099261646898459420053)
    ·
      refine ⟨1861645277889698365285315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39715099261646898459420053 1861645277889698365285315)
      ·
        refine ⟨2792467916834547547927973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1861645277889698365285315 2792467916834547547927973)
        ·
          refine ⟨523587734406477665236495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2792467916834547547927973 523587734406477665236495)
          ·
            refine ⟨785381601609716497854743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523587734406477665236495 785381601609716497854743)
            ·
              refine ⟨1178072402414574746782115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785381601609716497854743 1178072402414574746782115)
              ·
                refine ⟨1767108603621862120173173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1178072402414574746782115 1767108603621862120173173)
                ·
                  refine ⟨165666431589549573766235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1767108603621862120173173 165666431589549573766235)
                  ·
                    rfl

theorem cell21_725927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 5].length) (baseStart_725927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725927 prefixEnd_725927 := by exact prefixLift 725927
  have htrace : WordTrace (prefixWord ++ tailWord_725927) baseStart_725927 baseEnd_725927 := by
    simpa [prefixWord, tailWord_725927, baseEnd_725927] using wordTrace_append hprefix tailTrace_725927
  have hstable : (prefixWord ++ tailWord_725927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725927).length < 2 ^ (prefixWord ++ tailWord_725927).sum := by decide
  have hdescent : baseEnd_725927 < baseStart_725927 := by decide
  rcases family_descends (prefixWord ++ tailWord_725927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725969 : List Nat := [1, 2, 2, 1, 2, 1, 4, 5, 3]
def baseStart_725969 : Nat := 118140960795 + 725969 * 2 ^ 59
def prefixEnd_725969 : Nat := 4983230072969 + 3 ^ 40 * 725969 * 2
def baseEnd_725969 : Nat := 165676016561766834066149

theorem tailTrace_725969 : CollatzResearch.WordTrace tailWord_725969 prefixEnd_725969 165676016561766834066149 := by
  unfold tailWord_725969
  simp only [CollatzResearch.WordTrace]
  refine ⟨26478264706945773479308961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17652176471297182319539307 26478264706945773479308961)
  ·
    refine ⟨19858698530209330109481721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26478264706945773479308961 19858698530209330109481721)
    ·
      refine ⟨14894023897656997582111291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19858698530209330109481721 14894023897656997582111291)
      ·
        refine ⟨22341035846485496373166937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14894023897656997582111291 22341035846485496373166937)
        ·
          refine ⟨16755776884864122279875203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22341035846485496373166937 16755776884864122279875203)
          ·
            refine ⟨25133665327296183419812805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16755776884864122279875203 25133665327296183419812805)
            ·
              refine ⟨4712562248868034391214901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25133665327296183419812805 4712562248868034391214901)
              ·
                refine ⟨441802710831378224176397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4712562248868034391214901 441802710831378224176397)
                ·
                  refine ⟨165676016561766834066149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 441802710831378224176397 165676016561766834066149)
                  ·
                    rfl

theorem cell21_725969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 3].length) (baseStart_725969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_725969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_725969 prefixEnd_725969 := by exact prefixLift 725969
  have htrace : WordTrace (prefixWord ++ tailWord_725969) baseStart_725969 baseEnd_725969 := by
    simpa [prefixWord, tailWord_725969, baseEnd_725969] using wordTrace_append hprefix tailTrace_725969
  have hstable : (prefixWord ++ tailWord_725969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725969).length < 2 ^ (prefixWord ++ tailWord_725969).sum := by decide
  have hdescent : baseEnd_725969 < baseStart_725969 := by decide
  rcases family_descends (prefixWord ++ tailWord_725969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726034 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 6]
def baseStart_726034 : Nat := 118140960795 + 726034 * 2 ^ 59
def prefixEnd_726034 : Nat := 4983230072969 + 3 ^ 40 * 726034 * 2
def baseEnd_726034 : Nat := 165690850447341165482683

theorem tailTrace_726034 : CollatzResearch.WordTrace tailWord_726034 prefixEnd_726034 165690850447341165482683 := by
  unfold tailWord_726034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6620158862927572395106289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17653756967806859720283437 6620158862927572395106289)
  ·
    refine ⟨4965119147195679296329717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6620158862927572395106289 4965119147195679296329717)
    ·
      refine ⟨465479920049594934030911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4965119147195679296329717 465479920049594934030911)
      ·
        refine ⟨698219880074392401046367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465479920049594934030911 698219880074392401046367)
        ·
          refine ⟨1047329820111588601569551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 698219880074392401046367 1047329820111588601569551)
          ·
            refine ⟨1570994730167382902354327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1047329820111588601569551 1570994730167382902354327)
            ·
              refine ⟨2356492095251074353531491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570994730167382902354327 2356492095251074353531491)
              ·
                refine ⟨3534738142876611530297237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2356492095251074353531491 3534738142876611530297237)
                ·
                  refine ⟨165690850447341165482683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3534738142876611530297237 165690850447341165482683)
                  ·
                    rfl

theorem cell21_726034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_726034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726034 prefixEnd_726034 := by exact prefixLift 726034
  have htrace : WordTrace (prefixWord ++ tailWord_726034) baseStart_726034 baseEnd_726034 := by
    simpa [prefixWord, tailWord_726034, baseEnd_726034] using wordTrace_append hprefix tailTrace_726034
  have hstable : (prefixWord ++ tailWord_726034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726034).length < 2 ^ (prefixWord ++ tailWord_726034).sum := by decide
  have hdescent : baseEnd_726034 < baseStart_726034 := by decide
  rcases family_descends (prefixWord ++ tailWord_726034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726110 : List Nat := [4, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_726110 : Nat := 118140960795 + 726110 * 2 ^ 59
def prefixEnd_726110 : Nat := 4983230072969 + 3 ^ 40 * 726110 * 2
def baseEnd_726110 : Nat := 165708194682781922215861

theorem tailTrace_726110 : CollatzResearch.WordTrace tailWord_726110 prefixEnd_726110 165708194682781922215861 := by
  unfold tailWord_726110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3310425924929369320023973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17655604932956636373461189 3310425924929369320023973)
  ·
    refine ⟨620704860924256747504495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3310425924929369320023973 620704860924256747504495)
    ·
      refine ⟨931057291386385121256743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 620704860924256747504495 931057291386385121256743)
      ·
        refine ⟨1396585937079577681885115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 931057291386385121256743 1396585937079577681885115)
        ·
          refine ⟨2094878905619366522827673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1396585937079577681885115 2094878905619366522827673)
          ·
            refine ⟨1571159179214524892120755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2094878905619366522827673 1571159179214524892120755)
            ·
              refine ⟨2356738768821787338181133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571159179214524892120755 2356738768821787338181133)
              ·
                refine ⟨883777038308170251817925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2356738768821787338181133 883777038308170251817925)
                ·
                  refine ⟨165708194682781922215861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 883777038308170251817925 165708194682781922215861)
                  ·
                    rfl

theorem cell21_726110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_726110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726110 prefixEnd_726110 := by exact prefixLift 726110
  have htrace : WordTrace (prefixWord ++ tailWord_726110) baseStart_726110 baseEnd_726110 := by
    simpa [prefixWord, tailWord_726110, baseEnd_726110] using wordTrace_append hprefix tailTrace_726110
  have hstable : (prefixWord ++ tailWord_726110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726110).length < 2 ^ (prefixWord ++ tailWord_726110).sum := by decide
  have hdescent : baseEnd_726110 < baseStart_726110 := by decide
  rcases family_descends (prefixWord ++ tailWord_726110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726149 : List Nat := [1, 3, 1, 1, 6, 9]
def baseStart_726149 : Nat := 118140960795 + 726149 * 2 ^ 59
def prefixEnd_726149 : Nat := 4983230072969 + 3 ^ 40 * 726149 * 2
def baseEnd_726149 : Nat := 6137670185708389669103

theorem tailTrace_726149 : CollatzResearch.WordTrace tailWord_726149 prefixEnd_726149 6137670185708389669103 := by
  unfold tailWord_726149
  simp only [CollatzResearch.WordTrace]
  refine ⟨26484829846293664220861501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17656553230862442813907667 26484829846293664220861501)
  ·
    refine ⟨9931811192360124082823063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26484829846293664220861501 9931811192360124082823063)
    ·
      refine ⟨14897716788540186124234595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9931811192360124082823063 14897716788540186124234595)
      ·
        refine ⟨22346575182810279186351893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14897716788540186124234595 22346575182810279186351893)
        ·
          refine ⟨1047495711694231836860245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22346575182810279186351893 1047495711694231836860245)
          ·
            refine ⟨6137670185708389669103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1047495711694231836860245 6137670185708389669103)
            ·
              rfl

theorem cell21_726149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 9].length) (baseStart_726149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726149 prefixEnd_726149 := by exact prefixLift 726149
  have htrace : WordTrace (prefixWord ++ tailWord_726149) baseStart_726149 baseEnd_726149 := by
    simpa [prefixWord, tailWord_726149, baseEnd_726149] using wordTrace_append hprefix tailTrace_726149
  have hstable : (prefixWord ++ tailWord_726149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726149).length < 2 ^ (prefixWord ++ tailWord_726149).sum := by decide
  have hdescent : baseEnd_726149 < baseStart_726149 := by decide
  rcases family_descends (prefixWord ++ tailWord_726149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726180 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 7]
def baseStart_726180 : Nat := 118140960795 + 726180 * 2 ^ 59
def prefixEnd_726180 : Nat := 4983230072969 + 3 ^ 40 * 726180 * 2
def baseEnd_726180 : Nat := 165724169636477356049051

theorem tailTrace_726180 : CollatzResearch.WordTrace tailWord_726180 prefixEnd_726180 165724169636477356049051 := by
  unfold tailWord_726180
  simp only [CollatzResearch.WordTrace]
  refine ⟨13242980254590678257619997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17657307006120904343493329 13242980254590678257619997)
  ·
    refine ⟨4966117595471504346607499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13242980254590678257619997 4966117595471504346607499)
    ·
      refine ⟨7449176393207256519911249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4966117595471504346607499 7449176393207256519911249)
      ·
        refine ⟨5586882294905442389933437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7449176393207256519911249 5586882294905442389933437)
        ·
          refine ⟨2095080860589540896225039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5586882294905442389933437 2095080860589540896225039)
          ·
            refine ⟨3142621290884311344337559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2095080860589540896225039 3142621290884311344337559)
            ·
              refine ⟨4713931936326467016506339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3142621290884311344337559 4713931936326467016506339)
              ·
                refine ⟨7070897904489700524759509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4713931936326467016506339 7070897904489700524759509)
                ·
                  refine ⟨165724169636477356049051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7070897904489700524759509 165724169636477356049051)
                  ·
                    rfl

theorem cell21_726180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_726180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726180 prefixEnd_726180 := by exact prefixLift 726180
  have htrace : WordTrace (prefixWord ++ tailWord_726180) baseStart_726180 baseEnd_726180 := by
    simpa [prefixWord, tailWord_726180, baseEnd_726180] using wordTrace_append hprefix tailTrace_726180
  have hstable : (prefixWord ++ tailWord_726180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726180).length < 2 ^ (prefixWord ++ tailWord_726180).sum := by decide
  have hdescent : baseEnd_726180 < baseStart_726180 := by decide
  rcases family_descends (prefixWord ++ tailWord_726180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726183 : List Nat := [1, 1, 6, 2, 1, 2, 3, 5]
def baseStart_726183 : Nat := 118140960795 + 726183 * 2 ^ 59
def prefixEnd_726183 : Nat := 4983230072969 + 3 ^ 40 * 726183 * 2
def baseEnd_726183 : Nat := 55241618092450005833015

theorem tailTrace_726183 : CollatzResearch.WordTrace tailWord_726183 prefixEnd_726183 55241618092450005833015 := by
  unfold tailWord_726183
  simp only [CollatzResearch.WordTrace]
  refine ⟨26486069928170488027599203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17657379952113658685066135 26486069928170488027599203)
  ·
    refine ⟨39729104892255732041398805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26486069928170488027599203 39729104892255732041398805)
    ·
      refine ⟨1862301791824487439440569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39729104892255732041398805 1862301791824487439440569)
      ·
        refine ⟨1396726343868365579580427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1862301791824487439440569 1396726343868365579580427)
        ·
          refine ⟨2095089515802548369370641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1396726343868365579580427 2095089515802548369370641)
          ·
            refine ⟨1571317136851911277027981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2095089515802548369370641 1571317136851911277027981)
            ·
              refine ⟨589243926319466728885493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1571317136851911277027981 589243926319466728885493)
              ·
                refine ⟨55241618092450005833015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 589243926319466728885493 55241618092450005833015)
                ·
                  rfl

theorem cell21_726183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 5].length) (baseStart_726183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726183 prefixEnd_726183 := by exact prefixLift 726183
  have htrace : WordTrace (prefixWord ++ tailWord_726183) baseStart_726183 baseEnd_726183 := by
    simpa [prefixWord, tailWord_726183, baseEnd_726183] using wordTrace_append hprefix tailTrace_726183
  have hstable : (prefixWord ++ tailWord_726183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726183).length < 2 ^ (prefixWord ++ tailWord_726183).sum := by decide
  have hdescent : baseEnd_726183 < baseStart_726183 := by decide
  rcases family_descends (prefixWord ++ tailWord_726183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726273 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 5]
def baseStart_726273 : Nat := 118140960795 + 726273 * 2 ^ 59
def prefixEnd_726273 : Nat := 4983230072969 + 3 ^ 40 * 726273 * 2
def baseEnd_726273 : Nat := 165745393503529860998861

theorem tailTrace_726273 : CollatzResearch.WordTrace tailWord_726273 prefixEnd_726273 165745393503529860998861 := by
  unfold tailWord_726273
  simp only [CollatzResearch.WordTrace]
  refine ⟨26489352497844433398375473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17659568331896288932250315 26489352497844433398375473)
  ·
    refine ⟨19867014373383325048781605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26489352497844433398375473 19867014373383325048781605)
    ·
      refine ⟨3725065195009373446646551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19867014373383325048781605 3725065195009373446646551)
      ·
        refine ⟨5587597792514060169969827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3725065195009373446646551 5587597792514060169969827)
        ·
          refine ⟨8381396688771090254954741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5587597792514060169969827 8381396688771090254954741)
          ·
            refine ⟨785755939572289711402007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8381396688771090254954741 785755939572289711402007)
            ·
              refine ⟨1178633909358434567103011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785755939572289711402007 1178633909358434567103011)
              ·
                refine ⟨1767950864037651850654517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1178633909358434567103011 1767950864037651850654517)
                ·
                  refine ⟨165745393503529860998861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1767950864037651850654517 165745393503529860998861)
                  ·
                    rfl

theorem cell21_726273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_726273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726273 prefixEnd_726273 := by exact prefixLift 726273
  have htrace : WordTrace (prefixWord ++ tailWord_726273) baseStart_726273 baseEnd_726273 := by
    simpa [prefixWord, tailWord_726273, baseEnd_726273] using wordTrace_append hprefix tailTrace_726273
  have hstable : (prefixWord ++ tailWord_726273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726273).length < 2 ^ (prefixWord ++ tailWord_726273).sum := by decide
  have hdescent : baseEnd_726273 < baseStart_726273 := by decide
  rcases family_descends (prefixWord ++ tailWord_726273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726380 : List Nat := [2, 2, 1, 1, 5, 3, 1, 2, 4]
def baseStart_726380 : Nat := 118140960795 + 726380 * 2 ^ 59
def prefixEnd_726380 : Nat := 4983230072969 + 3 ^ 40 * 726380 * 2
def baseEnd_726380 : Nat := 165769812361321452715309

theorem tailTrace_726380 : CollatzResearch.WordTrace tailWord_726380 prefixEnd_726380 165769812361321452715309 := by
  unfold tailWord_726380
  simp only [CollatzResearch.WordTrace]
  refine ⟨13246627554228395336260297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17662170072304527115013729 13246627554228395336260297)
  ·
    refine ⟨9934970665671296502195223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13246627554228395336260297 9934970665671296502195223)
    ·
      refine ⟨14902455998506944753292835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9934970665671296502195223 14902455998506944753292835)
      ·
        refine ⟨22353683997760417129939253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14902455998506944753292835 22353683997760417129939253)
        ·
          refine ⟨2095657874790039105931805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22353683997760417129939253 2095657874790039105931805)
          ·
            refine ⟨785871703046264664724427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2095657874790039105931805 785871703046264664724427)
            ·
              refine ⟨1178807554569396997086641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785871703046264664724427 1178807554569396997086641)
              ·
                refine ⟨884105665927047747814981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1178807554569396997086641 884105665927047747814981)
                ·
                  refine ⟨165769812361321452715309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 884105665927047747814981 165769812361321452715309)
                  ·
                    rfl

theorem cell21_726380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_726380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726380 prefixEnd_726380 := by exact prefixLift 726380
  have htrace : WordTrace (prefixWord ++ tailWord_726380) baseStart_726380 baseEnd_726380 := by
    simpa [prefixWord, tailWord_726380, baseEnd_726380] using wordTrace_append hprefix tailTrace_726380
  have hstable : (prefixWord ++ tailWord_726380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726380).length < 2 ^ (prefixWord ++ tailWord_726380).sum := by decide
  have hdescent : baseEnd_726380 < baseStart_726380 := by decide
  rcases family_descends (prefixWord ++ tailWord_726380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726408 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 5]
def baseStart_726408 : Nat := 118140960795 + 726408 * 2 ^ 59
def prefixEnd_726408 : Nat := 4983230072969 + 3 ^ 40 * 726408 * 2
def baseEnd_726408 : Nat := 165776202342799626248585

theorem tailTrace_726408 : CollatzResearch.WordTrace tailWord_726408 prefixEnd_726408 165776202342799626248585 := by
  unfold tailWord_726408
  simp only [CollatzResearch.WordTrace]
  refine ⟨13247138176177675727269939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17662850901570234303026585 13247138176177675727269939)
  ·
    refine ⟨19870707264266513590904909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13247138176177675727269939 19870707264266513590904909)
    ·
      refine ⟨7451515224099942596589341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19870707264266513590904909 7451515224099942596589341)
      ·
        refine ⟨2794318209037478473721003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7451515224099942596589341 2794318209037478473721003)
        ·
          refine ⟨4191477313556217710581505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794318209037478473721003 4191477313556217710581505)
          ·
            refine ⟨3143607985167163282936129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4191477313556217710581505 3143607985167163282936129)
            ·
              refine ⟨2357705988875372462202097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3143607985167163282936129 2357705988875372462202097)
              ·
                refine ⟨1768279491656529346651573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2357705988875372462202097 1768279491656529346651573)
                ·
                  refine ⟨165776202342799626248585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1768279491656529346651573 165776202342799626248585)
                  ·
                    rfl

theorem cell21_726408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_726408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726408 prefixEnd_726408 := by exact prefixLift 726408
  have htrace : WordTrace (prefixWord ++ tailWord_726408) baseStart_726408 baseEnd_726408 := by
    simpa [prefixWord, tailWord_726408, baseEnd_726408] using wordTrace_append hprefix tailTrace_726408
  have hstable : (prefixWord ++ tailWord_726408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726408).length < 2 ^ (prefixWord ++ tailWord_726408).sum := by decide
  have hdescent : baseEnd_726408 < baseStart_726408 := by decide
  rcases family_descends (prefixWord ++ tailWord_726408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726425 : List Nat := [1, 2, 1, 2, 1, 5, 3, 3, 3]
def baseStart_726425 : Nat := 118140960795 + 726425 * 2 ^ 59
def prefixEnd_726425 : Nat := 4983230072969 + 3 ^ 40 * 726425 * 2
def baseEnd_726425 : Nat := 165780081974411374465217

theorem tailTrace_726425 : CollatzResearch.WordTrace tailWord_726425 prefixEnd_726425 165780081974411374465217 := by
  unfold tailWord_726425
  simp only [CollatzResearch.WordTrace]
  refine ⟨26494896393293763357908729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17663264262195842238605819 26494896393293763357908729)
  ·
    refine ⟨19871172294970322518431547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26494896393293763357908729 19871172294970322518431547)
    ·
      refine ⟨29806758442455483777647321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19871172294970322518431547 29806758442455483777647321)
      ·
        refine ⟨22355068831841612833235491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29806758442455483777647321 22355068831841612833235491)
        ·
          refine ⟨33532603247762419249853237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22355068831841612833235491 33532603247762419249853237)
          ·
            refine ⟨3143681554477726804673741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33532603247762419249853237 3143681554477726804673741)
            ·
              refine ⟨1178880582929147551752653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3143681554477726804673741 1178880582929147551752653)
              ·
                refine ⟨442080218598430331907245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1178880582929147551752653 442080218598430331907245)
                ·
                  refine ⟨165780081974411374465217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 442080218598430331907245 165780081974411374465217)
                  ·
                    rfl

theorem cell21_726425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 3].length) (baseStart_726425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726425 prefixEnd_726425 := by exact prefixLift 726425
  have htrace : WordTrace (prefixWord ++ tailWord_726425) baseStart_726425 baseEnd_726425 := by
    simpa [prefixWord, tailWord_726425, baseEnd_726425] using wordTrace_append hprefix tailTrace_726425
  have hstable : (prefixWord ++ tailWord_726425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726425).length < 2 ^ (prefixWord ++ tailWord_726425).sum := by decide
  have hdescent : baseEnd_726425 < baseStart_726425 := by decide
  rcases family_descends (prefixWord ++ tailWord_726425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726439 : List Nat := [1, 1, 6, 1, 1, 1, 2, 4, 4]
def baseStart_726439 : Nat := 118140960795 + 726439 * 2 ^ 59
def prefixEnd_726439 : Nat := 4983230072969 + 3 ^ 40 * 726439 * 2
def baseEnd_726439 : Nat := 165783276965150461231855

theorem tailTrace_726439 : CollatzResearch.WordTrace tailWord_726439 prefixEnd_726439 165783276965150461231855 := by
  unfold tailWord_726439
  simp only [CollatzResearch.WordTrace]
  refine ⟨26495407015243043748918371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17663604676828695832612247 26495407015243043748918371)
  ·
    refine ⟨39743110522864565623377557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26495407015243043748918371 39743110522864565623377557)
    ·
      refine ⟨1862958305759276513595823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39743110522864565623377557 1862958305759276513595823)
      ·
        refine ⟨2794437458638914770393735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1862958305759276513595823 2794437458638914770393735)
        ·
          refine ⟨4191656187958372155590603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794437458638914770393735 4191656187958372155590603)
          ·
            refine ⟨6287484281937558233385905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4191656187958372155590603 6287484281937558233385905)
            ·
              refine ⟨4715613211453168675039429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6287484281937558233385905 4715613211453168675039429)
              ·
                refine ⟨884177477147469126569893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4715613211453168675039429 884177477147469126569893)
                ·
                  refine ⟨165783276965150461231855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 884177477147469126569893 165783276965150461231855)
                  ·
                    rfl

theorem cell21_726439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 4].length) (baseStart_726439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726439 prefixEnd_726439 := by exact prefixLift 726439
  have htrace : WordTrace (prefixWord ++ tailWord_726439) baseStart_726439 baseEnd_726439 := by
    simpa [prefixWord, tailWord_726439, baseEnd_726439] using wordTrace_append hprefix tailTrace_726439
  have hstable : (prefixWord ++ tailWord_726439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726439).length < 2 ^ (prefixWord ++ tailWord_726439).sum := by decide
  have hdescent : baseEnd_726439 < baseStart_726439 := by decide
  rcases family_descends (prefixWord ++ tailWord_726439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726453 : List Nat := [1, 3, 3, 2, 2, 1, 1, 8]
def baseStart_726453 : Nat := 118140960795 + 726453 * 2 ^ 59
def prefixEnd_726453 : Nat := 4983230072969 + 3 ^ 40 * 726453 * 2
def baseEnd_726453 : Nat := 55262157318629849332831

theorem tailTrace_726453 : CollatzResearch.WordTrace tailWord_726453 prefixEnd_726453 55262157318629849332831 := by
  unfold tailWord_726453
  simp only [CollatzResearch.WordTrace]
  refine ⟨26495917637192324139928013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17663945091461549426618675 26495917637192324139928013)
  ·
    refine ⟨9935969113947121552473005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26495917637192324139928013 9935969113947121552473005)
    ·
      refine ⟨3725988417730170582177377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9935969113947121552473005 3725988417730170582177377)
      ·
        refine ⟨2794491313297627936633033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3725988417730170582177377 2794491313297627936633033)
        ·
          refine ⟨2095868484973220952474775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2794491313297627936633033 2095868484973220952474775)
          ·
            refine ⟨3143802727459831428712163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2095868484973220952474775 3143802727459831428712163)
            ·
              refine ⟨4715704091189747143068245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3143802727459831428712163 4715704091189747143068245)
              ·
                refine ⟨55262157318629849332831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4715704091189747143068245 55262157318629849332831)
                ·
                  rfl

theorem cell21_726453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 8].length) (baseStart_726453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726453 prefixEnd_726453 := by exact prefixLift 726453
  have htrace : WordTrace (prefixWord ++ tailWord_726453) baseStart_726453 baseEnd_726453 := by
    simpa [prefixWord, tailWord_726453, baseEnd_726453] using wordTrace_append hprefix tailTrace_726453
  have hstable : (prefixWord ++ tailWord_726453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726453).length < 2 ^ (prefixWord ++ tailWord_726453).sum := by decide
  have hdescent : baseEnd_726453 < baseStart_726453 := by decide
  rcases family_descends (prefixWord ++ tailWord_726453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726467 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 5]
def baseStart_726467 : Nat := 118140960795 + 726467 * 2 ^ 59
def prefixEnd_726467 : Nat := 4983230072969 + 3 ^ 40 * 726467 * 2
def baseEnd_726467 : Nat := 165789666946628634765131

theorem tailTrace_726467 : CollatzResearch.WordTrace tailWord_726467 prefixEnd_726467 165789666946628634765131 := by
  unfold tailWord_726467
  simp only [CollatzResearch.WordTrace]
  refine ⟨26496428259141604530937655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17664285506094403020625103 26496428259141604530937655)
  ·
    refine ⟨39744642388712406796406483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26496428259141604530937655 39744642388712406796406483)
    ·
      refine ⟨59616963583068610194609725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39744642388712406796406483 59616963583068610194609725)
      ·
        refine ⟨22356361343650728822978647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59616963583068610194609725 22356361343650728822978647)
        ·
          refine ⟨33534542015476093234467971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22356361343650728822978647 33534542015476093234467971)
          ·
            refine ⟨50301813023214139851701957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33534542015476093234467971 50301813023214139851701957)
            ·
              refine ⟨9431589941852651222194117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50301813023214139851701957 9431589941852651222194117)
              ·
                refine ⟨1768423114097372104161397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9431589941852651222194117 1768423114097372104161397)
                ·
                  refine ⟨165789666946628634765131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1768423114097372104161397 165789666946628634765131)
                  ·
                    rfl

theorem cell21_726467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 5].length) (baseStart_726467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726467 prefixEnd_726467 := by exact prefixLift 726467
  have htrace : WordTrace (prefixWord ++ tailWord_726467) baseStart_726467 baseEnd_726467 := by
    simpa [prefixWord, tailWord_726467, baseEnd_726467] using wordTrace_append hprefix tailTrace_726467
  have hstable : (prefixWord ++ tailWord_726467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726467).length < 2 ^ (prefixWord ++ tailWord_726467).sum := by decide
  have hdescent : baseEnd_726467 < baseStart_726467 := by decide
  rcases family_descends (prefixWord ++ tailWord_726467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726560 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 5]
def baseStart_726560 : Nat := 118140960795 + 726560 * 2 ^ 59
def prefixEnd_726560 : Nat := 4983230072969 + 3 ^ 40 * 726560 * 2
def baseEnd_726560 : Nat := 165810890813681139714941

theorem tailTrace_726560 : CollatzResearch.WordTrace tailWord_726560 prefixEnd_726560 165810890813681139714941 := by
  unfold tailWord_726560
  simp only [CollatzResearch.WordTrace]
  refine ⟨13249910123902340707036567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17666546831869787609382089 13249910123902340707036567)
  ·
    refine ⟨19874865185853511060554851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13249910123902340707036567 19874865185853511060554851)
    ·
      refine ⟨29812297778780266590832277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19874865185853511060554851 29812297778780266590832277)
      ·
        refine ⟨1397451458380324996445263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29812297778780266590832277 1397451458380324996445263)
        ·
          refine ⟨2096177187570487494667895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1397451458380324996445263 2096177187570487494667895)
          ·
            refine ⟨3144265781355731242001843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2096177187570487494667895 3144265781355731242001843)
            ·
              refine ⟨4716398672033596863002765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3144265781355731242001843 4716398672033596863002765)
              ·
                refine ⟨1768649502012598823626037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4716398672033596863002765 1768649502012598823626037)
                ·
                  refine ⟨165810890813681139714941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1768649502012598823626037 165810890813681139714941)
                  ·
                    rfl

theorem cell21_726560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_726560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726560 prefixEnd_726560 := by exact prefixLift 726560
  have htrace : WordTrace (prefixWord ++ tailWord_726560) baseStart_726560 baseEnd_726560 := by
    simpa [prefixWord, tailWord_726560, baseEnd_726560] using wordTrace_append hprefix tailTrace_726560
  have hstable : (prefixWord ++ tailWord_726560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726560).length < 2 ^ (prefixWord ++ tailWord_726560).sum := by decide
  have hdescent : baseEnd_726560 < baseStart_726560 := by decide
  rcases family_descends (prefixWord ++ tailWord_726560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726670 : List Nat := [4, 1, 1, 3, 1, 2, 4, 2, 3]
def baseStart_726670 : Nat := 118140960795 + 726670 * 2 ^ 59
def prefixEnd_726670 : Nat := 4983230072969 + 3 ^ 40 * 726670 * 2
def baseEnd_726670 : Nat := 165835994312345392881383

theorem tailTrace_726670 : CollatzResearch.WordTrace tailWord_726670 prefixEnd_726670 165835994312345392881383 := by
  unfold tailWord_726670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3312979034675771275072183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17669221518270780133718309 3312979034675771275072183)
  ·
    refine ⟨4969468552013656912608275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3312979034675771275072183 4969468552013656912608275)
    ·
      refine ⟨7454202828020485368912413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4969468552013656912608275 7454202828020485368912413)
      ·
        refine ⟨2795326060507682013342155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7454202828020485368912413 2795326060507682013342155)
        ·
          refine ⟨4192989090761523020013233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2795326060507682013342155 4192989090761523020013233)
          ·
            refine ⟨3144741818071142265009925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4192989090761523020013233 3144741818071142265009925)
            ·
              refine ⟨589639090888339174689361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3144741818071142265009925 589639090888339174689361)
              ·
                refine ⟨442229318166254381017021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589639090888339174689361 442229318166254381017021)
                ·
                  refine ⟨165835994312345392881383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 442229318166254381017021 165835994312345392881383)
                  ·
                    rfl

theorem cell21_726670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_726670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726670 prefixEnd_726670 := by exact prefixLift 726670
  have htrace : WordTrace (prefixWord ++ tailWord_726670) baseStart_726670 baseEnd_726670 := by
    simpa [prefixWord, tailWord_726670, baseEnd_726670] using wordTrace_append hprefix tailTrace_726670
  have hstable : (prefixWord ++ tailWord_726670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726670).length < 2 ^ (prefixWord ++ tailWord_726670).sum := by decide
  have hdescent : baseEnd_726670 < baseStart_726670 := by decide
  rcases family_descends (prefixWord ++ tailWord_726670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726743 : List Nat := [1, 1, 3, 2, 1, 3, 5, 1, 4]
def baseStart_726743 : Nat := 118140960795 + 726743 * 2 ^ 59
def prefixEnd_726743 : Nat := 4983230072969 + 3 ^ 40 * 726743 * 2
def baseEnd_726743 : Nat := 165852653906913488164567

theorem tailTrace_726743 : CollatzResearch.WordTrace tailWord_726743 prefixEnd_726743 165852653906913488164567 := by
  unfold tailWord_726743
  simp only [CollatzResearch.WordTrace]
  refine ⟨26506494806141703667984883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17670996537427802445323255 26506494806141703667984883)
  ·
    refine ⟨39759742209212555501977325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26506494806141703667984883 39759742209212555501977325)
    ·
      refine ⟨14909903328454708313241497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39759742209212555501977325 14909903328454708313241497)
      ·
        refine ⟨11182427496341031234931123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14909903328454708313241497 11182427496341031234931123)
        ·
          refine ⟨16773641244511546852396685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11182427496341031234931123 16773641244511546852396685)
          ·
            refine ⟨6290115466691830069648757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16773641244511546852396685 6290115466691830069648757)
            ·
              refine ⟨589698325002359069029571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6290115466691830069648757 589698325002359069029571)
              ·
                refine ⟨884547487503538603544357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589698325002359069029571 884547487503538603544357)
                ·
                  refine ⟨165852653906913488164567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 884547487503538603544357 165852653906913488164567)
                  ·
                    rfl

theorem cell21_726743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 4].length) (baseStart_726743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726743 prefixEnd_726743 := by exact prefixLift 726743
  have htrace : WordTrace (prefixWord ++ tailWord_726743) baseStart_726743 baseEnd_726743 := by
    simpa [prefixWord, tailWord_726743, baseEnd_726743] using wordTrace_append hprefix tailTrace_726743
  have hstable : (prefixWord ++ tailWord_726743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726743).length < 2 ^ (prefixWord ++ tailWord_726743).sum := by decide
  have hdescent : baseEnd_726743 < baseStart_726743 := by decide
  rcases family_descends (prefixWord ++ tailWord_726743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726788 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 5]
def baseStart_726788 : Nat := 118140960795 + 726788 * 2 ^ 59
def prefixEnd_726788 : Nat := 4983230072969 + 3 ^ 40 * 726788 * 2
def baseEnd_726788 : Nat := 165862923520003409914475

theorem tailTrace_726788 : CollatzResearch.WordTrace tailWord_726788 prefixEnd_726788 165862923520003409914475 := by
  unfold tailWord_726788
  simp only [CollatzResearch.WordTrace]
  refine ⟨13254068045489338176686509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17672090727319117568915345 13254068045489338176686509)
  ·
    refine ⟨4970275517058501816257441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13254068045489338176686509 4970275517058501816257441)
    ·
      refine ⟨3727706637793876362193081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4970275517058501816257441 3727706637793876362193081)
      ·
        refine ⟨2795779978345407271644811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3727706637793876362193081 2795779978345407271644811)
        ·
          refine ⟨4193669967518110907467217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2795779978345407271644811 4193669967518110907467217)
          ·
            refine ⟨3145252475638583180600413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4193669967518110907467217 3145252475638583180600413)
            ·
              refine ⟨1179469678364468692725155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3145252475638583180600413 1179469678364468692725155)
              ·
                refine ⟨1769204517546703039087733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179469678364468692725155 1769204517546703039087733)
                ·
                  refine ⟨165862923520003409914475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1769204517546703039087733 165862923520003409914475)
                  ·
                    rfl

theorem cell21_726788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_726788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726788 prefixEnd_726788 := by exact prefixLift 726788
  have htrace : WordTrace (prefixWord ++ tailWord_726788) baseStart_726788 baseEnd_726788 := by
    simpa [prefixWord, tailWord_726788, baseEnd_726788] using wordTrace_append hprefix tailTrace_726788
  have hstable : (prefixWord ++ tailWord_726788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726788).length < 2 ^ (prefixWord ++ tailWord_726788).sum := by decide
  have hdescent : baseEnd_726788 < baseStart_726788 := by decide
  rcases family_descends (prefixWord ++ tailWord_726788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726816 : List Nat := [2, 1, 1, 5, 1, 1, 1, 9]
def baseStart_726816 : Nat := 118140960795 + 726816 * 2 ^ 59
def prefixEnd_726816 : Nat := 4983230072969 + 3 ^ 40 * 726816 * 2
def baseEnd_726816 : Nat := 55289771167160527815917

theorem tailTrace_726816 : CollatzResearch.WordTrace tailWord_726816 prefixEnd_726816 55289771167160527815917 := by
  unfold tailWord_726816
  simp only [CollatzResearch.WordTrace]
  refine ⟨13254578667438618567696151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17672771556584824756928201 13254578667438618567696151)
  ·
    refine ⟨19881868001157927851544227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13254578667438618567696151 19881868001157927851544227)
    ·
      refine ⟨29822802001736891777316341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19881868001157927851544227 29822802001736891777316341)
      ·
        refine ⟨2795887687662833604123407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29822802001736891777316341 2795887687662833604123407)
        ·
          refine ⟨4193831531494250406185111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2795887687662833604123407 4193831531494250406185111)
          ·
            refine ⟨6290747297241375609277667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4193831531494250406185111 6290747297241375609277667)
            ·
              refine ⟨9436120945862063413916501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6290747297241375609277667 9436120945862063413916501)
              ·
                refine ⟨55289771167160527815917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9436120945862063413916501 55289771167160527815917)
                ·
                  rfl

theorem cell21_726816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 9].length) (baseStart_726816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726816 prefixEnd_726816 := by exact prefixLift 726816
  have htrace : WordTrace (prefixWord ++ tailWord_726816) baseStart_726816 baseEnd_726816 := by
    simpa [prefixWord, tailWord_726816, baseEnd_726816] using wordTrace_append hprefix tailTrace_726816
  have hstable : (prefixWord ++ tailWord_726816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726816).length < 2 ^ (prefixWord ++ tailWord_726816).sum := by decide
  have hdescent : baseEnd_726816 < baseStart_726816 := by decide
  rcases family_descends (prefixWord ++ tailWord_726816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726836 : List Nat := [2, 5, 1, 1, 2, 2, 2, 2, 4]
def baseStart_726836 : Nat := 118140960795 + 726836 * 2 ^ 59
def prefixEnd_726836 : Nat := 4983230072969 + 3 ^ 40 * 726836 * 2
def baseEnd_726836 : Nat := 165873877773965993114377

theorem tailTrace_726836 : CollatzResearch.WordTrace tailWord_726836 prefixEnd_726836 165873877773965993114377 := by
  unfold tailWord_726836
  simp only [CollatzResearch.WordTrace]
  refine ⟨13254943397402390275560181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17673257863203187034080241 13254943397402390275560181)
  ·
    refine ⟨1242650943506474088333767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13254943397402390275560181 1242650943506474088333767)
    ·
      refine ⟨1863976415259711132500651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1242650943506474088333767 1863976415259711132500651)
      ·
        refine ⟨2795964622889566698750977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1863976415259711132500651 2795964622889566698750977)
        ·
          refine ⟨2096973467167175024063233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2795964622889566698750977 2096973467167175024063233)
          ·
            refine ⟨1572730100375381268047425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2096973467167175024063233 1572730100375381268047425)
            ·
              refine ⟨1179547575281535951035569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1572730100375381268047425 1179547575281535951035569)
              ·
                refine ⟨884660681461151963276677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1179547575281535951035569 884660681461151963276677)
                ·
                  refine ⟨165873877773965993114377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 884660681461151963276677 165873877773965993114377)
                  ·
                    rfl

theorem cell21_726836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_726836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726836 prefixEnd_726836 := by exact prefixLift 726836
  have htrace : WordTrace (prefixWord ++ tailWord_726836) baseStart_726836 baseEnd_726836 := by
    simpa [prefixWord, tailWord_726836, baseEnd_726836] using wordTrace_append hprefix tailTrace_726836
  have hstable : (prefixWord ++ tailWord_726836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726836).length < 2 ^ (prefixWord ++ tailWord_726836).sum := by decide
  have hdescent : baseEnd_726836 < baseStart_726836 := by decide
  rcases family_descends (prefixWord ++ tailWord_726836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726892 : List Nat := [2, 2, 1, 1, 4, 3, 8]
def baseStart_726892 : Nat := 118140960795 + 726892 * 2 ^ 59
def prefixEnd_726892 : Nat := 4983230072969 + 3 ^ 40 * 726892 * 2
def baseEnd_726892 : Nat := 18431850859658037797881

theorem tailTrace_726892 : CollatzResearch.WordTrace tailWord_726892 prefixEnd_726892 18431850859658037797881 := by
  unfold tailWord_726892
  simp only [CollatzResearch.WordTrace]
  refine ⟨13255964641300951057579465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17674619521734601410105953 13255964641300951057579465)
  ·
    refine ⟨9941973480975713293184599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13255964641300951057579465 9941973480975713293184599)
    ·
      refine ⟨14912960221463569939776899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9941973480975713293184599 14912960221463569939776899)
      ·
        refine ⟨22369440332195354909665349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14912960221463569939776899 22369440332195354909665349)
        ·
          refine ⟨4194270062286629045562253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22369440332195354909665349 4194270062286629045562253)
          ·
            refine ⟨1572851273357485892085845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4194270062286629045562253 1572851273357485892085845)
            ·
              refine ⟨18431850859658037797881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1572851273357485892085845 18431850859658037797881)
              ·
                rfl

theorem cell21_726892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 8].length) (baseStart_726892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726892 prefixEnd_726892 := by exact prefixLift 726892
  have htrace : WordTrace (prefixWord ++ tailWord_726892) baseStart_726892 baseEnd_726892 := by
    simpa [prefixWord, tailWord_726892, baseEnd_726892] using wordTrace_append hprefix tailTrace_726892
  have hstable : (prefixWord ++ tailWord_726892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726892).length < 2 ^ (prefixWord ++ tailWord_726892).sum := by decide
  have hdescent : baseEnd_726892 < baseStart_726892 := by decide
  rcases family_descends (prefixWord ++ tailWord_726892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726926 : List Nat := [4, 1, 1, 5, 1, 1, 1, 7]
def baseStart_726926 : Nat := 118140960795 + 726926 * 2 ^ 59
def prefixEnd_726926 : Nat := 4983230072969 + 3 ^ 40 * 726926 * 2
def baseEnd_726926 : Nat := 55298139000048612204731

theorem tailTrace_726926 : CollatzResearch.WordTrace tailWord_726926 prefixEnd_726926 55298139000048612204731 := by
  unfold tailWord_726926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3314146170559840740237079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17675446242985817281264421 3314146170559840740237079)
  ·
    refine ⟨4971219255839761110355619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3314146170559840740237079 4971219255839761110355619)
    ·
      refine ⟨7456828883759641665533429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4971219255839761110355619 7456828883759641665533429)
      ·
        refine ⟨699077707852466406143759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7456828883759641665533429 699077707852466406143759)
        ·
          refine ⟨1048616561778699609215639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699077707852466406143759 1048616561778699609215639)
          ·
            refine ⟨1572924842668049413823459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048616561778699609215639 1572924842668049413823459)
            ·
              refine ⟨2359387264002074120735189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1572924842668049413823459 2359387264002074120735189)
              ·
                refine ⟨55298139000048612204731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2359387264002074120735189 55298139000048612204731)
                ·
                  rfl

theorem cell21_726926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_726926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726926 prefixEnd_726926 := by exact prefixLift 726926
  have htrace : WordTrace (prefixWord ++ tailWord_726926) baseStart_726926 baseEnd_726926 := by
    simpa [prefixWord, tailWord_726926, baseEnd_726926] using wordTrace_append hprefix tailTrace_726926
  have hstable : (prefixWord ++ tailWord_726926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726926).length < 2 ^ (prefixWord ++ tailWord_726926).sum := by decide
  have hdescent : baseEnd_726926 < baseStart_726926 := by decide
  rcases family_descends (prefixWord ++ tailWord_726926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726937 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 6]
def baseStart_726937 : Nat := 118140960795 + 726937 * 2 ^ 59
def prefixEnd_726937 : Nat := 4983230072969 + 3 ^ 40 * 726937 * 2
def baseEnd_726937 : Nat := 165896927350012261930837

theorem tailTrace_726937 : CollatzResearch.WordTrace tailWord_726937 prefixEnd_726937 165896927350012261930837 := by
  unfold tailWord_726937
  simp only [CollatzResearch.WordTrace]
  refine ⟨26513570567438874800547065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17675713711625916533698043 26513570567438874800547065)
  ·
    refine ⟨19885177925579156100410299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26513570567438874800547065 19885177925579156100410299)
    ·
      refine ⟨29827766888368734150615449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19885177925579156100410299 29827766888368734150615449)
      ·
        refine ⟨22370825166276550612961587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29827766888368734150615449 22370825166276550612961587)
        ·
          refine ⟨33556237749414825919442381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22370825166276550612961587 33556237749414825919442381)
          ·
            refine ⟨12583589156030559719790893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33556237749414825919442381 12583589156030559719790893)
            ·
              refine ⟨4718845933511459894921585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12583589156030559719790893 4718845933511459894921585)
              ·
                refine ⟨3539134450133594921191189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4718845933511459894921585 3539134450133594921191189)
                ·
                  refine ⟨165896927350012261930837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3539134450133594921191189 165896927350012261930837)
                  ·
                    rfl

theorem cell21_726937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_726937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726937 prefixEnd_726937 := by exact prefixLift 726937
  have htrace : WordTrace (prefixWord ++ tailWord_726937) baseStart_726937 baseEnd_726937 := by
    simpa [prefixWord, tailWord_726937, baseEnd_726937] using wordTrace_append hprefix tailTrace_726937
  have hstable : (prefixWord ++ tailWord_726937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726937).length < 2 ^ (prefixWord ++ tailWord_726937).sum := by decide
  have hdescent : baseEnd_726937 < baseStart_726937 := by decide
  rcases family_descends (prefixWord ++ tailWord_726937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726968 : List Nat := [2, 1, 2, 1, 2, 3, 4, 6]
def baseStart_726968 : Nat := 118140960795 + 726968 * 2 ^ 59
def prefixEnd_726968 : Nat := 4983230072969 + 3 ^ 40 * 726968 * 2
def baseEnd_726968 : Nat := 55301333990787698971369

theorem tailTrace_726968 : CollatzResearch.WordTrace tailWord_726968 prefixEnd_726968 55301333990787698971369 := by
  unfold tailWord_726968
  simp only [CollatzResearch.WordTrace]
  refine ⟨13257350615163283547462779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17676467486884378063283705 13257350615163283547462779)
  ·
    refine ⟨19886025922744925321194169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13257350615163283547462779 19886025922744925321194169)
    ·
      refine ⟨14914519442058693990895627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19886025922744925321194169 14914519442058693990895627)
      ·
        refine ⟨22371779163088040986343441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14914519442058693990895627 22371779163088040986343441)
        ·
          refine ⟨16778834372316030739757581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22371779163088040986343441 16778834372316030739757581)
          ·
            refine ⟨6292062889618511527409093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16778834372316030739757581 6292062889618511527409093)
            ·
              refine ⟨1179761791803470911389205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6292062889618511527409093 1179761791803470911389205)
              ·
                refine ⟨55301333990787698971369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1179761791803470911389205 55301333990787698971369)
                ·
                  rfl

theorem cell21_726968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 6].length) (baseStart_726968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_726968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_726968 prefixEnd_726968 := by exact prefixLift 726968
  have htrace : WordTrace (prefixWord ++ tailWord_726968) baseStart_726968 baseEnd_726968 := by
    simpa [prefixWord, tailWord_726968, baseEnd_726968] using wordTrace_append hprefix tailTrace_726968
  have hstable : (prefixWord ++ tailWord_726968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726968).length < 2 ^ (prefixWord ++ tailWord_726968).sum := by decide
  have hdescent : baseEnd_726968 < baseStart_726968 := by decide
  rcases family_descends (prefixWord ++ tailWord_726968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727075 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 5]
def baseStart_727075 : Nat := 118140960795 + 727075 * 2 ^ 59
def prefixEnd_727075 : Nat := 4983230072969 + 3 ^ 40 * 727075 * 2
def baseEnd_727075 : Nat := 165928420830154688630555

theorem tailTrace_727075 : CollatzResearch.WordTrace tailWord_727075 prefixEnd_727075 165928420830154688630555 := by
  unfold tailWord_727075
  simp only [CollatzResearch.WordTrace]
  refine ⟨26518603840938924369070679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17679069227292616246047119 26518603840938924369070679)
  ·
    refine ⟨39777905761408386553606019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26518603840938924369070679 39777905761408386553606019)
    ·
      refine ⟨59666858642112579830409029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39777905761408386553606019 59666858642112579830409029)
      ·
        refine ⟨11187535995396108718201693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59666858642112579830409029 11187535995396108718201693)
        ·
          refine ⟨4195325998273540769325635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11187535995396108718201693 4195325998273540769325635)
          ·
            refine ⟨6292988997410311153988453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4195325998273540769325635 6292988997410311153988453)
            ·
              refine ⟨1179935437014433341372835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6292988997410311153988453 1179935437014433341372835)
              ·
                refine ⟨1769903155521650012059253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179935437014433341372835 1769903155521650012059253)
                ·
                  refine ⟨165928420830154688630555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1769903155521650012059253 165928420830154688630555)
                  ·
                    rfl

theorem cell21_727075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 5].length) (baseStart_727075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727075 prefixEnd_727075 := by exact prefixLift 727075
  have htrace : WordTrace (prefixWord ++ tailWord_727075) baseStart_727075 baseEnd_727075 := by
    simpa [prefixWord, tailWord_727075, baseEnd_727075] using wordTrace_append hprefix tailTrace_727075
  have hstable : (prefixWord ++ tailWord_727075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727075).length < 2 ^ (prefixWord ++ tailWord_727075).sum := by decide
  have hdescent : baseEnd_727075 < baseStart_727075 := by decide
  rcases family_descends (prefixWord ++ tailWord_727075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727126 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_727126 : Nat := 118140960795 + 727126 * 2 ^ 59
def prefixEnd_727126 : Nat := 4983230072969 + 3 ^ 40 * 727126 * 2
def baseEnd_727126 : Nat := 165940059724989933280451

theorem tailTrace_727126 : CollatzResearch.WordTrace tailWord_727126 prefixEnd_727126 165940059724989933280451 := by
  unfold tailWord_727126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1657528997734635004948577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17680309309169440052784821 1657528997734635004948577)
  ·
    refine ⟨1243146748300976253711433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1657528997734635004948577 1243146748300976253711433)
    ·
      refine ⟨932360061225732190283575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1243146748300976253711433 932360061225732190283575)
      ·
        refine ⟨1398540091838598285425363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932360061225732190283575 1398540091838598285425363)
        ·
          refine ⟨2097810137757897428138045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1398540091838598285425363 2097810137757897428138045)
          ·
            refine ⟨786678801659211535551767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2097810137757897428138045 786678801659211535551767)
            ·
              refine ⟨1180018202488817303327651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786678801659211535551767 1180018202488817303327651)
              ·
                refine ⟨1770027303733225954991477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1180018202488817303327651 1770027303733225954991477)
                ·
                  refine ⟨165940059724989933280451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1770027303733225954991477 165940059724989933280451)
                  ·
                    rfl

theorem cell21_727126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_727126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727126 prefixEnd_727126 := by exact prefixLift 727126
  have htrace : WordTrace (prefixWord ++ tailWord_727126) baseStart_727126 baseEnd_727126 := by
    simpa [prefixWord, tailWord_727126, baseEnd_727126] using wordTrace_append hprefix tailTrace_727126
  have hstable : (prefixWord ++ tailWord_727126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727126).length < 2 ^ (prefixWord ++ tailWord_727126).sum := by decide
  have hdescent : baseEnd_727126 < baseStart_727126 := by decide
  rcases family_descends (prefixWord ++ tailWord_727126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727233 : List Nat := [1, 2, 6, 1, 3, 1, 1, 2, 4]
def baseStart_727233 : Nat := 118140960795 + 727233 * 2 ^ 59
def prefixEnd_727233 : Nat := 4983230072969 + 3 ^ 40 * 727233 * 2
def baseEnd_727233 : Nat := 165964478582781524996899

theorem tailTrace_727233 : CollatzResearch.WordTrace tailWord_727233 prefixEnd_727233 165964478582781524996899 := by
  unfold tailWord_727233
  simp only [CollatzResearch.WordTrace]
  refine ⟨26524366574366517353322353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17682911049577678235548235 26524366574366517353322353)
  ·
    refine ⟨19893274930774888014991765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26524366574366517353322353 19893274930774888014991765)
    ·
      refine ⟨932497262380072875702739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19893274930774888014991765 932497262380072875702739)
      ·
        refine ⟨1398745893570109313554109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932497262380072875702739 1398745893570109313554109)
        ·
          refine ⟨524529710088790992582791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1398745893570109313554109 524529710088790992582791)
          ·
            refine ⟨786794565133186488874187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524529710088790992582791 786794565133186488874187)
            ·
              refine ⟨1180191847699779733311281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786794565133186488874187 1180191847699779733311281)
              ·
                refine ⟨885143885774834799983461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180191847699779733311281 885143885774834799983461)
                ·
                  refine ⟨165964478582781524996899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 885143885774834799983461 165964478582781524996899)
                  ·
                    rfl

theorem cell21_727233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 4].length) (baseStart_727233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727233 prefixEnd_727233 := by exact prefixLift 727233
  have htrace : WordTrace (prefixWord ++ tailWord_727233) baseStart_727233 baseEnd_727233 := by
    simpa [prefixWord, tailWord_727233, baseEnd_727233] using wordTrace_append hprefix tailTrace_727233
  have hstable : (prefixWord ++ tailWord_727233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727233).length < 2 ^ (prefixWord ++ tailWord_727233).sum := by decide
  have hdescent : baseEnd_727233 < baseStart_727233 := by decide
  rcases family_descends (prefixWord ++ tailWord_727233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727241 : List Nat := [1, 2, 1, 1, 2, 1, 1, 8, 4]
def baseStart_727241 : Nat := 118140960795 + 727241 * 2 ^ 59
def prefixEnd_727241 : Nat := 4983230072969 + 3 ^ 40 * 727241 * 2
def baseEnd_727241 : Nat := 165966304291775288863549

theorem tailTrace_727241 : CollatzResearch.WordTrace tailWord_727241 prefixEnd_727241 165966304291775288863549 := by
  unfold tailWord_727241
  simp only [CollatzResearch.WordTrace]
  refine ⟨26524658358337534719613577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17683105572225023146409051 26524658358337534719613577)
  ·
    refine ⟨19893493768753151039710183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26524658358337534719613577 19893493768753151039710183)
    ·
      refine ⟨29840240653129726559565275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19893493768753151039710183 29840240653129726559565275)
      ·
        refine ⟨44760360979694589839347913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29840240653129726559565275 44760360979694589839347913)
        ·
          refine ⟨33570270734770942379510935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44760360979694589839347913 33570270734770942379510935)
          ·
            refine ⟨50355406102156413569266403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33570270734770942379510935 50355406102156413569266403)
            ·
              refine ⟨75533109153234620353899605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50355406102156413569266403 75533109153234620353899605)
              ·
                refine ⟨885153622889468207272261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 75533109153234620353899605 885153622889468207272261)
                ·
                  refine ⟨165966304291775288863549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 885153622889468207272261 165966304291775288863549)
                  ·
                    rfl

theorem cell21_727241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_727241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727241 prefixEnd_727241 := by exact prefixLift 727241
  have htrace : WordTrace (prefixWord ++ tailWord_727241) baseStart_727241 baseEnd_727241 := by
    simpa [prefixWord, tailWord_727241, baseEnd_727241] using wordTrace_append hprefix tailTrace_727241
  have hstable : (prefixWord ++ tailWord_727241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727241).length < 2 ^ (prefixWord ++ tailWord_727241).sum := by decide
  have hdescent : baseEnd_727241 < baseStart_727241 := by decide
  rcases family_descends (prefixWord ++ tailWord_727241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727255 : List Nat := [1, 1, 3, 2, 1, 2, 1, 10]
def baseStart_727255 : Nat := 118140960795 + 727255 * 2 ^ 59
def prefixEnd_727255 : Nat := 4983230072969 + 3 ^ 40 * 727255 * 2
def baseEnd_727255 : Nat := 55323166427504791876729

theorem tailTrace_727255 : CollatzResearch.WordTrace tailWord_727255 prefixEnd_727255 55323166427504791876729 := by
  unfold tailWord_727255
  simp only [CollatzResearch.WordTrace]
  refine ⟨26525168980286815110623219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17683445986857876740415479 26525168980286815110623219)
  ·
    refine ⟨39787753470430222665934829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26525168980286815110623219 39787753470430222665934829)
    ·
      refine ⟨14920407551411333499725561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39787753470430222665934829 14920407551411333499725561)
      ·
        refine ⟨11190305663558500124794171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14920407551411333499725561 11190305663558500124794171)
        ·
          refine ⟨16785458495337750187191257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11190305663558500124794171 16785458495337750187191257)
          ·
            refine ⟨12589093871503312640393443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16785458495337750187191257 12589093871503312640393443)
            ·
              refine ⟨18883640807254968960590165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12589093871503312640393443 18883640807254968960590165)
              ·
                refine ⟨55323166427504791876729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18883640807254968960590165 55323166427504791876729)
                ·
                  rfl

theorem cell21_727255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 10].length) (baseStart_727255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727255 prefixEnd_727255 := by exact prefixLift 727255
  have htrace : WordTrace (prefixWord ++ tailWord_727255) baseStart_727255 baseEnd_727255 := by
    simpa [prefixWord, tailWord_727255, baseEnd_727255] using wordTrace_append hprefix tailTrace_727255
  have hstable : (prefixWord ++ tailWord_727255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727255).length < 2 ^ (prefixWord ++ tailWord_727255).sum := by decide
  have hdescent : baseEnd_727255 < baseStart_727255 := by decide
  rcases family_descends (prefixWord ++ tailWord_727255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727272 : List Nat := [2, 1, 4, 1, 2, 3, 1, 7]
def baseStart_727272 : Nat := 118140960795 + 727272 * 2 ^ 59
def prefixEnd_727272 : Nat := 4983230072969 + 3 ^ 40 * 727272 * 2
def baseEnd_727272 : Nat := 55324459638042041282273

theorem tailTrace_727272 : CollatzResearch.WordTrace tailWord_727272 prefixEnd_727272 55324459638042041282273 := by
  unfold tailWord_727272
  simp only [CollatzResearch.WordTrace]
  refine ⟨13262894510612613506996035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17683859347483484675994713 13262894510612613506996035)
  ·
    refine ⟨19894341765918920260494053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13262894510612613506996035 19894341765918920260494053)
    ·
      refine ⟨3730189081109797548842635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19894341765918920260494053 3730189081109797548842635)
      ·
        refine ⟨5595283621664696323263953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3730189081109797548842635 5595283621664696323263953)
        ·
          refine ⟨4196462716248522242447965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5595283621664696323263953 4196462716248522242447965)
          ·
            refine ⟨1573673518593195840917987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4196462716248522242447965 1573673518593195840917987)
            ·
              refine ⟨2360510277889793761376981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1573673518593195840917987 2360510277889793761376981)
              ·
                refine ⟨55324459638042041282273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2360510277889793761376981 55324459638042041282273)
                ·
                  rfl

theorem cell21_727272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 7].length) (baseStart_727272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727272 prefixEnd_727272 := by exact prefixLift 727272
  have htrace : WordTrace (prefixWord ++ tailWord_727272) baseStart_727272 baseEnd_727272 := by
    simpa [prefixWord, tailWord_727272, baseEnd_727272] using wordTrace_append hprefix tailTrace_727272
  have hstable : (prefixWord ++ tailWord_727272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727272).length < 2 ^ (prefixWord ++ tailWord_727272).sum := by decide
  have hdescent : baseEnd_727272 < baseStart_727272 := by decide
  rcases family_descends (prefixWord ++ tailWord_727272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727331 : List Nat := [1, 1, 1, 4, 2, 2, 1, 9]
def baseStart_727331 : Nat := 118140960795 + 727331 * 2 ^ 59
def prefixEnd_727331 : Nat := 4983230072969 + 3 ^ 40 * 727331 * 2
def baseEnd_727331 : Nat := 55328947839318377454455

theorem tailTrace_727331 : CollatzResearch.WordTrace tailWord_727331 prefixEnd_727331 55328947839318377454455 := by
  unfold tailWord_727331
  simp only [CollatzResearch.WordTrace]
  refine ⟨26527940928011480090389847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17685293952007653393593231 26527940928011480090389847)
  ·
    refine ⟨39791911392017220135584771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26527940928011480090389847 39791911392017220135584771)
    ·
      refine ⟨59687867088025830203377157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39791911392017220135584771 59687867088025830203377157)
      ·
        refine ⟨11191475079004843163133217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59687867088025830203377157 11191475079004843163133217)
        ·
          refine ⟨8393606309253632372349913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11191475079004843163133217 8393606309253632372349913)
          ·
            refine ⟨6295204731940224279262435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8393606309253632372349913 6295204731940224279262435)
            ·
              refine ⟨9442807097910336418893653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6295204731940224279262435 9442807097910336418893653)
              ·
                refine ⟨55328947839318377454455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9442807097910336418893653 55328947839318377454455)
                ·
                  rfl

theorem cell21_727331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 9].length) (baseStart_727331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_727331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_727331 prefixEnd_727331 := by exact prefixLift 727331
  have htrace : WordTrace (prefixWord ++ tailWord_727331) baseStart_727331 baseEnd_727331 := by
    simpa [prefixWord, tailWord_727331, baseEnd_727331] using wordTrace_append hprefix tailTrace_727331
  have hstable : (prefixWord ++ tailWord_727331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727331).length < 2 ^ (prefixWord ++ tailWord_727331).sum := by decide
  have hdescent : baseEnd_727331 < baseStart_727331 := by decide
  rcases family_descends (prefixWord ++ tailWord_727331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
