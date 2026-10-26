import V185TrunkScan21Chunk135

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1657746 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 5]
def baseStart_1657746 : Nat := 118140960795 + 1657746 * 2 ^ 59
def prefixEnd_1657746 : Nat := 4983230072969 + 3 ^ 40 * 1657746 * 2
def baseEnd_1657746 : Nat := 378320222697056131044965

theorem tailTrace_1657746 : CollatzResearch.WordTrace tailWord_1657746 prefixEnd_1657746 378320222697056131044965 := by
  unfold tailWord_1657746
  simp only [CollatzResearch.WordTrace]
  refine ⟨15115740963069209330384273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40308642568184558214358061 15115740963069209330384273)
  ·
    refine ⟨11336805722301906997788205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15115740963069209330384273 11336805722301906997788205)
    ·
      refine ⟨4251302145863215124170577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11336805722301906997788205 4251302145863215124170577)
      ·
        refine ⟨3188476609397411343127933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4251302145863215124170577 3188476609397411343127933)
        ·
          refine ⟨1195678728524029253672975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3188476609397411343127933 1195678728524029253672975)
          ·
            refine ⟨1793518092786043880509463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195678728524029253672975 1793518092786043880509463)
            ·
              refine ⟨2690277139179065820764195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793518092786043880509463 2690277139179065820764195)
              ·
                refine ⟨4035415708768598731146293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2690277139179065820764195 4035415708768598731146293)
                ·
                  refine ⟨378320222697056131044965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4035415708768598731146293 378320222697056131044965)
                  ·
                    rfl

theorem cell21_1657746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_1657746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657746 prefixEnd_1657746 := by exact prefixLift 1657746
  have htrace : WordTrace (prefixWord ++ tailWord_1657746) baseStart_1657746 baseEnd_1657746 := by
    simpa [prefixWord, tailWord_1657746, baseEnd_1657746] using wordTrace_append hprefix tailTrace_1657746
  have hstable : (prefixWord ++ tailWord_1657746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657746).length < 2 ^ (prefixWord ++ tailWord_1657746).sum := by decide
  have hdescent : baseEnd_1657746 < baseStart_1657746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657816 : List Nat := [2, 1, 2, 2, 2, 3, 3, 6]
def baseStart_1657816 : Nat := 118140960795 + 1657816 * 2 ^ 59
def prefixEnd_1657816 : Nat := 4983230072969 + 3 ^ 40 * 1657816 * 2
def baseEnd_1657816 : Nat := 126112065883583854959385

theorem tailTrace_1657816 : CollatzResearch.WordTrace tailWord_1657816 prefixEnd_1657816 126112065883583854959385 := by
  unfold tailWord_1657816
  simp only [CollatzResearch.WordTrace]
  refine ⟨30232758481011619638292651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40310344641348826184390201 30232758481011619638292651)
  ·
    refine ⟨45349137721517429457438977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30232758481011619638292651 45349137721517429457438977)
    ·
      refine ⟨34011853291138072093079233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45349137721517429457438977 34011853291138072093079233)
      ·
        refine ⟨25508889968353554069809425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34011853291138072093079233 25508889968353554069809425)
        ·
          refine ⟨19131667476265165552357069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25508889968353554069809425 19131667476265165552357069)
          ·
            refine ⟨7174375303599437082133901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19131667476265165552357069 7174375303599437082133901)
            ·
              refine ⟨2690390738849788905800213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7174375303599437082133901 2690390738849788905800213)
              ·
                refine ⟨126112065883583854959385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2690390738849788905800213 126112065883583854959385)
                ·
                  rfl

theorem cell21_1657816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 6].length) (baseStart_1657816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657816 prefixEnd_1657816 := by exact prefixLift 1657816
  have htrace : WordTrace (prefixWord ++ tailWord_1657816) baseStart_1657816 baseEnd_1657816 := by
    simpa [prefixWord, tailWord_1657816, baseEnd_1657816] using wordTrace_append hprefix tailTrace_1657816
  have hstable : (prefixWord ++ tailWord_1657816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657816).length < 2 ^ (prefixWord ++ tailWord_1657816).sum := by decide
  have hdescent : baseEnd_1657816 < baseStart_1657816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657861 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 6]
def baseStart_1657861 : Nat := 118140960795 + 1657861 * 2 ^ 59
def prefixEnd_1657861 : Nat := 4983230072969 + 3 ^ 40 * 1657861 * 2
def baseEnd_1657861 : Nat := 378346467263841486628063

theorem tailTrace_1657861 : CollatzResearch.WordTrace tailWord_1657861 prefixEnd_1657861 378346467263841486628063 := by
  unfold tailWord_1657861
  simp only [CollatzResearch.WordTrace]
  refine ⟨60467158246860211961973437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40311438831240141307982291 60467158246860211961973437)
  ·
    refine ⟨22675184342572579485740039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60467158246860211961973437 22675184342572579485740039)
    ·
      refine ⟨34012776513858869228610059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22675184342572579485740039 34012776513858869228610059)
      ·
        refine ⟨51019164770788303842915089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34012776513858869228610059 51019164770788303842915089)
        ·
          refine ⟨38264373578091227882186317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51019164770788303842915089 38264373578091227882186317)
          ·
            refine ⟨14349140091784210455819869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38264373578091227882186317 14349140091784210455819869)
            ·
              refine ⟨5380927534419078920932451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14349140091784210455819869 5380927534419078920932451)
              ·
                refine ⟨8071391301628618381398677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5380927534419078920932451 8071391301628618381398677)
                ·
                  refine ⟨378346467263841486628063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8071391301628618381398677 378346467263841486628063)
                  ·
                    rfl

theorem cell21_1657861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_1657861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657861 prefixEnd_1657861 := by exact prefixLift 1657861
  have htrace : WordTrace (prefixWord ++ tailWord_1657861) baseStart_1657861 baseEnd_1657861 := by
    simpa [prefixWord, tailWord_1657861, baseEnd_1657861] using wordTrace_append hprefix tailTrace_1657861
  have hstable : (prefixWord ++ tailWord_1657861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657861).length < 2 ^ (prefixWord ++ tailWord_1657861).sum := by decide
  have hdescent : baseEnd_1657861 < baseStart_1657861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657864 : List Nat := [2, 1, 3, 2, 1, 3, 2, 4, 3]
def baseStart_1657864 : Nat := 118140960795 + 1657864 * 2 ^ 59
def prefixEnd_1657864 : Nat := 4983230072969 + 3 ^ 40 * 1657864 * 2
def baseEnd_1657864 : Nat := 378347151904714148078057

theorem tailTrace_1657864 : CollatzResearch.WordTrace tailWord_1657864 prefixEnd_1657864 378347151904714148078057 := by
  unfold tailWord_1657864
  simp only [CollatzResearch.WordTrace]
  refine ⟨30233633832924671737166323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40311511777232895649555097 30233633832924671737166323)
  ·
    refine ⟨45350450749387007605749485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30233633832924671737166323 45350450749387007605749485)
    ·
      refine ⟨17006419031020127852156057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45350450749387007605749485 17006419031020127852156057)
      ·
        refine ⟨12754814273265095889117043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17006419031020127852156057 12754814273265095889117043)
        ·
          refine ⟨19132221409897643833675565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12754814273265095889117043 19132221409897643833675565)
          ·
            refine ⟨7174583028711616437628337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19132221409897643833675565 7174583028711616437628337)
            ·
              refine ⟨5380937271533712328221253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7174583028711616437628337 5380937271533712328221253)
              ·
                refine ⟨1008925738412571061541485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5380937271533712328221253 1008925738412571061541485)
                ·
                  refine ⟨378347151904714148078057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1008925738412571061541485 378347151904714148078057)
                  ·
                    rfl

theorem cell21_1657864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 3].length) (baseStart_1657864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657864 prefixEnd_1657864 := by exact prefixLift 1657864
  have htrace : WordTrace (prefixWord ++ tailWord_1657864) baseStart_1657864 baseEnd_1657864 := by
    simpa [prefixWord, tailWord_1657864, baseEnd_1657864] using wordTrace_append hprefix tailTrace_1657864
  have hstable : (prefixWord ++ tailWord_1657864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657864).length < 2 ^ (prefixWord ++ tailWord_1657864).sum := by decide
  have hdescent : baseEnd_1657864 < baseStart_1657864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657875 : List Nat := [1, 1, 1, 2, 1, 4, 1, 10]
def baseStart_1657875 : Nat := 118140960795 + 1657875 * 2 ^ 59
def prefixEnd_1657875 : Nat := 4983230072969 + 3 ^ 40 * 1657875 * 2
def baseEnd_1657875 : Nat := 126116554084860191131567

theorem tailTrace_1657875 : CollatzResearch.WordTrace tailWord_1657875 prefixEnd_1657875 126116554084860191131567 := by
  unfold tailWord_1657875
  simp only [CollatzResearch.WordTrace]
  refine ⟨60467668868809492352983079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40311779245872994901988719 60467668868809492352983079)
  ·
    refine ⟨90701503303214238529474619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60467668868809492352983079 90701503303214238529474619)
    ·
      refine ⟨136052254954821357794211929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90701503303214238529474619 136052254954821357794211929)
      ·
        refine ⟨102039191216116018345658947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136052254954821357794211929 102039191216116018345658947)
        ·
          refine ⟨153058786824174027518488421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102039191216116018345658947 153058786824174027518488421)
          ·
            refine ⟨28698522529532630159716579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153058786824174027518488421 28698522529532630159716579)
            ·
              refine ⟨43047783794298945239574869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28698522529532630159716579 43047783794298945239574869)
              ·
                refine ⟨126116554084860191131567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43047783794298945239574869 126116554084860191131567)
                ·
                  rfl

theorem cell21_1657875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 10].length) (baseStart_1657875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657875 prefixEnd_1657875 := by exact prefixLift 1657875
  have htrace : WordTrace (prefixWord ++ tailWord_1657875) baseStart_1657875 baseEnd_1657875 := by
    simpa [prefixWord, tailWord_1657875, baseEnd_1657875] using wordTrace_append hprefix tailTrace_1657875
  have hstable : (prefixWord ++ tailWord_1657875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657875).length < 2 ^ (prefixWord ++ tailWord_1657875).sum := by decide
  have hdescent : baseEnd_1657875 < baseStart_1657875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657898 : List Nat := [3, 1, 4, 1, 3, 2, 1, 3, 3]
def baseStart_1657898 : Nat := 118140960795 + 1657898 * 2 ^ 59
def prefixEnd_1657898 : Nat := 4983230072969 + 3 ^ 40 * 1657898 * 2
def baseEnd_1657898 : Nat := 378354911167937644511321

theorem tailTrace_1657898 : CollatzResearch.WordTrace tailWord_1657898 prefixEnd_1657898 378354911167937644511321 := by
  unfold tailWord_1657898
  simp only [CollatzResearch.WordTrace]
  refine ⟨15117126936931541820267587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40312338498484111520713565 15117126936931541820267587)
  ·
    refine ⟨22675690405397312730401381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15117126936931541820267587 22675690405397312730401381)
    ·
      refine ⟨4251691951011996136950259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22675690405397312730401381 4251691951011996136950259)
      ·
        refine ⟨6377537926517994205425389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4251691951011996136950259 6377537926517994205425389)
        ·
          refine ⟨2391576722444247827034521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6377537926517994205425389 2391576722444247827034521)
          ·
            refine ⟨1793682541833185870275891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2391576722444247827034521 1793682541833185870275891)
            ·
              refine ⟨2690523812749778805413837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793682541833185870275891 2690523812749778805413837)
              ·
                refine ⟨1008946429781167052030189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2690523812749778805413837 1008946429781167052030189)
                ·
                  refine ⟨378354911167937644511321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1008946429781167052030189 378354911167937644511321)
                  ·
                    rfl

theorem cell21_1657898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_1657898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657898 prefixEnd_1657898 := by exact prefixLift 1657898
  have htrace : WordTrace (prefixWord ++ tailWord_1657898) baseStart_1657898 baseEnd_1657898 := by
    simpa [prefixWord, tailWord_1657898, baseEnd_1657898] using wordTrace_append hprefix tailTrace_1657898
  have hstable : (prefixWord ++ tailWord_1657898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657898).length < 2 ^ (prefixWord ++ tailWord_1657898).sum := by decide
  have hdescent : baseEnd_1657898 < baseStart_1657898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657926 : List Nat := [6, 1, 1, 1, 1, 3, 2, 6]
def baseStart_1657926 : Nat := 118140960795 + 1657926 * 2 ^ 59
def prefixEnd_1657926 : Nat := 4983230072969 + 3 ^ 40 * 1657926 * 2
def baseEnd_1657926 : Nat := 126120433716471939348199

theorem tailTrace_1657926 : CollatzResearch.WordTrace tailWord_1657926 prefixEnd_1657926 126120433716471939348199 := by
  unfold tailWord_1657926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1889672780988272751971551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40313019327749818708726421 1889672780988272751971551)
  ·
    refine ⟨2834509171482409127957327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1889672780988272751971551 2834509171482409127957327)
    ·
      refine ⟨4251763757223613691935991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2834509171482409127957327 4251763757223613691935991)
      ·
        refine ⟨6377645635835420537903987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4251763757223613691935991 6377645635835420537903987)
        ·
          refine ⟨9566468453753130806855981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6377645635835420537903987 9566468453753130806855981)
          ·
            refine ⟨3587425670157424052570993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9566468453753130806855981 3587425670157424052570993)
            ·
              refine ⟨2690569252618068039428245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3587425670157424052570993 2690569252618068039428245)
              ·
                refine ⟨126120433716471939348199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2690569252618068039428245 126120433716471939348199)
                ·
                  rfl

theorem cell21_1657926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_1657926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657926 prefixEnd_1657926 := by exact prefixLift 1657926
  have htrace : WordTrace (prefixWord ++ tailWord_1657926) baseStart_1657926 baseEnd_1657926 := by
    simpa [prefixWord, tailWord_1657926, baseEnd_1657926] using wordTrace_append hprefix tailTrace_1657926
  have hstable : (prefixWord ++ tailWord_1657926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657926).length < 2 ^ (prefixWord ++ tailWord_1657926).sum := by decide
  have hdescent : baseEnd_1657926 < baseStart_1657926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657951 : List Nat := [1, 1, 2, 3, 1, 1, 3, 9]
def baseStart_1657951 : Nat := 118140960795 + 1657951 * 2 ^ 59
def prefixEnd_1657951 : Nat := 4983230072969 + 3 ^ 40 * 1657951 * 2
def baseEnd_1657951 : Nat := 126122335496673776709293

theorem tailTrace_1657951 : CollatzResearch.WordTrace tailWord_1657951 prefixEnd_1657951 126122335496673776709293 := by
  unfold tailWord_1657951
  simp only [CollatzResearch.WordTrace]
  refine ⟨60470440816534157332749707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40313627211022771555166471 60470440816534157332749707)
  ·
    refine ⟨90705661224801235999124561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60470440816534157332749707 90705661224801235999124561)
    ·
      refine ⟨68029245918600926999343421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90705661224801235999124561 68029245918600926999343421)
      ·
        refine ⟨25510967219475347624753783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68029245918600926999343421 25510967219475347624753783)
        ·
          refine ⟨38266450829213021437130675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25510967219475347624753783 38266450829213021437130675)
          ·
            refine ⟨57399676243819532155696013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38266450829213021437130675 57399676243819532155696013)
            ·
              refine ⟨21524878591432324558386005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57399676243819532155696013 21524878591432324558386005)
              ·
                refine ⟨126122335496673776709293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21524878591432324558386005 126122335496673776709293)
                ·
                  rfl

theorem cell21_1657951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 9].length) (baseStart_1657951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657951 prefixEnd_1657951 := by exact prefixLift 1657951
  have htrace : WordTrace (prefixWord ++ tailWord_1657951) baseStart_1657951 baseEnd_1657951 := by
    simpa [prefixWord, tailWord_1657951, baseEnd_1657951] using wordTrace_append hprefix tailTrace_1657951
  have hstable : (prefixWord ++ tailWord_1657951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657951).length < 2 ^ (prefixWord ++ tailWord_1657951).sum := by decide
  have hdescent : baseEnd_1657951 < baseStart_1657951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657985 : List Nat := [1, 2, 4, 2, 2, 3, 1, 6]
def baseStart_1657985 : Nat := 118140960795 + 1657985 * 2 ^ 59
def prefixEnd_1657985 : Nat := 4983230072969 + 3 ^ 40 * 1657985 * 2
def baseEnd_1657985 : Nat := 126124921917748275520381

theorem tailTrace_1657985 : CollatzResearch.WordTrace tailWord_1657985 prefixEnd_1657985 126124921917748275520381 := by
  unfold tailWord_1657985
  simp only [CollatzResearch.WordTrace]
  refine ⟨60471680898410981139487409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40314453932273987426324939 60471680898410981139487409)
  ·
    refine ⟨45353760673808235854615557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60471680898410981139487409 45353760673808235854615557)
    ·
      refine ⟨8503830126339044222740417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45353760673808235854615557 8503830126339044222740417)
      ·
        refine ⟨6377872594754283167055313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8503830126339044222740417 6377872594754283167055313)
        ·
          refine ⟨4783404446065712375291485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6377872594754283167055313 4783404446065712375291485)
          ·
            refine ⟨1793776667274642140734307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4783404446065712375291485 1793776667274642140734307)
            ·
              refine ⟨2690665000911963211101461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793776667274642140734307 2690665000911963211101461)
              ·
                refine ⟨126124921917748275520381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2690665000911963211101461 126124921917748275520381)
                ·
                  rfl

theorem cell21_1657985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 6].length) (baseStart_1657985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1657985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1657985 prefixEnd_1657985 := by exact prefixLift 1657985
  have htrace : WordTrace (prefixWord ++ tailWord_1657985) baseStart_1657985 baseEnd_1657985 := by
    simpa [prefixWord, tailWord_1657985, baseEnd_1657985] using wordTrace_append hprefix tailTrace_1657985
  have hstable : (prefixWord ++ tailWord_1657985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657985).length < 2 ^ (prefixWord ++ tailWord_1657985).sum := by decide
  have hdescent : baseEnd_1657985 < baseStart_1657985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658013 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 6]
def baseStart_1658013 : Nat := 118140960795 + 1658013 * 2 ^ 59
def prefixEnd_1658013 : Nat := 4983230072969 + 3 ^ 40 * 1658013 * 2
def baseEnd_1658013 : Nat := 378381155734723000094419

theorem tailTrace_1658013 : CollatzResearch.WordTrace tailWord_1658013 prefixEnd_1658013 378381155734723000094419 := by
  unfold tailWord_1658013
  simp only [CollatzResearch.WordTrace]
  refine ⟨60472702142309541921506693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40315134761539694614337795 60472702142309541921506693)
  ·
    refine ⟨11338631651683039110282505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60472702142309541921506693 11338631651683039110282505)
    ·
      refine ⟨8503973738762279332711879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11338631651683039110282505 8503973738762279332711879)
      ·
        refine ⟨12755960608143418999067819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8503973738762279332711879 12755960608143418999067819)
        ·
          refine ⟨19133940912215128498601729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12755960608143418999067819 19133940912215128498601729)
          ·
            refine ⟨14350455684161346373951297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19133940912215128498601729 14350455684161346373951297)
            ·
              refine ⟨10762841763121009780463473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14350455684161346373951297 10762841763121009780463473)
              ·
                refine ⟨8072131322340757335347605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10762841763121009780463473 8072131322340757335347605)
                ·
                  refine ⟨378381155734723000094419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8072131322340757335347605 378381155734723000094419)
                  ·
                    rfl

theorem cell21_1658013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_1658013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658013 prefixEnd_1658013 := by exact prefixLift 1658013
  have htrace : WordTrace (prefixWord ++ tailWord_1658013) baseStart_1658013 baseEnd_1658013 := by
    simpa [prefixWord, tailWord_1658013, baseEnd_1658013] using wordTrace_append hprefix tailTrace_1658013
  have hstable : (prefixWord ++ tailWord_1658013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658013).length < 2 ^ (prefixWord ++ tailWord_1658013).sum := by decide
  have hdescent : baseEnd_1658013 < baseStart_1658013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658016 : List Nat := [2, 1, 1, 4, 2, 1, 4, 3, 3]
def baseStart_1658016 : Nat := 118140960795 + 1658016 * 2 ^ 59
def prefixEnd_1658016 : Nat := 4983230072969 + 3 ^ 40 * 1658016 * 2
def baseEnd_1658016 : Nat := 378381840375595661544413

theorem tailTrace_1658016 : CollatzResearch.WordTrace tailWord_1658016 prefixEnd_1658016 378381840375595661544413 := by
  unfold tailWord_1658016
  simp only [CollatzResearch.WordTrace]
  refine ⟨30236405780649336716932951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40315207707532448955910601 30236405780649336716932951)
  ·
    refine ⟨45354608670974005075399427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30236405780649336716932951 45354608670974005075399427)
    ·
      refine ⟨68031913006461007613099141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45354608670974005075399427 68031913006461007613099141)
      ·
        refine ⟨12755983688711438927456089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68031913006461007613099141 12755983688711438927456089)
        ·
          refine ⟨9566987766533579195592067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12755983688711438927456089 9566987766533579195592067)
          ·
            refine ⟨14350481649800368793388101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9566987766533579195592067 14350481649800368793388101)
            ·
              refine ⟨2690715309337569148760269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14350481649800368793388101 2690715309337569148760269)
              ·
                refine ⟨1009018241001588430785101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2690715309337569148760269 1009018241001588430785101)
                ·
                  refine ⟨378381840375595661544413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009018241001588430785101 378381840375595661544413)
                  ·
                    rfl

theorem cell21_1658016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 3].length) (baseStart_1658016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658016 prefixEnd_1658016 := by exact prefixLift 1658016
  have htrace : WordTrace (prefixWord ++ tailWord_1658016) baseStart_1658016 baseEnd_1658016 := by
    simpa [prefixWord, tailWord_1658016, baseEnd_1658016] using wordTrace_append hprefix tailTrace_1658016
  have hstable : (prefixWord ++ tailWord_1658016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658016).length < 2 ^ (prefixWord ++ tailWord_1658016).sum := by decide
  have hdescent : baseEnd_1658016 < baseStart_1658016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658244 : List Nat := [2, 3, 2, 1, 1, 3, 3, 3, 3]
def baseStart_1658244 : Nat := 118140960795 + 1658244 * 2 ^ 59
def prefixEnd_1658244 : Nat := 4983230072969 + 3 ^ 40 * 1658244 * 2
def baseEnd_1658244 : Nat := 378433873081917931743947

theorem tailTrace_1658244 : CollatzResearch.WordTrace tailWord_1658244 prefixEnd_1658244 378433873081917931743947 := by
  unfold tailWord_1658244
  simp only [CollatzResearch.WordTrace]
  refine ⟨30240563702236334186582893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40320751602981778915443857 30240563702236334186582893)
  ·
    refine ⟨11340211388338625319968585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30240563702236334186582893 11340211388338625319968585)
    ·
      refine ⟨8505158541253968989976439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11340211388338625319968585 8505158541253968989976439)
      ·
        refine ⟨12757737811880953484964659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8505158541253968989976439 12757737811880953484964659)
        ·
          refine ⟨19136606717821430227446989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12757737811880953484964659 19136606717821430227446989)
          ·
            refine ⟨7176227519183036335292621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19136606717821430227446989 7176227519183036335292621)
            ·
              refine ⟨2691085319693638625734733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7176227519183036335292621 2691085319693638625734733)
              ·
                refine ⟨1009156994885114484650525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2691085319693638625734733 1009156994885114484650525)
                ·
                  refine ⟨378433873081917931743947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009156994885114484650525 378433873081917931743947)
                  ·
                    rfl

theorem cell21_1658244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_1658244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658244 prefixEnd_1658244 := by exact prefixLift 1658244
  have htrace : WordTrace (prefixWord ++ tailWord_1658244) baseStart_1658244 baseEnd_1658244 := by
    simpa [prefixWord, tailWord_1658244, baseEnd_1658244] using wordTrace_append hprefix tailTrace_1658244
  have hstable : (prefixWord ++ tailWord_1658244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658244).length < 2 ^ (prefixWord ++ tailWord_1658244).sum := by decide
  have hdescent : baseEnd_1658244 < baseStart_1658244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658306 : List Nat := [3, 5, 2, 1, 10]
def baseStart_1658306 : Nat := 118140960795 + 1658306 * 2 ^ 59
def prefixEnd_1658306 : Nat := 4983230072969 + 3 ^ 40 * 1658306 * 2
def baseEnd_1658306 : Nat := 4672197806501476564327

theorem tailTrace_1658306 : CollatzResearch.WordTrace tailWord_1658306 prefixEnd_1658306 4672197806501476564327 := by
  unfold tailWord_1658306
  simp only [CollatzResearch.WordTrace]
  refine ⟨15120847182562013240480693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40322259153498701974615181 15120847182562013240480693)
  ·
    refine ⟨1417579423365188741295065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15120847182562013240480693 1417579423365188741295065)
    ·
      refine ⟨1063184567523891555971299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1417579423365188741295065 1063184567523891555971299)
      ·
        refine ⟨1594776851285837333956949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1063184567523891555971299 1594776851285837333956949)
        ·
          refine ⟨4672197806501476564327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1594776851285837333956949 4672197806501476564327)
          ·
            rfl

theorem cell21_1658306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 10].length) (baseStart_1658306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658306 prefixEnd_1658306 := by exact prefixLift 1658306
  have htrace : WordTrace (prefixWord ++ tailWord_1658306) baseStart_1658306 baseEnd_1658306 := by
    simpa [prefixWord, tailWord_1658306, baseEnd_1658306] using wordTrace_append hprefix tailTrace_1658306
  have hstable : (prefixWord ++ tailWord_1658306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658306).length < 2 ^ (prefixWord ++ tailWord_1658306).sum := by decide
  have hdescent : baseEnd_1658306 < baseStart_1658306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658379 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 5]
def baseStart_1658379 : Nat := 118140960795 + 1658379 * 2 ^ 59
def prefixEnd_1658379 : Nat := 4983230072969 + 3 ^ 40 * 1658379 * 2
def baseEnd_1658379 : Nat := 378464681921187696993671

theorem tailTrace_1658379 : CollatzResearch.WordTrace tailWord_1658379 prefixEnd_1658379 378464681921187696993671 := by
  unfold tailWord_1658379
  simp only [CollatzResearch.WordTrace]
  refine ⟨60486051258983586429330191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40324034172655724286220127 60486051258983586429330191)
  ·
    refine ⟨90729076888475379643995287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60486051258983586429330191 90729076888475379643995287)
    ·
      refine ⟨136093615332713069465992931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90729076888475379643995287 136093615332713069465992931)
      ·
        refine ⟨204140422999069604198989397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136093615332713069465992931 204140422999069604198989397)
        ·
          refine ⟨2392270582020346924206907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 204140422999069604198989397 2392270582020346924206907)
          ·
            refine ⟨3588405873030520386310361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392270582020346924206907 3588405873030520386310361)
            ·
              refine ⟨2691304404772890289732771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3588405873030520386310361 2691304404772890289732771)
              ·
                refine ⟨4036956607159335434599157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2691304404772890289732771 4036956607159335434599157)
                ·
                  refine ⟨378464681921187696993671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4036956607159335434599157 378464681921187696993671)
                  ·
                    rfl

theorem cell21_1658379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 5].length) (baseStart_1658379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658379 prefixEnd_1658379 := by exact prefixLift 1658379
  have htrace : WordTrace (prefixWord ++ tailWord_1658379) baseStart_1658379 baseEnd_1658379 := by
    simpa [prefixWord, tailWord_1658379, baseEnd_1658379] using wordTrace_append hprefix tailTrace_1658379
  have hstable : (prefixWord ++ tailWord_1658379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658379).length < 2 ^ (prefixWord ++ tailWord_1658379).sum := by decide
  have hdescent : baseEnd_1658379 < baseStart_1658379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658486 : List Nat := [5, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_1658486 : Nat := 118140960795 + 1658486 * 2 ^ 59
def prefixEnd_1658486 : Nat := 4983230072969 + 3 ^ 40 * 1658486 * 2
def baseEnd_1658486 : Nat := 378489100778979288710119

theorem tailTrace_1658486 : CollatzResearch.WordTrace tailWord_1658486 prefixEnd_1658486 378489100778979288710119 := by
  unfold tailWord_1658486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3780622116849746481467207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40326635913063962468983541 3780622116849746481467207)
  ·
    refine ⟨5670933175274619722200811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3780622116849746481467207 5670933175274619722200811)
    ·
      refine ⟨8506399762911929583301217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5670933175274619722200811 8506399762911929583301217)
      ·
        refine ⟨6379799822183947187475913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8506399762911929583301217 6379799822183947187475913)
        ·
          refine ⟨4784849866637960390606935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6379799822183947187475913 4784849866637960390606935)
          ·
            refine ⟨7177274799956940585910403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4784849866637960390606935 7177274799956940585910403)
            ·
              refine ⟨10765912199935410878865605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7177274799956940585910403 10765912199935410878865605)
              ·
                refine ⟨2018608537487889539787301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10765912199935410878865605 2018608537487889539787301)
                ·
                  refine ⟨378489100778979288710119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2018608537487889539787301 378489100778979288710119)
                  ·
                    rfl

theorem cell21_1658486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_1658486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658486 prefixEnd_1658486 := by exact prefixLift 1658486
  have htrace : WordTrace (prefixWord ++ tailWord_1658486) baseStart_1658486 baseEnd_1658486 := by
    simpa [prefixWord, tailWord_1658486, baseEnd_1658486] using wordTrace_append hprefix tailTrace_1658486
  have hstable : (prefixWord ++ tailWord_1658486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658486).length < 2 ^ (prefixWord ++ tailWord_1658486).sum := by decide
  have hdescent : baseEnd_1658486 < baseStart_1658486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658531 : List Nat := [1, 1, 1, 4, 1, 1, 6, 3, 3]
def baseStart_1658531 : Nat := 118140960795 + 1658531 * 2 ^ 59
def prefixEnd_1658531 : Nat := 4983230072969 + 3 ^ 40 * 1658531 * 2
def baseEnd_1658531 : Nat := 378499370392069210460027

theorem tailTrace_1658531 : CollatzResearch.WordTrace tailWord_1658531 prefixEnd_1658531 378499370392069210460027 := by
  unfold tailWord_1658531
  simp only [CollatzResearch.WordTrace]
  refine ⟨60491595154432916388863447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40327730102955277592575631 60491595154432916388863447)
  ·
    refine ⟨90737392731649374583295171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60491595154432916388863447 90737392731649374583295171)
    ·
      refine ⟨136106089097474061874942757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90737392731649374583295171 136106089097474061874942757)
      ·
        refine ⟨25519891705776386601551767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136106089097474061874942757 25519891705776386601551767)
        ·
          refine ⟨38279837558664579902327651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25519891705776386601551767 38279837558664579902327651)
          ·
            refine ⟨57419756337996869853491477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38279837558664579902327651 57419756337996869853491477)
            ·
              refine ⟨2691551078343603274382413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57419756337996869853491477 2691551078343603274382413)
              ·
                refine ⟨1009331654378851227893405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2691551078343603274382413 1009331654378851227893405)
                ·
                  refine ⟨378499370392069210460027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009331654378851227893405 378499370392069210460027)
                  ·
                    rfl

theorem cell21_1658531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 3].length) (baseStart_1658531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658531 prefixEnd_1658531 := by exact prefixLift 1658531
  have htrace : WordTrace (prefixWord ++ tailWord_1658531) baseStart_1658531 baseEnd_1658531 := by
    simpa [prefixWord, tailWord_1658531, baseEnd_1658531] using wordTrace_append hprefix tailTrace_1658531
  have hstable : (prefixWord ++ tailWord_1658531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658531).length < 2 ^ (prefixWord ++ tailWord_1658531).sum := by decide
  have hdescent : baseEnd_1658531 < baseStart_1658531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658604 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 6]
def baseStart_1658604 : Nat := 118140960795 + 1658604 * 2 ^ 59
def prefixEnd_1658604 : Nat := 4983230072969 + 3 ^ 40 * 1658604 * 2
def baseEnd_1658604 : Nat := 378516029986637305743211

theorem tailTrace_1658604 : CollatzResearch.WordTrace tailWord_1658604 prefixEnd_1658604 378516029986637305743211 := by
  unfold tailWord_1658604
  simp only [CollatzResearch.WordTrace]
  refine ⟨30247128841584224928135433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40329505122112299904180577 30247128841584224928135433)
  ·
    refine ⟨22685346631188168696101575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30247128841584224928135433 22685346631188168696101575)
    ·
      refine ⟨34028019946782253044152363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22685346631188168696101575 34028019946782253044152363)
      ·
        refine ⟨51042029920173379566228545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34028019946782253044152363 51042029920173379566228545)
        ·
          refine ⟨38281522440130034674671409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51042029920173379566228545 38281522440130034674671409)
          ·
            refine ⟨28711141830097526006003557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38281522440130034674671409 28711141830097526006003557)
            ·
              refine ⟨5383339093143286126125667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28711141830097526006003557 5383339093143286126125667)
              ·
                refine ⟨8075008639714929189188501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5383339093143286126125667 8075008639714929189188501)
                ·
                  refine ⟨378516029986637305743211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8075008639714929189188501 378516029986637305743211)
                  ·
                    rfl

theorem cell21_1658604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_1658604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658604 prefixEnd_1658604 := by exact prefixLift 1658604
  have htrace : WordTrace (prefixWord ++ tailWord_1658604) baseStart_1658604 baseEnd_1658604 := by
    simpa [prefixWord, tailWord_1658604, baseEnd_1658604] using wordTrace_append hprefix tailTrace_1658604
  have hstable : (prefixWord ++ tailWord_1658604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658604).length < 2 ^ (prefixWord ++ tailWord_1658604).sum := by decide
  have hdescent : baseEnd_1658604 < baseStart_1658604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658700 : List Nat := [2, 2, 1, 3, 4, 1, 2, 3, 3]
def baseStart_1658700 : Nat := 118140960795 + 1658700 * 2 ^ 59
def prefixEnd_1658700 : Nat := 4983230072969 + 3 ^ 40 * 1658700 * 2
def baseEnd_1658700 : Nat := 378537938494562472143015

theorem tailTrace_1658700 : CollatzResearch.WordTrace tailWord_1658700 prefixEnd_1658700 378537938494562472143015 := by
  unfold tailWord_1658700
  simp only [CollatzResearch.WordTrace]
  refine ⟨30248879545410329125882777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40331839393880438834510369 30248879545410329125882777)
  ·
    refine ⟨22686659659057746844412083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30248879545410329125882777 22686659659057746844412083)
    ·
      refine ⟨34029989488586620266618125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22686659659057746844412083 34029989488586620266618125)
      ·
        refine ⟨12761246058219982599981797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34029989488586620266618125 12761246058219982599981797)
        ·
          refine ⟨2392733635916246737496587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12761246058219982599981797 2392733635916246737496587)
          ·
            refine ⟨3589100453874370106244881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392733635916246737496587 3589100453874370106244881)
            ·
              refine ⟨2691825340405777579683661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3589100453874370106244881 2691825340405777579683661)
              ·
                refine ⟨1009434502652166592381373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2691825340405777579683661 1009434502652166592381373)
                ·
                  refine ⟨378537938494562472143015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009434502652166592381373 378537938494562472143015)
                  ·
                    rfl

theorem cell21_1658700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_1658700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658700 prefixEnd_1658700 := by exact prefixLift 1658700
  have htrace : WordTrace (prefixWord ++ tailWord_1658700) baseStart_1658700 baseEnd_1658700 := by
    simpa [prefixWord, tailWord_1658700, baseEnd_1658700] using wordTrace_append hprefix tailTrace_1658700
  have hstable : (prefixWord ++ tailWord_1658700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658700).length < 2 ^ (prefixWord ++ tailWord_1658700).sum := by decide
  have hdescent : baseEnd_1658700 < baseStart_1658700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658711 : List Nat := [1, 1, 3, 2, 5, 1, 8]
def baseStart_1658711 : Nat := 118140960795 + 1658711 * 2 ^ 59
def prefixEnd_1658711 : Nat := 4983230072969 + 3 ^ 40 * 1658711 * 2
def baseEnd_1658711 : Nat := 42060049871603210828851

theorem tailTrace_1658711 : CollatzResearch.WordTrace tailWord_1658711 prefixEnd_1658711 42060049871603210828851 := by
  unfold tailWord_1658711
  simp only [CollatzResearch.WordTrace]
  refine ⟨60498160293780807130415987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40332106862520538086943991 60498160293780807130415987)
  ·
    refine ⟨90747240440671210695623981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60498160293780807130415987 90747240440671210695623981)
    ·
      refine ⟨34030215165251704010858993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90747240440671210695623981 34030215165251704010858993)
      ·
        refine ⟨25522661373938778008144245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34030215165251704010858993 25522661373938778008144245)
        ·
          refine ⟨2392749503806760438263523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25522661373938778008144245 2392749503806760438263523)
          ·
            refine ⟨3589124255710140657395285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392749503806760438263523 3589124255710140657395285)
            ·
              refine ⟨42060049871603210828851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3589124255710140657395285 42060049871603210828851)
              ·
                rfl

theorem cell21_1658711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 8].length) (baseStart_1658711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658711 prefixEnd_1658711 := by exact prefixLift 1658711
  have htrace : WordTrace (prefixWord ++ tailWord_1658711) baseStart_1658711 baseEnd_1658711 := by
    simpa [prefixWord, tailWord_1658711, baseEnd_1658711] using wordTrace_append hprefix tailTrace_1658711
  have hstable : (prefixWord ++ tailWord_1658711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658711).length < 2 ^ (prefixWord ++ tailWord_1658711).sum := by decide
  have hdescent : baseEnd_1658711 < baseStart_1658711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658756 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 6]
def baseStart_1658756 : Nat := 118140960795 + 1658756 * 2 ^ 59
def prefixEnd_1658756 : Nat := 4983230072969 + 3 ^ 40 * 1658756 * 2
def baseEnd_1658756 : Nat := 378550718457518819209567

theorem tailTrace_1658756 : CollatzResearch.WordTrace tailWord_1658756 prefixEnd_1658756 378550718457518819209567 := by
  unfold tailWord_1658756
  simp only [CollatzResearch.WordTrace]
  refine ⟨30249900789308889907902061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40333201052411853210536081 30249900789308889907902061)
  ·
    refine ⟨11343712795990833715463273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30249900789308889907902061 11343712795990833715463273)
    ·
      refine ⟨8507784596993125286597455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11343712795990833715463273 8507784596993125286597455)
      ·
        refine ⟨12761676895489687929896183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8507784596993125286597455 12761676895489687929896183)
        ·
          refine ⟨19142515343234531894844275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12761676895489687929896183 19142515343234531894844275)
          ·
            refine ⟨28713773014851797842266413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19142515343234531894844275 28713773014851797842266413)
            ·
              refine ⟨10767664880569424190849905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28713773014851797842266413 10767664880569424190849905)
              ·
                refine ⟨8075748660427068143137429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10767664880569424190849905 8075748660427068143137429)
                ·
                  refine ⟨378550718457518819209567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8075748660427068143137429 378550718457518819209567)
                  ·
                    rfl

theorem cell21_1658756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_1658756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658756 prefixEnd_1658756 := by exact prefixLift 1658756
  have htrace : WordTrace (prefixWord ++ tailWord_1658756) baseStart_1658756 baseEnd_1658756 := by
    simpa [prefixWord, tailWord_1658756, baseEnd_1658756] using wordTrace_append hprefix tailTrace_1658756
  have hstable : (prefixWord ++ tailWord_1658756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658756).length < 2 ^ (prefixWord ++ tailWord_1658756).sum := by decide
  have hdescent : baseEnd_1658756 < baseStart_1658756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658776 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 5]
def baseStart_1658776 : Nat := 118140960795 + 1658776 * 2 ^ 59
def prefixEnd_1658776 : Nat := 4983230072969 + 3 ^ 40 * 1658776 * 2
def baseEnd_1658776 : Nat := 378555282730003228876193

theorem tailTrace_1658776 : CollatzResearch.WordTrace tailWord_1658776 prefixEnd_1658776 378555282730003228876193 := by
  unfold tailWord_1658776
  simp only [CollatzResearch.WordTrace]
  refine ⟨30250265519272661615766091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40333687359030215487688121 30250265519272661615766091)
  ·
    refine ⟨45375398278908992423649137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30250265519272661615766091 45375398278908992423649137)
    ·
      refine ⟨34031548709181744317736853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45375398278908992423649137 34031548709181744317736853)
      ·
        refine ⟨1595228845742894264893915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34031548709181744317736853 1595228845742894264893915)
        ·
          refine ⟨2392843268614341397340873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595228845742894264893915 2392843268614341397340873)
          ·
            refine ⟨1794632451460756048005655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2392843268614341397340873 1794632451460756048005655)
            ·
              refine ⟨2691948677191134072008483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1794632451460756048005655 2691948677191134072008483)
              ·
                refine ⟨4037923015786701108012725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2691948677191134072008483 4037923015786701108012725)
                ·
                  refine ⟨378555282730003228876193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4037923015786701108012725 378555282730003228876193)
                  ·
                    rfl

theorem cell21_1658776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_1658776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658776 prefixEnd_1658776 := by exact prefixLift 1658776
  have htrace : WordTrace (prefixWord ++ tailWord_1658776) baseStart_1658776 baseEnd_1658776 := by
    simpa [prefixWord, tailWord_1658776, baseEnd_1658776] using wordTrace_append hprefix tailTrace_1658776
  have hstable : (prefixWord ++ tailWord_1658776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658776).length < 2 ^ (prefixWord ++ tailWord_1658776).sum := by decide
  have hdescent : baseEnd_1658776 < baseStart_1658776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658832 : List Nat := [2, 1, 1, 1, 1, 2, 5, 4, 4]
def baseStart_1658832 : Nat := 118140960795 + 1658832 * 2 ^ 59
def prefixEnd_1658832 : Nat := 4983230072969 + 3 ^ 40 * 1658832 * 2
def baseEnd_1658832 : Nat := 378568062692959575942745

theorem tailTrace_1658832 : CollatzResearch.WordTrace tailWord_1658832 prefixEnd_1658832 378568062692959575942745 := by
  unfold tailWord_1658832
  simp only [CollatzResearch.WordTrace]
  refine ⟨30251286763171222397785375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40335049017561629863713833 30251286763171222397785375)
  ·
    refine ⟨45376930144756833596678063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30251286763171222397785375 45376930144756833596678063)
    ·
      refine ⟨68065395217135250395017095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45376930144756833596678063 68065395217135250395017095)
      ·
        refine ⟨102098092825702875592525643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68065395217135250395017095 102098092825702875592525643)
        ·
          refine ⟨153147139238554313388788465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102098092825702875592525643 153147139238554313388788465)
          ·
            refine ⟨114860354428915735041591349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153147139238554313388788465 114860354428915735041591349)
            ·
              refine ⟨10768158227710850160149189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114860354428915735041591349 10768158227710850160149189)
              ·
                refine ⟨2019029667695784405027973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10768158227710850160149189 2019029667695784405027973)
                ·
                  refine ⟨378568062692959575942745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2019029667695784405027973 378568062692959575942745)
                  ·
                    rfl

theorem cell21_1658832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_1658832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658832 prefixEnd_1658832 := by exact prefixLift 1658832
  have htrace : WordTrace (prefixWord ++ tailWord_1658832) baseStart_1658832 baseEnd_1658832 := by
    simpa [prefixWord, tailWord_1658832, baseEnd_1658832] using wordTrace_append hprefix tailTrace_1658832
  have hstable : (prefixWord ++ tailWord_1658832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658832).length < 2 ^ (prefixWord ++ tailWord_1658832).sum := by decide
  have hdescent : baseEnd_1658832 < baseStart_1658832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658838 : List Nat := [5, 2, 1, 1, 4, 1, 1, 6]
def baseStart_1658838 : Nat := 118140960795 + 1658838 * 2 ^ 59
def prefixEnd_1658838 : Nat := 4983230072969 + 3 ^ 40 * 1658838 * 2
def baseEnd_1658838 : Nat := 126189810658234966280911

theorem tailTrace_1658838 : CollatzResearch.WordTrace tailWord_1658838 prefixEnd_1658838 126189810658234966280911 := by
  unfold tailWord_1658838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3781424522770044238768073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40335194909547138546859445 3781424522770044238768073)
  ·
    refine ⟨2836068392077533179076055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3781424522770044238768073 2836068392077533179076055)
    ·
      refine ⟨4254102588116299768614083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2836068392077533179076055 4254102588116299768614083)
      ·
        refine ⟨6381153882174449652921125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4254102588116299768614083 6381153882174449652921125)
        ·
          refine ⟨1196466352907709309922711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6381153882174449652921125 1196466352907709309922711)
          ·
            refine ⟨1794699529361563964884067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196466352907709309922711 1794699529361563964884067)
            ·
              refine ⟨2692049294042345947326101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1794699529361563964884067 2692049294042345947326101)
              ·
                refine ⟨126189810658234966280911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2692049294042345947326101 126189810658234966280911)
                ·
                  rfl

theorem cell21_1658838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_1658838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658838 prefixEnd_1658838 := by exact prefixLift 1658838
  have htrace : WordTrace (prefixWord ++ tailWord_1658838) baseStart_1658838 baseEnd_1658838 := by
    simpa [prefixWord, tailWord_1658838, baseEnd_1658838] using wordTrace_append hprefix tailTrace_1658838
  have hstable : (prefixWord ++ tailWord_1658838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658838).length < 2 ^ (prefixWord ++ tailWord_1658838).sum := by decide
  have hdescent : baseEnd_1658838 < baseStart_1658838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658863 : List Nat := [1, 1, 2, 1, 4, 2, 5, 5]
def baseStart_1658863 : Nat := 118140960795 + 1658863 * 2 ^ 59
def prefixEnd_1658863 : Nat := 4983230072969 + 3 ^ 40 * 1658863 * 2
def baseEnd_1658863 : Nat := 126191712438436803642005

theorem tailTrace_1658863 : CollatzResearch.WordTrace tailWord_1658863 prefixEnd_1658863 126191712438436803642005 := by
  unfold tailWord_1658863
  simp only [CollatzResearch.WordTrace]
  refine ⟨60503704189230137089949243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40335802792820091393299495 60503704189230137089949243)
  ·
    refine ⟨90755556283845205634923865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60503704189230137089949243 90755556283845205634923865)
    ·
      refine ⟨68066667212883904226192899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90755556283845205634923865 68066667212883904226192899)
      ·
        refine ⟨102100000819325856339289349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68066667212883904226192899 102100000819325856339289349)
        ·
          refine ⟨19143750153623598063616753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102100000819325856339289349 19143750153623598063616753)
          ·
            refine ⟨14357812615217698547712565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19143750153623598063616753 14357812615217698547712565)
            ·
              refine ⟨1346044932676659238848053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14357812615217698547712565 1346044932676659238848053)
              ·
                refine ⟨126191712438436803642005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1346044932676659238848053 126191712438436803642005)
                ·
                  rfl

theorem cell21_1658863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 5].length) (baseStart_1658863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658863 prefixEnd_1658863 := by exact prefixLift 1658863
  have htrace : WordTrace (prefixWord ++ tailWord_1658863) baseStart_1658863 baseEnd_1658863 := by
    simpa [prefixWord, tailWord_1658863, baseEnd_1658863] using wordTrace_append hprefix tailTrace_1658863
  have hstable : (prefixWord ++ tailWord_1658863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658863).length < 2 ^ (prefixWord ++ tailWord_1658863).sum := by decide
  have hdescent : baseEnd_1658863 < baseStart_1658863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658886 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1658886 : Nat := 118140960795 + 1658886 * 2 ^ 59
def prefixEnd_1658886 : Nat := 4983230072969 + 3 ^ 40 * 1658886 * 2
def baseEnd_1658886 : Nat := 378580386228667482042635

theorem tailTrace_1658886 : CollatzResearch.WordTrace tailWord_1658886 prefixEnd_1658886 378580386228667482042635 := by
  unfold tailWord_1658886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1890766970879587875563641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40336362045431208012024341 1890766970879587875563641)
  ·
    refine ⟨1418075228159690906672731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1890766970879587875563641 1418075228159690906672731)
    ·
      refine ⟨2127112842239536360009097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1418075228159690906672731 2127112842239536360009097)
      ·
        refine ⟨1595334631679652270006823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2127112842239536360009097 1595334631679652270006823)
        ·
          refine ⟨2393001947519478405010235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595334631679652270006823 2393001947519478405010235)
          ·
            refine ⟨3589502921279217607515353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393001947519478405010235 3589502921279217607515353)
            ·
              refine ⟨2692127190959413205636515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3589502921279217607515353 2692127190959413205636515)
              ·
                refine ⟨4038190786439119808454773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2692127190959413205636515 4038190786439119808454773)
                ·
                  refine ⟨378580386228667482042635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4038190786439119808454773 378580386228667482042635)
                  ·
                    rfl

theorem cell21_1658886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1658886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658886 prefixEnd_1658886 := by exact prefixLift 1658886
  have htrace : WordTrace (prefixWord ++ tailWord_1658886) baseStart_1658886 baseEnd_1658886 := by
    simpa [prefixWord, tailWord_1658886, baseEnd_1658886] using wordTrace_append hprefix tailTrace_1658886
  have hstable : (prefixWord ++ tailWord_1658886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658886).length < 2 ^ (prefixWord ++ tailWord_1658886).sum := by decide
  have hdescent : baseEnd_1658886 < baseStart_1658886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658894 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_1658894 : Nat := 118140960795 + 1658894 * 2 ^ 59
def prefixEnd_1658894 : Nat := 4983230072969 + 3 ^ 40 * 1658894 * 2
def baseEnd_1658894 : Nat := 378582211937661245909285

theorem tailTrace_1658894 : CollatzResearch.WordTrace tailWord_1658894 prefixEnd_1658894 378582211937661245909285 := by
  unfold tailWord_1658894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7563104356514728673040967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40336556568078552922885157 7563104356514728673040967)
  ·
    refine ⟨11344656534772093009561451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7563104356514728673040967 11344656534772093009561451)
    ·
      refine ⟨17016984802158139514342177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11344656534772093009561451 17016984802158139514342177)
      ·
        refine ⟨12762738601618604635756633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17016984802158139514342177 12762738601618604635756633)
        ·
          refine ⟨9572053951213953476817475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12762738601618604635756633 9572053951213953476817475)
          ·
            refine ⟨14358080926820930215226213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9572053951213953476817475 14358080926820930215226213)
            ·
              refine ⟨2692140173778924415354915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14358080926820930215226213 2692140173778924415354915)
              ·
                refine ⟨4038210260668386623032373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2692140173778924415354915 4038210260668386623032373)
                ·
                  refine ⟨378582211937661245909285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4038210260668386623032373 378582211937661245909285)
                  ·
                    rfl

theorem cell21_1658894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_1658894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658894 prefixEnd_1658894 := by exact prefixLift 1658894
  have htrace : WordTrace (prefixWord ++ tailWord_1658894) baseStart_1658894 baseEnd_1658894 := by
    simpa [prefixWord, tailWord_1658894, baseEnd_1658894] using wordTrace_append hprefix tailTrace_1658894
  have hstable : (prefixWord ++ tailWord_1658894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658894).length < 2 ^ (prefixWord ++ tailWord_1658894).sum := by decide
  have hdescent : baseEnd_1658894 < baseStart_1658894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658900 : List Nat := [2, 4, 3, 2, 1, 1, 3, 1, 4]
def baseStart_1658900 : Nat := 118140960795 + 1658900 * 2 ^ 59
def prefixEnd_1658900 : Nat := 4983230072969 + 3 ^ 40 * 1658900 * 2
def baseEnd_1658900 : Nat := 378583581219406568809273

theorem tailTrace_1658900 : CollatzResearch.WordTrace tailWord_1658900 prefixEnd_1658900 378583581219406568809273 := by
  unfold tailWord_1658900
  simp only [CollatzResearch.WordTrace]
  refine ⟨30252526845048046204523077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40336702460064061606030769 30252526845048046204523077)
  ·
    refine ⟨5672348783446508663348077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30252526845048046204523077 5672348783446508663348077)
    ·
      refine ⟨2127130793792440748755529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5672348783446508663348077 2127130793792440748755529)
      ·
        refine ⟨1595348095344330561566647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2127130793792440748755529 1595348095344330561566647)
        ·
          refine ⟨2393022143016495842349971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595348095344330561566647 2393022143016495842349971)
          ·
            refine ⟨3589533214524743763524957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393022143016495842349971 3589533214524743763524957)
            ·
              refine ⟨1346074955446778911321859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3589533214524743763524957 1346074955446778911321859)
              ·
                refine ⟨2019112433170168366982789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1346074955446778911321859 2019112433170168366982789)
                ·
                  refine ⟨378583581219406568809273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2019112433170168366982789 378583581219406568809273)
                  ·
                    rfl

theorem cell21_1658900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_1658900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1658900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1658900 prefixEnd_1658900 := by exact prefixLift 1658900
  have htrace : WordTrace (prefixWord ++ tailWord_1658900) baseStart_1658900 baseEnd_1658900 := by
    simpa [prefixWord, tailWord_1658900, baseEnd_1658900] using wordTrace_append hprefix tailTrace_1658900
  have hstable : (prefixWord ++ tailWord_1658900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658900).length < 2 ^ (prefixWord ++ tailWord_1658900).sum := by decide
  have hdescent : baseEnd_1658900 < baseStart_1658900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659001 : List Nat := [1, 2, 1, 3, 4, 2, 2, 2, 4]
def baseStart_1659001 : Nat := 118140960795 + 1659001 * 2 ^ 59
def prefixEnd_1659001 : Nat := 4983230072969 + 3 ^ 40 * 1659001 * 2
def baseEnd_1659001 : Nat := 378606630795452837625733

theorem tailTrace_1659001 : CollatzResearch.WordTrace tailWord_1659001 prefixEnd_1659001 378606630795452837625733 := by
  unfold tailWord_1659001
  simp only [CollatzResearch.WordTrace]
  refine ⟨60508737462730186658472857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40339158308486791105648571 60508737462730186658472857)
  ·
    refine ⟨45381553097047639993854643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60508737462730186658472857 45381553097047639993854643)
    ·
      refine ⟨68072329645571459990781965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45381553097047639993854643 68072329645571459990781965)
      ·
        refine ⟨25527123617089297496543237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68072329645571459990781965 25527123617089297496543237)
        ·
          refine ⟨4786335678204243280601857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25527123617089297496543237 4786335678204243280601857)
          ·
            refine ⟨3589751758653182460451393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4786335678204243280601857 3589751758653182460451393)
            ·
              refine ⟨2692313818989886845338545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3589751758653182460451393 2692313818989886845338545)
              ·
                refine ⟨2019235364242415134003909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2692313818989886845338545 2019235364242415134003909)
                ·
                  refine ⟨378606630795452837625733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2019235364242415134003909 378606630795452837625733)
                  ·
                    rfl

theorem cell21_1659001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_1659001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659001 prefixEnd_1659001 := by exact prefixLift 1659001
  have htrace : WordTrace (prefixWord ++ tailWord_1659001) baseStart_1659001 baseEnd_1659001 := by
    simpa [prefixWord, tailWord_1659001, baseEnd_1659001] using wordTrace_append hprefix tailTrace_1659001
  have hstable : (prefixWord ++ tailWord_1659001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659001).length < 2 ^ (prefixWord ++ tailWord_1659001).sum := by decide
  have hdescent : baseEnd_1659001 < baseStart_1659001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659004 : List Nat := [2, 2, 2, 1, 1, 6, 2, 2, 3]
def baseStart_1659004 : Nat := 118140960795 + 1659004 * 2 ^ 59
def prefixEnd_1659004 : Nat := 4983230072969 + 3 ^ 40 * 1659004 * 2
def baseEnd_1659004 : Nat := 378607315436325499075727

theorem tailTrace_1659004 : CollatzResearch.WordTrace tailWord_1659004 prefixEnd_1659004 378607315436325499075727 := by
  unfold tailWord_1659004
  simp only [CollatzResearch.WordTrace]
  refine ⟨30254423440859659085416033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40339231254479545447221377 30254423440859659085416033)
  ·
    refine ⟨22690817580644744314062025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30254423440859659085416033 22690817580644744314062025)
    ·
      refine ⟨17018113185483558235546519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22690817580644744314062025 17018113185483558235546519)
      ·
        refine ⟨25527169778225337353319779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17018113185483558235546519 25527169778225337353319779)
        ·
          refine ⟨38290754667338006029979669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25527169778225337353319779 38290754667338006029979669)
          ·
            refine ⟨1794879125031469032655297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38290754667338006029979669 1794879125031469032655297)
            ·
              refine ⟨1346159343773601774491473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1794879125031469032655297 1346159343773601774491473)
              ·
                refine ⟨1009619507830201330868605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346159343773601774491473 1009619507830201330868605)
                ·
                  refine ⟨378607315436325499075727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009619507830201330868605 378607315436325499075727)
                  ·
                    rfl

theorem cell21_1659004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_1659004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659004 prefixEnd_1659004 := by exact prefixLift 1659004
  have htrace : WordTrace (prefixWord ++ tailWord_1659004) baseStart_1659004 baseEnd_1659004 := by
    simpa [prefixWord, tailWord_1659004, baseEnd_1659004] using wordTrace_append hprefix tailTrace_1659004
  have hstable : (prefixWord ++ tailWord_1659004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659004).length < 2 ^ (prefixWord ++ tailWord_1659004).sum := by decide
  have hdescent : baseEnd_1659004 < baseStart_1659004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659029 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 5]
def baseStart_1659029 : Nat := 118140960795 + 1659029 * 2 ^ 59
def prefixEnd_1659029 : Nat := 4983230072969 + 3 ^ 40 * 1659029 * 2
def baseEnd_1659029 : Nat := 378613020776931011159009

theorem tailTrace_1659029 : CollatzResearch.WordTrace tailWord_1659029 prefixEnd_1659029 378613020776931011159009 := by
  unfold tailWord_1659029
  simp only [CollatzResearch.WordTrace]
  refine ⟨60509758706628747440492141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40339839137752498293661427 60509758706628747440492141)
  ·
    refine ⟨22691159514985780290184553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60509758706628747440492141 22691159514985780290184553)
    ·
      refine ⟨17018369636239335217638415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22691159514985780290184553 17018369636239335217638415)
      ·
        refine ⟨25527554454359002826457623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17018369636239335217638415 25527554454359002826457623)
        ·
          refine ⟨38291331681538504239686435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25527554454359002826457623 38291331681538504239686435)
          ·
            refine ⟨57436997522307756359529653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38291331681538504239686435 57436997522307756359529653)
            ·
              refine ⟨5384718517716352158705905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57436997522307756359529653 5384718517716352158705905)
              ·
                refine ⟨4038538888287264119029429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5384718517716352158705905 4038538888287264119029429)
                ·
                  refine ⟨378613020776931011159009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4038538888287264119029429 378613020776931011159009)
                  ·
                    rfl

theorem cell21_1659029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_1659029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659029 prefixEnd_1659029 := by exact prefixLift 1659029
  have htrace : WordTrace (prefixWord ++ tailWord_1659029) baseStart_1659029 baseEnd_1659029 := by
    simpa [prefixWord, tailWord_1659029, baseEnd_1659029] using wordTrace_append hprefix tailTrace_1659029
  have hstable : (prefixWord ++ tailWord_1659029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659029).length < 2 ^ (prefixWord ++ tailWord_1659029).sum := by decide
  have hdescent : baseEnd_1659029 < baseStart_1659029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659032 : List Nat := [2, 1, 2, 4, 3, 1, 3, 5]
def baseStart_1659032 : Nat := 118140960795 + 1659032 * 2 ^ 59
def prefixEnd_1659032 : Nat := 4983230072969 + 3 ^ 40 * 1659032 * 2
def baseEnd_1659032 : Nat := 126204568472601224203001

theorem tailTrace_1659032 : CollatzResearch.WordTrace tailWord_1659032 prefixEnd_1659032 126204568472601224203001 := by
  unfold tailWord_1659032
  simp only [CollatzResearch.WordTrace]
  refine ⟨30254934062808939476425675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40339912083745252635234233 30254934062808939476425675)
  ·
    refine ⟨45382401094213409214638513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30254934062808939476425675 45382401094213409214638513)
    ·
      refine ⟨34036800820660056910978885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45382401094213409214638513 34036800820660056910978885)
      ·
        refine ⟨6381900153873760670808541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34036800820660056910978885 6381900153873760670808541)
        ·
          refine ⟨2393212557702660251553203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6381900153873760670808541 2393212557702660251553203)
          ·
            refine ⟨3589818836553990377329805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393212557702660251553203 3589818836553990377329805)
            ·
              refine ⟨1346182063707746391498677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3589818836553990377329805 1346182063707746391498677)
              ·
                refine ⟨126204568472601224203001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1346182063707746391498677 126204568472601224203001)
                ·
                  rfl

theorem cell21_1659032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 5].length) (baseStart_1659032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659032 prefixEnd_1659032 := by exact prefixLift 1659032
  have htrace : WordTrace (prefixWord ++ tailWord_1659032) baseStart_1659032 baseEnd_1659032 := by
    simpa [prefixWord, tailWord_1659032, baseEnd_1659032] using wordTrace_append hprefix tailTrace_1659032
  have hstable : (prefixWord ++ tailWord_1659032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659032).length < 2 ^ (prefixWord ++ tailWord_1659032).sum := by decide
  have hdescent : baseEnd_1659032 < baseStart_1659032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659122 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 5]
def baseStart_1659122 : Nat := 118140960795 + 1659122 * 2 ^ 59
def prefixEnd_1659122 : Nat := 4983230072969 + 3 ^ 40 * 1659122 * 2
def baseEnd_1659122 : Nat := 378634244643983516108819

theorem tailTrace_1659122 : CollatzResearch.WordTrace tailWord_1659122 prefixEnd_1659122 378634244643983516108819 := by
  unfold tailWord_1659122
  simp only [CollatzResearch.WordTrace]
  refine ⟨15128287673822956080906905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40342100463527882882418413 15128287673822956080906905)
  ·
    refine ⟨11346215755367217060680179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15128287673822956080906905 11346215755367217060680179)
    ·
      refine ⟨17019323633050825591020269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11346215755367217060680179 17019323633050825591020269)
      ·
        refine ⟨6382246362394059596632601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17019323633050825591020269 6382246362394059596632601)
        ·
          refine ⟨4786684771795544697474451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6382246362394059596632601 4786684771795544697474451)
          ·
            refine ⟨7180027157693317046211677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4786684771795544697474451 7180027157693317046211677)
            ·
              refine ⟨2692510184134993892329379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7180027157693317046211677 2692510184134993892329379)
              ·
                refine ⟨4038765276202490838494069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2692510184134993892329379 4038765276202490838494069)
                ·
                  refine ⟨378634244643983516108819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4038765276202490838494069 378634244643983516108819)
                  ·
                    rfl

theorem cell21_1659122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_1659122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659122 prefixEnd_1659122 := by exact prefixLift 1659122
  have htrace : WordTrace (prefixWord ++ tailWord_1659122) baseStart_1659122 baseEnd_1659122 := by
    simpa [prefixWord, tailWord_1659122, baseEnd_1659122] using wordTrace_append hprefix tailTrace_1659122
  have hstable : (prefixWord ++ tailWord_1659122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659122).length < 2 ^ (prefixWord ++ tailWord_1659122).sum := by decide
  have hdescent : baseEnd_1659122 < baseStart_1659122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659150 : List Nat := [4, 1, 1, 2, 1, 2, 1, 9]
def baseStart_1659150 : Nat := 118140960795 + 1659150 * 2 ^ 59
def prefixEnd_1659150 : Nat := 4983230072969 + 3 ^ 40 * 1659150 * 2
def baseEnd_1659150 : Nat := 126213544875153896547365

theorem tailTrace_1659150 : CollatzResearch.WordTrace tailWord_1659150 prefixEnd_1659150 126213544875153896547365 := by
  unfold tailWord_1659150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7564271492398798138205863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40342781292793590070431269 7564271492398798138205863)
  ·
    refine ⟨11346407238598197207308795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7564271492398798138205863 11346407238598197207308795)
    ·
      refine ⟨17019610857897295810963193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11346407238598197207308795 17019610857897295810963193)
      ·
        refine ⟨12764708143422971858222395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17019610857897295810963193 12764708143422971858222395)
        ·
          refine ⟨19147062215134457787333593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12764708143422971858222395 19147062215134457787333593)
          ·
            refine ⟨14360296661350843340500195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19147062215134457787333593 14360296661350843340500195)
            ·
              refine ⟨21540444992026265010750293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14360296661350843340500195 21540444992026265010750293)
              ·
                refine ⟨126213544875153896547365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21540444992026265010750293 126213544875153896547365)
                ·
                  rfl

theorem cell21_1659150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_1659150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659150 prefixEnd_1659150 := by exact prefixLift 1659150
  have htrace : WordTrace (prefixWord ++ tailWord_1659150) baseStart_1659150 baseEnd_1659150 := by
    simpa [prefixWord, tailWord_1659150, baseEnd_1659150] using wordTrace_append hprefix tailTrace_1659150
  have hstable : (prefixWord ++ tailWord_1659150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659150).length < 2 ^ (prefixWord ++ tailWord_1659150).sum := by decide
  have hdescent : baseEnd_1659150 < baseStart_1659150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659173 : List Nat := [1, 3, 1, 2, 6, 1, 2, 2, 3]
def baseStart_1659173 : Nat := 118140960795 + 1659173 * 2 ^ 59
def prefixEnd_1659173 : Nat := 4983230072969 + 3 ^ 40 * 1659173 * 2
def baseEnd_1659173 : Nat := 378645883538818760758715

theorem tailTrace_1659173 : CollatzResearch.WordTrace tailWord_1659173 prefixEnd_1659173 378645883538818760758715 := by
  unfold tailWord_1659173
  simp only [CollatzResearch.WordTrace]
  refine ⟨60515010818107060033734173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40343340545404706689156115 60515010818107060033734173)
  ·
    refine ⟨22693129056790147512650315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60515010818107060033734173 22693129056790147512650315)
    ·
      refine ⟨34039693585185221268975473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22693129056790147512650315 34039693585185221268975473)
      ·
        refine ⟨25529770188888915951731605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34039693585185221268975473 25529770188888915951731605)
        ·
          refine ⟨1196707977604167935237419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25529770188888915951731605 1196707977604167935237419)
          ·
            refine ⟨1795061966406251902856129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196707977604167935237419 1795061966406251902856129)
            ·
              refine ⟨1346296474804688927142097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1795061966406251902856129 1346296474804688927142097)
              ·
                refine ⟨1009722356103516695356573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346296474804688927142097 1009722356103516695356573)
                ·
                  refine ⟨378645883538818760758715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009722356103516695356573 378645883538818760758715)
                  ·
                    rfl

theorem cell21_1659173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_1659173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659173 prefixEnd_1659173 := by exact prefixLift 1659173
  have htrace : WordTrace (prefixWord ++ tailWord_1659173) baseStart_1659173 baseEnd_1659173 := by
    simpa [prefixWord, tailWord_1659173, baseEnd_1659173] using wordTrace_append hprefix tailTrace_1659173
  have hstable : (prefixWord ++ tailWord_1659173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659173).length < 2 ^ (prefixWord ++ tailWord_1659173).sum := by decide
  have hdescent : baseEnd_1659173 < baseStart_1659173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659198 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_1659198 : Nat := 118140960795 + 1659198 * 2 ^ 59
def prefixEnd_1659198 : Nat := 4983230072969 + 3 ^ 40 * 1659198 * 2
def baseEnd_1659198 : Nat := 378651588879424272841997

theorem tailTrace_1659198 : CollatzResearch.WordTrace tailWord_1659198 prefixEnd_1659198 378651588879424272841997 := by
  unfold tailWord_1659198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7564490330377061162924281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40343948428677659535596165 7564490330377061162924281)
  ·
    refine ⟨5673367747782795872193211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7564490330377061162924281 5673367747782795872193211)
    ·
      refine ⟨8510051621674193808289817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5673367747782795872193211 8510051621674193808289817)
      ·
        refine ⟨6382538716255645356217363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8510051621674193808289817 6382538716255645356217363)
        ·
          refine ⟨9573808074383468034326045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6382538716255645356217363 9573808074383468034326045)
          ·
            refine ⟨3590178027893800512872267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9573808074383468034326045 3590178027893800512872267)
            ·
              refine ⟨5385267041840700769308401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590178027893800512872267 5385267041840700769308401)
              ·
                refine ⟨4038950281380525576981301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5385267041840700769308401 4038950281380525576981301)
                ·
                  refine ⟨378651588879424272841997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4038950281380525576981301 378651588879424272841997)
                  ·
                    rfl

theorem cell21_1659198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_1659198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659198 prefixEnd_1659198 := by exact prefixLift 1659198
  have htrace : WordTrace (prefixWord ++ tailWord_1659198) baseStart_1659198 baseEnd_1659198 := by
    simpa [prefixWord, tailWord_1659198, baseEnd_1659198] using wordTrace_append hprefix tailTrace_1659198
  have hstable : (prefixWord ++ tailWord_1659198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659198).length < 2 ^ (prefixWord ++ tailWord_1659198).sum := by decide
  have hdescent : baseEnd_1659198 < baseStart_1659198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659266 : List Nat := [3, 4, 2, 1, 3, 1, 1, 3, 3]
def baseStart_1659266 : Nat := 118140960795 + 1659266 * 2 ^ 59
def prefixEnd_1659266 : Nat := 4983230072969 + 3 ^ 40 * 1659266 * 2
def baseEnd_1659266 : Nat := 378667107405871265708525

theorem tailTrace_1659266 : CollatzResearch.WordTrace tailWord_1659266 prefixEnd_1659266 378667107405871265708525 := by
  unfold tailWord_1659266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15129600701692534229217413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40345601871180091277913101 15129600701692534229217413)
  ·
    refine ⟨2836800131567350167978265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15129600701692534229217413 2836800131567350167978265)
    ·
      refine ⟨2127600098675512625983699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2836800131567350167978265 2127600098675512625983699)
      ·
        refine ⟨3191400148013268938975549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2127600098675512625983699 3191400148013268938975549)
        ·
          refine ⟨1196775055504975852115831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3191400148013268938975549 1196775055504975852115831)
          ·
            refine ⟨1795162583257463778173747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196775055504975852115831 1795162583257463778173747)
            ·
              refine ⟨2692743874886195667260621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795162583257463778173747 2692743874886195667260621)
              ·
                refine ⟨1009778953082323375222733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2692743874886195667260621 1009778953082323375222733)
                ·
                  refine ⟨378667107405871265708525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009778953082323375222733 378667107405871265708525)
                  ·
                    rfl

theorem cell21_1659266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_1659266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659266 prefixEnd_1659266 := by exact prefixLift 1659266
  have htrace : WordTrace (prefixWord ++ tailWord_1659266) baseStart_1659266 baseEnd_1659266 := by
    simpa [prefixWord, tailWord_1659266, baseEnd_1659266] using wordTrace_append hprefix tailTrace_1659266
  have hstable : (prefixWord ++ tailWord_1659266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659266).length < 2 ^ (prefixWord ++ tailWord_1659266).sum := by decide
  have hdescent : baseEnd_1659266 < baseStart_1659266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659271 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 8]
def baseStart_1659271 : Nat := 118140960795 + 1659271 * 2 ^ 59
def prefixEnd_1659271 : Nat := 4983230072969 + 3 ^ 40 * 1659271 * 2
def baseEnd_1659271 : Nat := 378668248473992368125181

theorem tailTrace_1659271 : CollatzResearch.WordTrace tailWord_1659271 prefixEnd_1659271 378668248473992368125181 := by
  unfold tailWord_1659271
  simp only [CollatzResearch.WordTrace]
  refine ⟨60518585171752022770801667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40345723447834681847201111 60518585171752022770801667)
  ·
    refine ⟨90777877757628034156202501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60518585171752022770801667 90777877757628034156202501)
    ·
      refine ⟨17020852079555256404287969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90777877757628034156202501 17020852079555256404287969)
      ·
        refine ⟨12765639059666442303215977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17020852079555256404287969 12765639059666442303215977)
        ·
          refine ⟨9574229294749831727411983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12765639059666442303215977 9574229294749831727411983)
          ·
            refine ⟨14361343942124747591117975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9574229294749831727411983 14361343942124747591117975)
            ·
              refine ⟨21542015913187121386676963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14361343942124747591117975 21542015913187121386676963)
              ·
                refine ⟨32313023869780682080015445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21542015913187121386676963 32313023869780682080015445)
                ·
                  refine ⟨378668248473992368125181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32313023869780682080015445 378668248473992368125181)
                  ·
                    rfl

theorem cell21_1659271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 8].length) (baseStart_1659271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659271 prefixEnd_1659271 := by exact prefixLift 1659271
  have htrace : WordTrace (prefixWord ++ tailWord_1659271) baseStart_1659271 baseEnd_1659271 := by
    simpa [prefixWord, tailWord_1659271, baseEnd_1659271] using wordTrace_append hprefix tailTrace_1659271
  have hstable : (prefixWord ++ tailWord_1659271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659271).length < 2 ^ (prefixWord ++ tailWord_1659271).sum := by decide
  have hdescent : baseEnd_1659271 < baseStart_1659271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659288 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 6]
def baseStart_1659288 : Nat := 118140960795 + 1659288 * 2 ^ 59
def prefixEnd_1659288 : Nat := 4983230072969 + 3 ^ 40 * 1659288 * 2
def baseEnd_1659288 : Nat := 378672128105604116341813

theorem tailTrace_1659288 : CollatzResearch.WordTrace tailWord_1659288 prefixEnd_1659288 378672128105604116341813 := by
  unfold tailWord_1659288
  simp only [CollatzResearch.WordTrace]
  refine ⟨30259602606345217337085259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40346136808460289782780345 30259602606345217337085259)
  ·
    refine ⟨45389403909517826005627889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30259602606345217337085259 45389403909517826005627889)
    ·
      refine ⟨34042052932138369504220917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45389403909517826005627889 34042052932138369504220917)
      ·
        refine ⟨3191442462387972141020711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34042052932138369504220917 3191442462387972141020711)
        ·
          refine ⟨4787163693581958211531067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3191442462387972141020711 4787163693581958211531067)
          ·
            refine ⟨7180745540372937317296601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4787163693581958211531067 7180745540372937317296601)
            ·
              refine ⟨5385559155279702987972451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7180745540372937317296601 5385559155279702987972451)
              ·
                refine ⟨8078338732919554481958677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5385559155279702987972451 8078338732919554481958677)
                ·
                  refine ⟨378672128105604116341813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8078338732919554481958677 378672128105604116341813)
                  ·
                    rfl

theorem cell21_1659288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_1659288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659288 prefixEnd_1659288 := by exact prefixLift 1659288
  have htrace : WordTrace (prefixWord ++ tailWord_1659288) baseStart_1659288 baseEnd_1659288 := by
    simpa [prefixWord, tailWord_1659288, baseEnd_1659288] using wordTrace_append hprefix tailTrace_1659288
  have hstable : (prefixWord ++ tailWord_1659288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659288).length < 2 ^ (prefixWord ++ tailWord_1659288).sum := by decide
  have hdescent : baseEnd_1659288 < baseStart_1659288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659350 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1659350 : Nat := 118140960795 + 1659350 * 2 ^ 59
def prefixEnd_1659350 : Nat := 4983230072969 + 3 ^ 40 * 1659350 * 2
def baseEnd_1659350 : Nat := 378686277350305786308353

theorem tailTrace_1659350 : CollatzResearch.WordTrace tailWord_1659350 prefixEnd_1659350 378686277350305786308353 := by
  unfold tailWord_1659350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3782591658654113703932969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40347644358977212841951669 3782591658654113703932969)
  ·
    refine ⟨2836943743990585277949727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3782591658654113703932969 2836943743990585277949727)
    ·
      refine ⟨4255415615985877916924591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2836943743990585277949727 4255415615985877916924591)
      ·
        refine ⟨6383123423978816875386887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4255415615985877916924591 6383123423978816875386887)
        ·
          refine ⟨9574685135968225313080331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6383123423978816875386887 9574685135968225313080331)
          ·
            refine ⟨14362027703952337969620497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9574685135968225313080331 14362027703952337969620497)
            ·
              refine ⟨10771520777964253477215373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14362027703952337969620497 10771520777964253477215373)
              ·
                refine ⟨4039320291736595053955765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10771520777964253477215373 4039320291736595053955765)
                ·
                  refine ⟨378686277350305786308353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4039320291736595053955765 378686277350305786308353)
                  ·
                    rfl

theorem cell21_1659350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1659350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659350 prefixEnd_1659350 := by exact prefixLift 1659350
  have htrace : WordTrace (prefixWord ++ tailWord_1659350) baseStart_1659350 baseEnd_1659350 := by
    simpa [prefixWord, tailWord_1659350, baseEnd_1659350] using wordTrace_append hprefix tailTrace_1659350
  have hstable : (prefixWord ++ tailWord_1659350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659350).length < 2 ^ (prefixWord ++ tailWord_1659350).sum := by decide
  have hdescent : baseEnd_1659350 < baseStart_1659350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659513 : List Nat := [1, 2, 1, 3, 3, 11]
def baseStart_1659513 : Nat := 118140960795 + 1659513 * 2 ^ 59
def prefixEnd_1659513 : Nat := 4983230072969 + 3 ^ 40 * 1659513 * 2
def baseEnd_1659513 : Nat := 14026795413742730558939

theorem tailTrace_1659513 : CollatzResearch.WordTrace tailWord_1659513 prefixEnd_1659513 14026795413742730558939 := by
  unfold tailWord_1659513
  simp only [CollatzResearch.WordTrace]
  refine ⟨60527411636875298101111193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40351607757916865400740795 60527411636875298101111193)
  ·
    refine ⟨45395558727656473575833395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60527411636875298101111193 45395558727656473575833395)
    ·
      refine ⟨68093338091484710363750093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45395558727656473575833395 68093338091484710363750093)
      ·
        refine ⟨25535001784306766386406285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68093338091484710363750093 25535001784306766386406285)
        ·
          refine ⟨9575625669115037394902357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25535001784306766386406285 9575625669115037394902357)
          ·
            refine ⟨14026795413742730558939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9575625669115037394902357 14026795413742730558939)
            ·
              rfl

theorem cell21_1659513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 11].length) (baseStart_1659513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659513 prefixEnd_1659513 := by exact prefixLift 1659513
  have htrace : WordTrace (prefixWord ++ tailWord_1659513) baseStart_1659513 baseEnd_1659513 := by
    simpa [prefixWord, tailWord_1659513, baseEnd_1659513] using wordTrace_append hprefix tailTrace_1659513
  have hstable : (prefixWord ++ tailWord_1659513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659513).length < 2 ^ (prefixWord ++ tailWord_1659513).sum := by decide
  have hdescent : baseEnd_1659513 < baseStart_1659513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659522 : List Nat := [3, 4, 3, 1, 1, 2, 1, 6]
def baseStart_1659522 : Nat := 118140960795 + 1659522 * 2 ^ 59
def prefixEnd_1659522 : Nat := 4983230072969 + 3 ^ 40 * 1659522 * 2
def baseEnd_1659522 : Nat := 126241843364557236480445

theorem tailTrace_1659522 : CollatzResearch.WordTrace tailWord_1659522 prefixEnd_1659522 126241843364557236480445 := by
  unfold tailWord_1659522
  simp only [CollatzResearch.WordTrace]
  refine ⟨15131934973460673159547205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40351826595895128425459213 15131934973460673159547205)
  ·
    refine ⟨2837237807523876217415101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15131934973460673159547205 2837237807523876217415101)
    ·
      refine ⟨1063964177821453581530663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2837237807523876217415101 1063964177821453581530663)
      ·
        refine ⟨1595946266732180372295995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1063964177821453581530663 1595946266732180372295995)
        ·
          refine ⟨2393919400098270558443993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595946266732180372295995 2393919400098270558443993)
          ·
            refine ⟨1795439550073702918832995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2393919400098270558443993 1795439550073702918832995)
            ·
              refine ⟨2693159325110554378249493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795439550073702918832995 2693159325110554378249493)
              ·
                refine ⟨126241843364557236480445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2693159325110554378249493 126241843364557236480445)
                ·
                  rfl

theorem cell21_1659522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_1659522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659522 prefixEnd_1659522 := by exact prefixLift 1659522
  have htrace : WordTrace (prefixWord ++ tailWord_1659522) baseStart_1659522 baseEnd_1659522 := by
    simpa [prefixWord, tailWord_1659522, baseEnd_1659522] using wordTrace_append hprefix tailTrace_1659522
  have hstable : (prefixWord ++ tailWord_1659522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659522).length < 2 ^ (prefixWord ++ tailWord_1659522).sum := by decide
  have hdescent : baseEnd_1659522 < baseStart_1659522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659561 : List Nat := [1, 2, 1, 1, 1, 1, 2, 9, 3]
def baseStart_1659561 : Nat := 118140960795 + 1659561 * 2 ^ 59
def prefixEnd_1659561 : Nat := 4983230072969 + 3 ^ 40 * 1659561 * 2
def baseEnd_1659561 : Nat := 378734430425016308291255

theorem tailTrace_1659561 : CollatzResearch.WordTrace tailWord_1659561 prefixEnd_1659561 378734430425016308291255 := by
  unfold tailWord_1659561
  simp only [CollatzResearch.WordTrace]
  refine ⟨60529162340701402298858537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40352774893800934865905691 60529162340701402298858537)
  ·
    refine ⟨45396871755526051724143903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60529162340701402298858537 45396871755526051724143903)
    ·
      refine ⟨68095307633289077586215855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45396871755526051724143903 68095307633289077586215855)
      ·
        refine ⟨102142961449933616379323783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68095307633289077586215855 102142961449933616379323783)
        ·
          refine ⟨153214442174900424568985675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102142961449933616379323783 153214442174900424568985675)
          ·
            refine ⟨229821663262350636853478513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153214442174900424568985675 229821663262350636853478513)
            ·
              refine ⟨172366247446762977640108885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229821663262350636853478513 172366247446762977640108885)
              ·
                refine ⟨1009958481133376822110013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 172366247446762977640108885 1009958481133376822110013)
                ·
                  refine ⟨378734430425016308291255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009958481133376822110013 378734430425016308291255)
                  ·
                    rfl

theorem cell21_1659561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 3].length) (baseStart_1659561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659561 prefixEnd_1659561 := by exact prefixLift 1659561
  have htrace : WordTrace (prefixWord ++ tailWord_1659561) baseStart_1659561 baseEnd_1659561 := by
    simpa [prefixWord, tailWord_1659561, baseEnd_1659561] using wordTrace_append hprefix tailTrace_1659561
  have hstable : (prefixWord ++ tailWord_1659561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659561).length < 2 ^ (prefixWord ++ tailWord_1659561).sum := by decide
  have hdescent : baseEnd_1659561 < baseStart_1659561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659612 : List Nat := [2, 2, 5, 1, 1, 3, 1, 3, 3]
def baseStart_1659612 : Nat := 118140960795 + 1659612 * 2 ^ 59
def prefixEnd_1659612 : Nat := 4983230072969 + 3 ^ 40 * 1659612 * 2
def baseEnd_1659612 : Nat := 378746069319851552941151

theorem tailTrace_1659612 : CollatzResearch.WordTrace tailWord_1659612 prefixEnd_1659612 378746069319851552941151 := by
  unfold tailWord_1659612
  simp only [CollatzResearch.WordTrace]
  refine ⟨30265511231758319004482545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40354014975677758672643393 30265511231758319004482545)
  ·
    refine ⟨22699133423818739253361909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30265511231758319004482545 22699133423818739253361909)
    ·
      refine ⟨2128043758483006805002679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22699133423818739253361909 2128043758483006805002679)
      ·
        refine ⟨3192065637724510207504019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2128043758483006805002679 3192065637724510207504019)
        ·
          refine ⟨4788098456586765311256029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3192065637724510207504019 4788098456586765311256029)
          ·
            refine ⟨1795536921220036991721011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4788098456586765311256029 1795536921220036991721011)
            ·
              refine ⟨2693305381830055487581517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795536921220036991721011 2693305381830055487581517)
              ·
                refine ⟨1009989518186270807843069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2693305381830055487581517 1009989518186270807843069)
                ·
                  refine ⟨378746069319851552941151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009989518186270807843069 378746069319851552941151)
                  ·
                    rfl

theorem cell21_1659612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_1659612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659612 prefixEnd_1659612 := by exact prefixLift 1659612
  have htrace : WordTrace (prefixWord ++ tailWord_1659612) baseStart_1659612 baseEnd_1659612 := by
    simpa [prefixWord, tailWord_1659612, baseEnd_1659612] using wordTrace_append hprefix tailTrace_1659612
  have hstable : (prefixWord ++ tailWord_1659612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659612).length < 2 ^ (prefixWord ++ tailWord_1659612).sum := by decide
  have hdescent : baseEnd_1659612 < baseStart_1659612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659665 : List Nat := [1, 2, 2, 1, 1, 3, 4, 7]
def baseStart_1659665 : Nat := 118140960795 + 1659665 * 2 ^ 59
def prefixEnd_1659665 : Nat := 4983230072969 + 3 ^ 40 * 1659665 * 2
def baseEnd_1659665 : Nat := 126252721547311746185903

theorem tailTrace_1659665 : CollatzResearch.WordTrace tailWord_1659665 prefixEnd_1659665 126252721547311746185903 := by
  unfold tailWord_1659665
  simp only [CollatzResearch.WordTrace]
  refine ⟨60532955532324628060644449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40355303688216418707096299 60532955532324628060644449)
  ·
    refine ⟨45399716649243471045483337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60532955532324628060644449 45399716649243471045483337)
    ·
      refine ⟨34049787486932603284112503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45399716649243471045483337 34049787486932603284112503)
      ·
        refine ⟨51074681230398904926168755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34049787486932603284112503 51074681230398904926168755)
        ·
          refine ⟨76612021845598357389253133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51074681230398904926168755 76612021845598357389253133)
          ·
            refine ⟨28729508192099384020969925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76612021845598357389253133 28729508192099384020969925)
            ·
              refine ⟨5386782786018634503931861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28729508192099384020969925 5386782786018634503931861)
              ·
                refine ⟨126252721547311746185903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5386782786018634503931861 126252721547311746185903)
                ·
                  rfl

theorem cell21_1659665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 7].length) (baseStart_1659665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659665 prefixEnd_1659665 := by exact prefixLift 1659665
  have htrace : WordTrace (prefixWord ++ tailWord_1659665) baseStart_1659665 baseEnd_1659665 := by
    simpa [prefixWord, tailWord_1659665, baseEnd_1659665] using wordTrace_append hprefix tailTrace_1659665
  have hstable : (prefixWord ++ tailWord_1659665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659665).length < 2 ^ (prefixWord ++ tailWord_1659665).sum := by decide
  have hdescent : baseEnd_1659665 < baseStart_1659665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659730 : List Nat := [3, 2, 2, 1, 1, 2, 4, 3, 3]
def baseStart_1659730 : Nat := 118140960795 + 1659730 * 2 ^ 59
def prefixEnd_1659730 : Nat := 4983230072969 + 3 ^ 40 * 1659730 * 2
def baseEnd_1659730 : Nat := 378772998527509569974243

theorem tailTrace_1659730 : CollatzResearch.WordTrace tailWord_1659730 prefixEnd_1659730 378772998527509569974243 := by
  unfold tailWord_1659730
  simp only [CollatzResearch.WordTrace]
  refine ⟨15133831569272286040440161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40356884184726096107840429 15133831569272286040440161)
  ·
    refine ⟨11350373676954214530330121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15133831569272286040440161 11350373676954214530330121)
    ·
      refine ⟨8512780257715660897747591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11350373676954214530330121 8512780257715660897747591)
      ·
        refine ⟨12769170386573491346621387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8512780257715660897747591 12769170386573491346621387)
        ·
          refine ⟨19153755579860237019932081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12769170386573491346621387 19153755579860237019932081)
          ·
            refine ⟨14365316684895177764949061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19153755579860237019932081 14365316684895177764949061)
            ·
              refine ⟨2693496878417845830927949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14365316684895177764949061 2693496878417845830927949)
              ·
                refine ⟨1010061329406692186597981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2693496878417845830927949 1010061329406692186597981)
                ·
                  refine ⟨378772998527509569974243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1010061329406692186597981 378772998527509569974243)
                  ·
                    rfl

theorem cell21_1659730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_1659730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659730 prefixEnd_1659730 := by exact prefixLift 1659730
  have htrace : WordTrace (prefixWord ++ tailWord_1659730) baseStart_1659730 baseEnd_1659730 := by
    simpa [prefixWord, tailWord_1659730, baseEnd_1659730] using wordTrace_append hprefix tailTrace_1659730
  have hstable : (prefixWord ++ tailWord_1659730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659730).length < 2 ^ (prefixWord ++ tailWord_1659730).sum := by decide
  have hdescent : baseEnd_1659730 < baseStart_1659730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659817 : List Nat := [1, 2, 1, 1, 1, 1, 8, 6]
def baseStart_1659817 : Nat := 118140960795 + 1659817 * 2 ^ 59
def prefixEnd_1659817 : Nat := 4983230072969 + 3 ^ 40 * 1659817 * 2
def baseEnd_1659817 : Nat := 126264284370938917341355

theorem tailTrace_1659817 : CollatzResearch.WordTrace tailWord_1659817 prefixEnd_1659817 126264284370938917341355 := by
  unfold tailWord_1659817
  simp only [CollatzResearch.WordTrace]
  refine ⟨60538499427773958020177705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40358999618515972013451803 60538499427773958020177705)
  ·
    refine ⟨45403874570830468515133279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60538499427773958020177705 45403874570830468515133279)
    ·
      refine ⟨68105811856245702772699919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45403874570830468515133279 68105811856245702772699919)
      ·
        refine ⟨102158717784368554159049879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68105811856245702772699919 102158717784368554159049879)
        ·
          refine ⟨153238076676552831238574819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102158717784368554159049879 153238076676552831238574819)
          ·
            refine ⟨229857115014829246857862229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153238076676552831238574819 229857115014829246857862229)
            ·
              refine ⟨2693638066580030236615573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 229857115014829246857862229 2693638066580030236615573)
              ·
                refine ⟨126264284370938917341355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2693638066580030236615573 126264284370938917341355)
                ·
                  rfl

theorem cell21_1659817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 6].length) (baseStart_1659817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659817 prefixEnd_1659817 := by exact prefixLift 1659817
  have htrace : WordTrace (prefixWord ++ tailWord_1659817) baseStart_1659817 baseEnd_1659817 := by
    simpa [prefixWord, tailWord_1659817, baseEnd_1659817] using wordTrace_append hprefix tailTrace_1659817
  have hstable : (prefixWord ++ tailWord_1659817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659817).length < 2 ^ (prefixWord ++ tailWord_1659817).sum := by decide
  have hdescent : baseEnd_1659817 < baseStart_1659817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659986 : List Nat := [3, 2, 2, 1, 3, 2, 2, 6]
def baseStart_1659986 : Nat := 118140960795 + 1659986 * 2 ^ 59
def prefixEnd_1659986 : Nat := 4983230072969 + 3 ^ 40 * 1659986 * 2
def baseEnd_1659986 : Nat := 126277140405103337902351

theorem tailTrace_1659986 : CollatzResearch.WordTrace tailWord_1659986 prefixEnd_1659986 126277140405103337902351 := by
  unfold tailWord_1659986
  simp only [CollatzResearch.WordTrace]
  refine ⟨15136165841040424970769953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40363108909441133255386541 15136165841040424970769953)
  ·
    refine ⟨11352124380780318728077465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15136165841040424970769953 11352124380780318728077465)
    ·
      refine ⟨8514093285585239046058099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11352124380780318728077465 8514093285585239046058099)
      ·
        refine ⟨12771139928377858569087149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8514093285585239046058099 12771139928377858569087149)
        ·
          refine ⟨4789177473141696963407681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12771139928377858569087149 4789177473141696963407681)
          ·
            refine ⟨3591883104856272722555761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4789177473141696963407681 3591883104856272722555761)
            ·
              refine ⟨2693912328642204541916821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3591883104856272722555761 2693912328642204541916821)
              ·
                refine ⟨126277140405103337902351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2693912328642204541916821 126277140405103337902351)
                ·
                  rfl

theorem cell21_1659986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_1659986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1659986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1659986 prefixEnd_1659986 := by exact prefixLift 1659986
  have htrace : WordTrace (prefixWord ++ tailWord_1659986) baseStart_1659986 baseEnd_1659986 := by
    simpa [prefixWord, tailWord_1659986, baseEnd_1659986] using wordTrace_append hprefix tailTrace_1659986
  have hstable : (prefixWord ++ tailWord_1659986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659986).length < 2 ^ (prefixWord ++ tailWord_1659986).sum := by decide
  have hdescent : baseEnd_1659986 < baseStart_1659986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660093 : List Nat := [1, 4, 1, 2, 1, 1, 4, 4, 3]
def baseStart_1660093 : Nat := 118140960795 + 1660093 * 2 ^ 59
def prefixEnd_1660093 : Nat := 4983230072969 + 3 ^ 40 * 1660093 * 2
def baseEnd_1660093 : Nat := 378855840073101605423501

theorem tailTrace_1660093 : CollatzResearch.WordTrace tailWord_1660093 prefixEnd_1660093 378855840073101605423501 := by
  unfold tailWord_1660093
  simp only [CollatzResearch.WordTrace]
  refine ⟨60548565974774057157224933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40365710649849371438149955 60548565974774057157224933)
  ·
    refine ⟨11352856120270135716979675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60548565974774057157224933 11352856120270135716979675)
    ·
      refine ⟨17029284180405203575469513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11352856120270135716979675 17029284180405203575469513)
      ·
        refine ⟨12771963135303902681602135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17029284180405203575469513 12771963135303902681602135)
        ·
          refine ⟨19157944702955854022403203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12771963135303902681602135 19157944702955854022403203)
          ·
            refine ⟨28736917054433781033604805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19157944702955854022403203 28736917054433781033604805)
            ·
              refine ⟨5388171947706333943800901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28736917054433781033604805 5388171947706333943800901)
              ·
                refine ⟨1010282240194937614462669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5388171947706333943800901 1010282240194937614462669)
                ·
                  refine ⟨378855840073101605423501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1010282240194937614462669 378855840073101605423501)
                  ·
                    rfl

theorem cell21_1660093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_1660093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660093 prefixEnd_1660093 := by exact prefixLift 1660093
  have htrace : WordTrace (prefixWord ++ tailWord_1660093) baseStart_1660093 baseEnd_1660093 := by
    simpa [prefixWord, tailWord_1660093, baseEnd_1660093] using wordTrace_append hprefix tailTrace_1660093
  have hstable : (prefixWord ++ tailWord_1660093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660093).length < 2 ^ (prefixWord ++ tailWord_1660093).sum := by decide
  have hdescent : baseEnd_1660093 < baseStart_1660093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660200 : List Nat := [2, 1, 5, 1, 2, 2, 2, 2, 4]
def baseStart_1660200 : Nat := 118140960795 + 1660200 * 2 ^ 59
def prefixEnd_1660200 : Nat := 4983230072969 + 3 ^ 40 * 1660200 * 2
def baseEnd_1660200 : Nat := 378880258930893197139949

theorem tailTrace_1660200 : CollatzResearch.WordTrace tailWord_1660200 prefixEnd_1660200 378880258930893197139949 := by
  unfold tailWord_1660200
  simp only [CollatzResearch.WordTrace]
  refine ⟨30276234292693207215685027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40368312390257609620913369 30276234292693207215685027)
  ·
    refine ⟨45414351439039810823527541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30276234292693207215685027 45414351439039810823527541)
    ·
      refine ⟨4257595447409982264705707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45414351439039810823527541 4257595447409982264705707)
      ·
        refine ⟨6386393171114973397058561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4257595447409982264705707 6386393171114973397058561)
        ·
          refine ⟨4789794878336230047793921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6386393171114973397058561 4789794878336230047793921)
          ·
            refine ⟨3592346158752172535845441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4789794878336230047793921 3592346158752172535845441)
            ·
              refine ⟨2694259619064129401884081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3592346158752172535845441 2694259619064129401884081)
              ·
                refine ⟨2020694714298097051413061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694259619064129401884081 2020694714298097051413061)
                ·
                  refine ⟨378880258930893197139949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2020694714298097051413061 378880258930893197139949)
                  ·
                    rfl

theorem cell21_1660200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_1660200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660200 prefixEnd_1660200 := by exact prefixLift 1660200
  have htrace : WordTrace (prefixWord ++ tailWord_1660200) baseStart_1660200 baseEnd_1660200 := by
    simpa [prefixWord, tailWord_1660200, baseEnd_1660200] using wordTrace_append hprefix tailTrace_1660200
  have hstable : (prefixWord ++ tailWord_1660200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660200).length < 2 ^ (prefixWord ++ tailWord_1660200).sum := by decide
  have hdescent : baseEnd_1660200 < baseStart_1660200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660242 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 6]
def baseStart_1660242 : Nat := 118140960795 + 1660242 * 2 ^ 59
def prefixEnd_1660242 : Nat := 4983230072969 + 3 ^ 40 * 1660242 * 2
def baseEnd_1660242 : Nat := 378889843903110457439863

theorem tailTrace_1660242 : CollatzResearch.WordTrace tailWord_1660242 prefixEnd_1660242 378889843903110457439863 := by
  unfold tailWord_1660242
  simp only [CollatzResearch.WordTrace]
  refine ⟨15138500112808563901099745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40369333634156170402932653 15138500112808563901099745)
  ·
    refine ⟨11353875084606422925824809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15138500112808563901099745 11353875084606422925824809)
    ·
      refine ⟨8515406313454817194368607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11353875084606422925824809 8515406313454817194368607)
      ·
        refine ⟨12773109470182225791552911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8515406313454817194368607 12773109470182225791552911)
        ·
          refine ⟨19159664205273338687329367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12773109470182225791552911 19159664205273338687329367)
          ·
            refine ⟨28739496307910008030994051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19159664205273338687329367 28739496307910008030994051)
            ·
              refine ⟨43109244461865012046491077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28739496307910008030994051 43109244461865012046491077)
              ·
                refine ⟨8082983336599689758717077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43109244461865012046491077 8082983336599689758717077)
                ·
                  refine ⟨378889843903110457439863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8082983336599689758717077 378889843903110457439863)
                  ·
                    rfl

theorem cell21_1660242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_1660242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660242 prefixEnd_1660242 := by exact prefixLift 1660242
  have htrace : WordTrace (prefixWord ++ tailWord_1660242) baseStart_1660242 baseEnd_1660242 := by
    simpa [prefixWord, tailWord_1660242, baseEnd_1660242] using wordTrace_append hprefix tailTrace_1660242
  have hstable : (prefixWord ++ tailWord_1660242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660242).length < 2 ^ (prefixWord ++ tailWord_1660242).sum := by decide
  have hdescent : baseEnd_1660242 < baseStart_1660242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660245 : List Nat := [1, 3, 2, 2, 3, 1, 1, 5, 3]
def baseStart_1660245 : Nat := 118140960795 + 1660245 * 2 ^ 59
def prefixEnd_1660245 : Nat := 4983230072969 + 3 ^ 40 * 1660245 * 2
def baseEnd_1660245 : Nat := 378890528543983118889857

theorem tailTrace_1660245 : CollatzResearch.WordTrace tailWord_1660245 prefixEnd_1660245 378890528543983118889857 := by
  unfold tailWord_1660245
  simp only [CollatzResearch.WordTrace]
  refine ⟨60554109870223387116758189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40369406580148924744505459 60554109870223387116758189)
  ·
    refine ⟨22707791201333770168784321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60554109870223387116758189 22707791201333770168784321)
    ·
      refine ⟨17030843401000327626588241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22707791201333770168784321 17030843401000327626588241)
      ·
        refine ⟨12773132550750245719941181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17030843401000327626588241 12773132550750245719941181)
        ·
          refine ⟨4789924706531342144977943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12773132550750245719941181 4789924706531342144977943)
          ·
            refine ⟨7184887059797013217466915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4789924706531342144977943 7184887059797013217466915)
            ·
              refine ⟨10777330589695519826200373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7184887059797013217466915 10777330589695519826200373)
              ·
                refine ⟨1010374742783954983706285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10777330589695519826200373 1010374742783954983706285)
                ·
                  refine ⟨378890528543983118889857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1010374742783954983706285 378890528543983118889857)
                  ·
                    rfl

theorem cell21_1660245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_1660245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660245 prefixEnd_1660245 := by exact prefixLift 1660245
  have htrace : WordTrace (prefixWord ++ tailWord_1660245) baseStart_1660245 baseEnd_1660245 := by
    simpa [prefixWord, tailWord_1660245, baseEnd_1660245] using wordTrace_append hprefix tailTrace_1660245
  have hstable : (prefixWord ++ tailWord_1660245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660245).length < 2 ^ (prefixWord ++ tailWord_1660245).sum := by decide
  have hdescent : baseEnd_1660245 < baseStart_1660245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660259 : List Nat := [1, 1, 1, 5, 2, 2, 3, 2, 4]
def baseStart_1660259 : Nat := 118140960795 + 1660259 * 2 ^ 59
def prefixEnd_1660259 : Nat := 4983230072969 + 3 ^ 40 * 1660259 * 2
def baseEnd_1660259 : Nat := 378893723534722205656495

theorem tailTrace_1660259 : CollatzResearch.WordTrace tailWord_1660259 prefixEnd_1660259 378893723534722205656495 := by
  unfold tailWord_1660259
  simp only [CollatzResearch.WordTrace]
  refine ⟨60554620492172667507767831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40369746994781778338511887 60554620492172667507767831)
  ·
    refine ⟨90831930738259001261651747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60554620492172667507767831 90831930738259001261651747)
    ·
      refine ⟨136247896107388501892477621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90831930738259001261651747 136247896107388501892477621)
      ·
        refine ⟨12773240260067672052419777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136247896107388501892477621 12773240260067672052419777)
        ·
          refine ⟨9579930195050754039314833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12773240260067672052419777 9579930195050754039314833)
          ·
            refine ⟨7184947646288065529486125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9579930195050754039314833 7184947646288065529486125)
            ·
              refine ⟨2694355367358024573557297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7184947646288065529486125 2694355367358024573557297)
              ·
                refine ⟨2020766525518518430167973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694355367358024573557297 2020766525518518430167973)
                ·
                  refine ⟨378893723534722205656495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2020766525518518430167973 378893723534722205656495)
                  ·
                    rfl

theorem cell21_1660259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 4].length) (baseStart_1660259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660259 prefixEnd_1660259 := by exact prefixLift 1660259
  have htrace : WordTrace (prefixWord ++ tailWord_1660259) baseStart_1660259 baseEnd_1660259 := by
    simpa [prefixWord, tailWord_1660259, baseEnd_1660259] using wordTrace_append hprefix tailTrace_1660259
  have hstable : (prefixWord ++ tailWord_1660259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660259).length < 2 ^ (prefixWord ++ tailWord_1660259).sum := by decide
  have hdescent : baseEnd_1660259 < baseStart_1660259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660332 : List Nat := [2, 2, 1, 1, 1, 1, 5, 8]
def baseStart_1660332 : Nat := 118140960795 + 1660332 * 2 ^ 59
def prefixEnd_1660332 : Nat := 4983230072969 + 3 ^ 40 * 1660332 * 2
def baseEnd_1660332 : Nat := 126303461043096766979893

theorem tailTrace_1660332 : CollatzResearch.WordTrace tailWord_1660332 prefixEnd_1660332 126303461043096766979893 := by
  unfold tailWord_1660332
  simp only [CollatzResearch.WordTrace]
  refine ⟨30278641510454100487587625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40371522013938800650116833 30278641510454100487587625)
  ·
    refine ⟨22708981132840575365690719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30278641510454100487587625 22708981132840575365690719)
    ·
      refine ⟨34063471699260863048536079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22708981132840575365690719 34063471699260863048536079)
      ·
        refine ⟨51095207548891294572804119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34063471699260863048536079 51095207548891294572804119)
        ·
          refine ⟨76642811323336941859206179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51095207548891294572804119 76642811323336941859206179)
          ·
            refine ⟨114964216985005412788809269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76642811323336941859206179 114964216985005412788809269)
            ·
              refine ⟨10777895342344257448950869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114964216985005412788809269 10777895342344257448950869)
              ·
                refine ⟨126303461043096766979893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10777895342344257448950869 126303461043096766979893)
                ·
                  rfl

theorem cell21_1660332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 8].length) (baseStart_1660332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660332 prefixEnd_1660332 := by exact prefixLift 1660332
  have htrace : WordTrace (prefixWord ++ tailWord_1660332) baseStart_1660332 baseEnd_1660332 := by
    simpa [prefixWord, tailWord_1660332, baseEnd_1660332] using wordTrace_append hprefix tailTrace_1660332
  have hstable : (prefixWord ++ tailWord_1660332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660332).length < 2 ^ (prefixWord ++ tailWord_1660332).sum := by decide
  have hdescent : baseEnd_1660332 < baseStart_1660332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660372 : List Nat := [2, 4, 1, 2, 4, 1, 2, 2, 3]
def baseStart_1660372 : Nat := 118140960795 + 1660372 * 2 ^ 59
def prefixEnd_1660372 : Nat := 4983230072969 + 3 ^ 40 * 1660372 * 2
def baseEnd_1660372 : Nat := 378919511674259120272931

theorem tailTrace_1660372 : CollatzResearch.WordTrace tailWord_1660372 prefixEnd_1660372 378919511674259120272931 := by
  unfold tailWord_1660372
  simp only [CollatzResearch.WordTrace]
  refine ⟨30279370970381643903315685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40372494627175525204420913 30279370970381643903315685)
  ·
    refine ⟨5677382056946558231871691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30279370970381643903315685 5677382056946558231871691)
    ·
      refine ⟨8516073085419837347807537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5677382056946558231871691 8516073085419837347807537)
      ·
        refine ⟨6387054814064878010855653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8516073085419837347807537 6387054814064878010855653)
        ·
          refine ⟨1197572777637164627035435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6387054814064878010855653 1197572777637164627035435)
          ·
            refine ⟨1796359166455746940553153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197572777637164627035435 1796359166455746940553153)
            ·
              refine ⟨1347269374841810205414865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1796359166455746940553153 1347269374841810205414865)
              ·
                refine ⟨1010452031131357654061149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1347269374841810205414865 1010452031131357654061149)
                ·
                  refine ⟨378919511674259120272931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1010452031131357654061149 378919511674259120272931)
                  ·
                    rfl

theorem cell21_1660372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_1660372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660372 prefixEnd_1660372 := by exact prefixLift 1660372
  have htrace : WordTrace (prefixWord ++ tailWord_1660372) baseStart_1660372 baseEnd_1660372 := by
    simpa [prefixWord, tailWord_1660372, baseEnd_1660372] using wordTrace_append hprefix tailTrace_1660372
  have hstable : (prefixWord ++ tailWord_1660372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660372).length < 2 ^ (prefixWord ++ tailWord_1660372).sum := by decide
  have hdescent : baseEnd_1660372 < baseStart_1660372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660397 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1660397 : Nat := 118140960795 + 1660397 * 2 ^ 59
def prefixEnd_1660397 : Nat := 4983230072969 + 3 ^ 40 * 1660397 * 2
def baseEnd_1660397 : Nat := 378925217014864632356213

theorem tailTrace_1660397 : CollatzResearch.WordTrace tailWord_1660397 prefixEnd_1660397 378925217014864632356213 := by
  unfold tailWord_1660397
  simp only [CollatzResearch.WordTrace]
  refine ⟨60559653765672717076291445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40373102510448478050860963 60559653765672717076291445)
  ·
    refine ⟨5677467540531817225902323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60559653765672717076291445 5677467540531817225902323)
    ·
      refine ⟨8516201310797725838853485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5677467540531817225902323 8516201310797725838853485)
      ·
        refine ⟨3193575491549147189570057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8516201310797725838853485 3193575491549147189570057)
        ·
          refine ⟨2395181618661860392177543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3193575491549147189570057 2395181618661860392177543)
          ·
            refine ⟨3592772427992790588266315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2395181618661860392177543 3592772427992790588266315)
            ·
              refine ⟨5389158641989185882399473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3592772427992790588266315 5389158641989185882399473)
              ·
                refine ⟨4041868981491889411799605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5389158641989185882399473 4041868981491889411799605)
                ·
                  refine ⟨378925217014864632356213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4041868981491889411799605 378925217014864632356213)
                  ·
                    rfl

theorem cell21_1660397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1660397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660397 prefixEnd_1660397 := by exact prefixLift 1660397
  have htrace : WordTrace (prefixWord ++ tailWord_1660397) baseStart_1660397 baseEnd_1660397 := by
    simpa [prefixWord, tailWord_1660397, baseEnd_1660397] using wordTrace_append hprefix tailTrace_1660397
  have hstable : (prefixWord ++ tailWord_1660397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660397).length < 2 ^ (prefixWord ++ tailWord_1660397).sum := by decide
  have hdescent : baseEnd_1660397 < baseStart_1660397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660428 : List Nat := [2, 2, 1, 2, 5, 2, 1, 2, 4]
def baseStart_1660428 : Nat := 118140960795 + 1660428 * 2 ^ 59
def prefixEnd_1660428 : Nat := 4983230072969 + 3 ^ 40 * 1660428 * 2
def baseEnd_1660428 : Nat := 378932291637215467339483

theorem tailTrace_1660428 : CollatzResearch.WordTrace tailWord_1660428 prefixEnd_1660428 378932291637215467339483 := by
  unfold tailWord_1660428
  simp only [CollatzResearch.WordTrace]
  refine ⟨30280392214280204685334969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40373856285706939580446625 30280392214280204685334969)
  ·
    refine ⟨22710294160710153514001227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30280392214280204685334969 22710294160710153514001227)
    ·
      refine ⟨34065441241065230271001841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22710294160710153514001227 34065441241065230271001841)
      ·
        refine ⟨25549080930798922703251381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34065441241065230271001841 25549080930798922703251381)
        ·
          refine ⟨2395226337262399003429817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25549080930798922703251381 2395226337262399003429817)
          ·
            refine ⟨1796419752946799252572363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2395226337262399003429817 1796419752946799252572363)
            ·
              refine ⟨2694629629420198878858545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796419752946799252572363 2694629629420198878858545)
              ·
                refine ⟨2020972222065149159143909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694629629420198878858545 2020972222065149159143909)
                ·
                  refine ⟨378932291637215467339483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2020972222065149159143909 378932291637215467339483)
                  ·
                    rfl

theorem cell21_1660428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_1660428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660428 prefixEnd_1660428 := by exact prefixLift 1660428
  have htrace : WordTrace (prefixWord ++ tailWord_1660428) baseStart_1660428 baseEnd_1660428 := by
    simpa [prefixWord, tailWord_1660428, baseEnd_1660428] using wordTrace_append hprefix tailTrace_1660428
  have hstable : (prefixWord ++ tailWord_1660428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660428).length < 2 ^ (prefixWord ++ tailWord_1660428).sum := by decide
  have hdescent : baseEnd_1660428 < baseStart_1660428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660473 : List Nat := [1, 2, 1, 5, 1, 2, 3, 3, 3]
def baseStart_1660473 : Nat := 118140960795 + 1660473 * 2 ^ 59
def prefixEnd_1660473 : Nat := 4983230072969 + 3 ^ 40 * 1660473 * 2
def baseEnd_1660473 : Nat := 378942561250305389089391

theorem tailTrace_1660473 : CollatzResearch.WordTrace tailWord_1660473 prefixEnd_1660473 378942561250305389089391 := by
  unfold tailWord_1660473
  simp only [CollatzResearch.WordTrace]
  refine ⟨60562425713397382056058073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40374950475598254704038715 60562425713397382056058073)
  ·
    refine ⟨45421819285048036542043555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60562425713397382056058073 45421819285048036542043555)
    ·
      refine ⟨68132728927572054813065333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45421819285048036542043555 68132728927572054813065333)
      ·
        refine ⟨6387443336959880138724875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68132728927572054813065333 6387443336959880138724875)
        ·
          refine ⟨9581165005439820208087313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6387443336959880138724875 9581165005439820208087313)
          ·
            refine ⟨7185873754079865156065485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9581165005439820208087313 7185873754079865156065485)
            ·
              refine ⟨2694702657779949433524557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7185873754079865156065485 2694702657779949433524557)
              ·
                refine ⟨1010513496667481037571709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2694702657779949433524557 1010513496667481037571709)
                ·
                  refine ⟨378942561250305389089391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1010513496667481037571709 378942561250305389089391)
                  ·
                    rfl

theorem cell21_1660473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 3].length) (baseStart_1660473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660473 prefixEnd_1660473 := by exact prefixLift 1660473
  have htrace : WordTrace (prefixWord ++ tailWord_1660473) baseStart_1660473 baseEnd_1660473 := by
    simpa [prefixWord, tailWord_1660473, baseEnd_1660473] using wordTrace_append hprefix tailTrace_1660473
  have hstable : (prefixWord ++ tailWord_1660473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660473).length < 2 ^ (prefixWord ++ tailWord_1660473).sum := by decide
  have hdescent : baseEnd_1660473 < baseStart_1660473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660529 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 8]
def baseStart_1660529 : Nat := 118140960795 + 1660529 * 2 ^ 59
def prefixEnd_1660529 : Nat := 4983230072969 + 3 ^ 40 * 1660529 * 2
def baseEnd_1660529 : Nat := 378955341213261736155943

theorem tailTrace_1660529 : CollatzResearch.WordTrace tailWord_1660529 prefixEnd_1660529 378955341213261736155943 := by
  unfold tailWord_1660529
  simp only [CollatzResearch.WordTrace]
  refine ⟨60564468201194503620096641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40376312134129669080064427 60564468201194503620096641)
  ·
    refine ⟨45423351150895877715072481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60564468201194503620096641 45423351150895877715072481)
    ·
      refine ⟨34067513363171908286304361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45423351150895877715072481 34067513363171908286304361)
      ·
        refine ⟨25550635022378931214728271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34067513363171908286304361 25550635022378931214728271)
        ·
          refine ⟨38325952533568396822092407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25550635022378931214728271 38325952533568396822092407)
          ·
            refine ⟨57488928800352595233138611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38325952533568396822092407 57488928800352595233138611)
            ·
              refine ⟨86233393200528892849707917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57488928800352595233138611 86233393200528892849707917)
              ·
                refine ⟨32337522450198334818640469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86233393200528892849707917 32337522450198334818640469)
                ·
                  refine ⟨378955341213261736155943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32337522450198334818640469 378955341213261736155943)
                  ·
                    rfl

theorem cell21_1660529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_1660529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660529 prefixEnd_1660529 := by exact prefixLift 1660529
  have htrace : WordTrace (prefixWord ++ tailWord_1660529) baseStart_1660529 baseEnd_1660529 := by
    simpa [prefixWord, tailWord_1660529, baseEnd_1660529] using wordTrace_append hprefix tailTrace_1660529
  have hstable : (prefixWord ++ tailWord_1660529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660529).length < 2 ^ (prefixWord ++ tailWord_1660529).sum := by decide
  have hdescent : baseEnd_1660529 < baseStart_1660529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660597 : List Nat := [1, 3, 3, 3, 3, 1, 1, 2, 4]
def baseStart_1660597 : Nat := 118140960795 + 1660597 * 2 ^ 59
def prefixEnd_1660597 : Nat := 4983230072969 + 3 ^ 40 * 1660597 * 2
def baseEnd_1660597 : Nat := 378970859739708729022471

theorem tailTrace_1660597 : CollatzResearch.WordTrace tailWord_1660597 prefixEnd_1660597 378970859739708729022471 := by
  unfold tailWord_1660597
  simp only [CollatzResearch.WordTrace]
  refine ⟨60566948364948151233572045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40377965576632100822381363 60566948364948151233572045)
  ·
    refine ⟨22712605636855556712589517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60566948364948151233572045 22712605636855556712589517)
    ·
      refine ⟨8517227113820833767221069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22712605636855556712589517 8517227113820833767221069)
      ·
        refine ⟨3193960167682812662707901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8517227113820833767221069 3193960167682812662707901)
        ·
          refine ⟨1197735062881054748515463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3193960167682812662707901 1197735062881054748515463)
          ·
            refine ⟨1796602594321582122773195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197735062881054748515463 1796602594321582122773195)
            ·
              refine ⟨2694903891482373184159793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796602594321582122773195 2694903891482373184159793)
              ·
                refine ⟨2021177918611779888119845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694903891482373184159793 2021177918611779888119845)
                ·
                  refine ⟨378970859739708729022471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2021177918611779888119845 378970859739708729022471)
                  ·
                    rfl

theorem cell21_1660597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_1660597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660597 prefixEnd_1660597 := by exact prefixLift 1660597
  have htrace : WordTrace (prefixWord ++ tailWord_1660597) baseStart_1660597 baseEnd_1660597 := by
    simpa [prefixWord, tailWord_1660597, baseEnd_1660597] using wordTrace_append hprefix tailTrace_1660597
  have hstable : (prefixWord ++ tailWord_1660597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660597).length < 2 ^ (prefixWord ++ tailWord_1660597).sum := by decide
  have hdescent : baseEnd_1660597 < baseStart_1660597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660608 : List Nat := [2, 1, 1, 2, 4, 1, 1, 6, 3]
def baseStart_1660608 : Nat := 118140960795 + 1660608 * 2 ^ 59
def prefixEnd_1660608 : Nat := 4983230072969 + 3 ^ 40 * 1660608 * 2
def baseEnd_1660608 : Nat := 378973370089575154339115

theorem tailTrace_1660608 : CollatzResearch.WordTrace tailWord_1660608 prefixEnd_1660608 378973370089575154339115 := by
  unfold tailWord_1660608
  simp only [CollatzResearch.WordTrace]
  refine ⟨30283674783954150056111239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40378233045272200074814985 30283674783954150056111239)
  ·
    refine ⟨45425512175931225084166859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30283674783954150056111239 45425512175931225084166859)
    ·
      refine ⟨68138268263896837626250289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45425512175931225084166859 68138268263896837626250289)
      ·
        refine ⟨51103701197922628219687717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68138268263896837626250289 51103701197922628219687717)
        ·
          refine ⟨9581943974610492791191447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51103701197922628219687717 9581943974610492791191447)
          ·
            refine ⟨14372915961915739186787171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9581943974610492791191447 14372915961915739186787171)
            ·
              refine ⟨21559373942873608780180757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14372915961915739186787171 21559373942873608780180757)
              ·
                refine ⟨1010595653572200411570973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21559373942873608780180757 1010595653572200411570973)
                ·
                  refine ⟨378973370089575154339115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1010595653572200411570973 378973370089575154339115)
                  ·
                    rfl

theorem cell21_1660608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 3].length) (baseStart_1660608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660608 prefixEnd_1660608 := by exact prefixLift 1660608
  have htrace : WordTrace (prefixWord ++ tailWord_1660608) baseStart_1660608 baseEnd_1660608 := by
    simpa [prefixWord, tailWord_1660608, baseEnd_1660608] using wordTrace_append hprefix tailTrace_1660608
  have hstable : (prefixWord ++ tailWord_1660608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660608).length < 2 ^ (prefixWord ++ tailWord_1660608).sum := by decide
  have hdescent : baseEnd_1660608 < baseStart_1660608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660614 : List Nat := [6, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1660614 : Nat := 118140960795 + 1660614 * 2 ^ 59
def prefixEnd_1660614 : Nat := 4983230072969 + 3 ^ 40 * 1660614 * 2
def baseEnd_1660614 : Nat := 378974739371320477239103

theorem tailTrace_1660614 : CollatzResearch.WordTrace tailWord_1660614 prefixEnd_1660614 378974739371320477239103 := by
  unfold tailWord_1660614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1892736512683955098029403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40378378937257708757960597 1892736512683955098029403)
  ·
    refine ⟨2839104769025932647044105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1892736512683955098029403 2839104769025932647044105)
    ·
      refine ⟨2129328576769449485283079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2839104769025932647044105 2129328576769449485283079)
      ·
        refine ⟨3193992865154174227924619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2129328576769449485283079 3193992865154174227924619)
        ·
          refine ⟨4790989297731261341886929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3193992865154174227924619 4790989297731261341886929)
          ·
            refine ⟨3593241973298446006415197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4790989297731261341886929 3593241973298446006415197)
            ·
              refine ⟨1347465739986917252405699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3593241973298446006415197 1347465739986917252405699)
              ·
                refine ⟨2021198609980375878608549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1347465739986917252405699 2021198609980375878608549)
                ·
                  refine ⟨378974739371320477239103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2021198609980375878608549 378974739371320477239103)
                  ·
                    rfl

theorem cell21_1660614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1660614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660614 prefixEnd_1660614 := by exact prefixLift 1660614
  have htrace : WordTrace (prefixWord ++ tailWord_1660614) baseStart_1660614 baseEnd_1660614 := by
    simpa [prefixWord, tailWord_1660614, baseEnd_1660614] using wordTrace_append hprefix tailTrace_1660614
  have hstable : (prefixWord ++ tailWord_1660614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660614).length < 2 ^ (prefixWord ++ tailWord_1660614).sum := by decide
  have hdescent : baseEnd_1660614 < baseStart_1660614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660653 : List Nat := [1, 5, 1, 2, 1, 4, 7]
def baseStart_1660653 : Nat := 118140960795 + 1660653 * 2 ^ 59
def prefixEnd_1660653 : Nat := 4983230072969 + 3 ^ 40 * 1660653 * 2
def baseEnd_1660653 : Nat := 42109293300296119565447

theorem tailTrace_1660653 : CollatzResearch.WordTrace tailWord_1660653 prefixEnd_1660653 42109293300296119565447 := by
  unfold tailWord_1660653
  simp only [CollatzResearch.WordTrace]
  refine ⟨60568990852745272797610613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40379327235163515198407075 60568990852745272797610613)
  ·
    refine ⟨5678342892444869324775995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60568990852745272797610613 5678342892444869324775995)
    ·
      refine ⟨8517514338667303987163993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5678342892444869324775995 8517514338667303987163993)
      ·
        refine ⟨6388135754000477990372995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8517514338667303987163993 6388135754000477990372995)
        ·
          refine ⟨9582203631000716985559493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6388135754000477990372995 9582203631000716985559493)
          ·
            refine ⟨1796663180812634434792405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9582203631000716985559493 1796663180812634434792405)
            ·
              refine ⟨42109293300296119565447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1796663180812634434792405 42109293300296119565447)
              ·
                rfl

theorem cell21_1660653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 7].length) (baseStart_1660653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660653 prefixEnd_1660653 := by exact prefixLift 1660653
  have htrace : WordTrace (prefixWord ++ tailWord_1660653) baseStart_1660653 baseEnd_1660653 := by
    simpa [prefixWord, tailWord_1660653, baseEnd_1660653] using wordTrace_append hprefix tailTrace_1660653
  have hstable : (prefixWord ++ tailWord_1660653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660653).length < 2 ^ (prefixWord ++ tailWord_1660653).sum := by decide
  have hdescent : baseEnd_1660653 < baseStart_1660653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660670 : List Nat := [4, 2, 2, 1, 3, 1, 2, 6]
def baseStart_1660670 : Nat := 118140960795 + 1660670 * 2 ^ 59
def prefixEnd_1660670 : Nat := 4983230072969 + 3 ^ 40 * 1660670 * 2
def baseEnd_1660670 : Nat := 126329173111425608101885

theorem tailTrace_1660670 : CollatzResearch.WordTrace tailWord_1660670 prefixEnd_1660670 126329173111425608101885 := by
  unfold tailWord_1660670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7571201361710460587622433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40379740595789123133986309 7571201361710460587622433)
  ·
    refine ⟨5678401021282845440716825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7571201361710460587622433 5678401021282845440716825)
    ·
      refine ⟨4258800765962134080537619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5678401021282845440716825 4258800765962134080537619)
      ·
        refine ⟨6388201148943201120806429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4258800765962134080537619 6388201148943201120806429)
        ·
          refine ⟨2395575430853700420302411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6388201148943201120806429 2395575430853700420302411)
          ·
            refine ⟨3593363146280550630453617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2395575430853700420302411 3593363146280550630453617)
            ·
              refine ⟨2695022359710412972840213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3593363146280550630453617 2695022359710412972840213)
              ·
                refine ⟨126329173111425608101885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2695022359710412972840213 126329173111425608101885)
                ·
                  rfl

theorem cell21_1660670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_1660670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660670 prefixEnd_1660670 := by exact prefixLift 1660670
  have htrace : WordTrace (prefixWord ++ tailWord_1660670) baseStart_1660670 baseEnd_1660670 := by
    simpa [prefixWord, tailWord_1660670, baseEnd_1660670] using wordTrace_append hprefix tailTrace_1660670
  have hstable : (prefixWord ++ tailWord_1660670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660670).length < 2 ^ (prefixWord ++ tailWord_1660670).sum := by decide
  have hdescent : baseEnd_1660670 < baseStart_1660670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660712 : List Nat := [2, 1, 5, 1, 1, 11]
def baseStart_1660712 : Nat := 118140960795 + 1660712 * 2 ^ 59
def prefixEnd_1660712 : Nat := 4983230072969 + 3 ^ 40 * 1660712 * 2
def baseEnd_1660712 : Nat := 14036929789129410540947

theorem tailTrace_1660712 : CollatzResearch.WordTrace tailWord_1660712 prefixEnd_1660712 14036929789129410540947 := by
  unfold tailWord_1660712
  simp only [CollatzResearch.WordTrace]
  refine ⟨30285571379765762937004195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40380761839687683916005593 30285571379765762937004195)
  ·
    refine ⟨45428357069648644405506293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30285571379765762937004195 45428357069648644405506293)
    ·
      refine ⟨4258908475279560413016215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45428357069648644405506293 4258908475279560413016215)
      ·
        refine ⟨6388362712919340619524323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4258908475279560413016215 6388362712919340619524323)
        ·
          refine ⟨9582544069379010929286485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6388362712919340619524323 9582544069379010929286485)
          ·
            refine ⟨14036929789129410540947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9582544069379010929286485 14036929789129410540947)
            ·
              rfl

theorem cell21_1660712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 11].length) (baseStart_1660712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660712 prefixEnd_1660712 := by exact prefixLift 1660712
  have htrace : WordTrace (prefixWord ++ tailWord_1660712) baseStart_1660712 baseEnd_1660712 := by
    simpa [prefixWord, tailWord_1660712, baseEnd_1660712] using wordTrace_append hprefix tailTrace_1660712
  have hstable : (prefixWord ++ tailWord_1660712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660712).length < 2 ^ (prefixWord ++ tailWord_1660712).sum := by decide
  have hdescent : baseEnd_1660712 < baseStart_1660712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660718 : List Nat := [4, 1, 3, 2, 2, 1, 1, 4, 3]
def baseStart_1660718 : Nat := 118140960795 + 1660718 * 2 ^ 59
def prefixEnd_1660718 : Nat := 4983230072969 + 3 ^ 40 * 1660718 * 2
def baseEnd_1660718 : Nat := 378998473588239407505557

theorem tailTrace_1660718 : CollatzResearch.WordTrace tailWord_1660718 prefixEnd_1660718 378998473588239407505557 := by
  unfold tailWord_1660718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7571420199688723612340851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40380907731673192599151205 7571420199688723612340851)
  ·
    refine ⟨11357130299533085418511277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7571420199688723612340851 11357130299533085418511277)
    ·
      refine ⟨4258923862324907031941729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11357130299533085418511277 4258923862324907031941729)
      ·
        refine ⟨3194192896743680273956297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4258923862324907031941729 3194192896743680273956297)
        ·
          refine ⟨2395644672557760205467223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3194192896743680273956297 2395644672557760205467223)
          ·
            refine ⟨3593467008836640308200835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2395644672557760205467223 3593467008836640308200835)
            ·
              refine ⟨5390200513254960462301253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3593467008836640308200835 5390200513254960462301253)
              ·
                refine ⟨1010662596235305086681485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5390200513254960462301253 1010662596235305086681485)
                ·
                  refine ⟨378998473588239407505557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1010662596235305086681485 378998473588239407505557)
                  ·
                    rfl

theorem cell21_1660718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_1660718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660718 prefixEnd_1660718 := by exact prefixLift 1660718
  have htrace : WordTrace (prefixWord ++ tailWord_1660718) baseStart_1660718 baseEnd_1660718 := by
    simpa [prefixWord, tailWord_1660718, baseEnd_1660718] using wordTrace_append hprefix tailTrace_1660718
  have hstable : (prefixWord ++ tailWord_1660718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660718).length < 2 ^ (prefixWord ++ tailWord_1660718).sum := by decide
  have hdescent : baseEnd_1660718 < baseStart_1660718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660836 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 5]
def baseStart_1660836 : Nat := 118140960795 + 1660836 * 2 ^ 59
def prefixEnd_1660836 : Nat := 4983230072969 + 3 ^ 40 * 1660836 * 2
def baseEnd_1660836 : Nat := 379025402795897424538649

theorem tailTrace_1660836 : CollatzResearch.WordTrace tailWord_1660836 prefixEnd_1660836 379025402795897424538649 := by
  unfold tailWord_1660836
  simp only [CollatzResearch.WordTrace]
  refine ⟨30287832705541147525761181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40383776940721530034348241 30287832705541147525761181)
  ·
    refine ⟨11357937264577930322160443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30287832705541147525761181 11357937264577930322160443)
    ·
      refine ⟨17036905896866895483240665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11357937264577930322160443 17036905896866895483240665)
      ·
        refine ⟨12777679422650171612430499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17036905896866895483240665 12777679422650171612430499)
        ·
          refine ⟨19166519133975257418645749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12777679422650171612430499 19166519133975257418645749)
          ·
            refine ⟨1796861168810180382998039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19166519133975257418645749 1796861168810180382998039)
            ·
              refine ⟨2695291753215270574497059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796861168810180382998039 2695291753215270574497059)
              ·
                refine ⟨4042937629822905861745589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2695291753215270574497059 4042937629822905861745589)
                ·
                  refine ⟨379025402795897424538649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4042937629822905861745589 379025402795897424538649)
                  ·
                    rfl

theorem cell21_1660836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_1660836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660836 prefixEnd_1660836 := by exact prefixLift 1660836
  have htrace : WordTrace (prefixWord ++ tailWord_1660836) baseStart_1660836 baseEnd_1660836 := by
    simpa [prefixWord, tailWord_1660836, baseEnd_1660836] using wordTrace_append hprefix tailTrace_1660836
  have hstable : (prefixWord ++ tailWord_1660836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660836).length < 2 ^ (prefixWord ++ tailWord_1660836).sum := by decide
  have hdescent : baseEnd_1660836 < baseStart_1660836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660923 : List Nat := [1, 1, 1, 1, 1, 3, 4, 9]
def baseStart_1660923 : Nat := 118140960795 + 1660923 * 2 ^ 59
def prefixEnd_1660923 : Nat := 4983230072969 + 3 ^ 40 * 1660923 * 2
def baseEnd_1660923 : Nat := 126348419127068202196157

theorem tailTrace_1660923 : CollatzResearch.WordTrace tailWord_1660923 prefixEnd_1660923 126348419127068202196157 := by
  unfold tailWord_1660923
  simp only [CollatzResearch.WordTrace]
  refine ⟨60578838561767108909939423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40385892374511405939959615 60578838561767108909939423)
  ·
    refine ⟨90868257842650663364909135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60578838561767108909939423 90868257842650663364909135)
    ·
      refine ⟨136302386763975995047363703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90868257842650663364909135 136302386763975995047363703)
      ·
        refine ⟨204453580145963992571045555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136302386763975995047363703 204453580145963992571045555)
        ·
          refine ⟨306680370218945988856568333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204453580145963992571045555 306680370218945988856568333)
          ·
            refine ⟨115005138832104745821213125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306680370218945988856568333 115005138832104745821213125)
            ·
              refine ⟨21563463531019639841477461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115005138832104745821213125 21563463531019639841477461)
              ·
                refine ⟨126348419127068202196157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21563463531019639841477461 126348419127068202196157)
                ·
                  rfl

theorem cell21_1660923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 9].length) (baseStart_1660923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660923 prefixEnd_1660923 := by exact prefixLift 1660923
  have htrace : WordTrace (prefixWord ++ tailWord_1660923) baseStart_1660923 baseEnd_1660923 := by
    simpa [prefixWord, tailWord_1660923, baseEnd_1660923] using wordTrace_append hprefix tailTrace_1660923
  have hstable : (prefixWord ++ tailWord_1660923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660923).length < 2 ^ (prefixWord ++ tailWord_1660923).sum := by decide
  have hdescent : baseEnd_1660923 < baseStart_1660923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660974 : List Nat := [4, 1, 3, 1, 1, 4, 2, 5]
def baseStart_1660974 : Nat := 118140960795 + 1660974 * 2 ^ 59
def prefixEnd_1660974 : Nat := 4983230072969 + 3 ^ 40 * 1660974 * 2
def baseEnd_1660974 : Nat := 126352298758679950412789

theorem tailTrace_1660974 : CollatzResearch.WordTrace tailWord_1660974 prefixEnd_1660974 126352298758679950412789 := by
  unfold tailWord_1660974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7572587335572793077505747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40387132456388229746697317 7572587335572793077505747)
  ·
    refine ⟨11358881003359189616258621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7572587335572793077505747 11358881003359189616258621)
    ·
      refine ⟨4259580376259696106096983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11358881003359189616258621 4259580376259696106096983)
      ·
        refine ⟨6389370564389544159145475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4259580376259696106096983 6389370564389544159145475)
        ·
          refine ⟨9584055846584316238718213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6389370564389544159145475 9584055846584316238718213)
          ·
            refine ⟨1797010471234559294759665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9584055846584316238718213 1797010471234559294759665)
            ·
              refine ⟨1347757853425919471069749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797010471234559294759665 1347757853425919471069749)
              ·
                refine ⟨126352298758679950412789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1347757853425919471069749 126352298758679950412789)
                ·
                  rfl

theorem cell21_1660974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_1660974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1660974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1660974 prefixEnd_1660974 := by exact prefixLift 1660974
  have htrace : WordTrace (prefixWord ++ tailWord_1660974) baseStart_1660974 baseEnd_1660974 := by
    simpa [prefixWord, tailWord_1660974, baseEnd_1660974] using wordTrace_append hprefix tailTrace_1660974
  have hstable : (prefixWord ++ tailWord_1660974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660974).length < 2 ^ (prefixWord ++ tailWord_1660974).sum := by decide
  have hdescent : baseEnd_1660974 < baseStart_1660974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661016 : List Nat := [2, 1, 2, 2, 1, 5, 2, 6]
def baseStart_1661016 : Nat := 118140960795 + 1661016 * 2 ^ 59
def prefixEnd_1661016 : Nat := 4983230072969 + 3 ^ 40 * 1661016 * 2
def baseEnd_1661016 : Nat := 126355493749419037179427

theorem tailTrace_1661016 : CollatzResearch.WordTrace tailWord_1661016 prefixEnd_1661016 126355493749419037179427 := by
  unfold tailWord_1661016
  simp only [CollatzResearch.WordTrace]
  refine ⟨30291115275215092896537451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40388153700286790528716601 30291115275215092896537451)
  ·
    refine ⟨45436672912822639344806177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30291115275215092896537451 45436672912822639344806177)
    ·
      refine ⟨34077504684616979508604633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45436672912822639344806177 34077504684616979508604633)
      ·
        refine ⟨25558128513462734631453475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34077504684616979508604633 25558128513462734631453475)
        ·
          refine ⟨38337192770194101947180213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25558128513462734631453475 38337192770194101947180213)
          ·
            refine ⟨3594111822205697057548145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38337192770194101947180213 3594111822205697057548145)
            ·
              refine ⟨2695583866654272793161109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3594111822205697057548145 2695583866654272793161109)
              ·
                refine ⟨126355493749419037179427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2695583866654272793161109 126355493749419037179427)
                ·
                  rfl

theorem cell21_1661016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 6].length) (baseStart_1661016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661016 prefixEnd_1661016 := by exact prefixLift 1661016
  have htrace : WordTrace (prefixWord ++ tailWord_1661016) baseStart_1661016 baseEnd_1661016 := by
    simpa [prefixWord, tailWord_1661016, baseEnd_1661016] using wordTrace_append hprefix tailTrace_1661016
  have hstable : (prefixWord ++ tailWord_1661016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661016).length < 2 ^ (prefixWord ++ tailWord_1661016).sum := by decide
  have hdescent : baseEnd_1661016 < baseStart_1661016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661098 : List Nat := [3, 1, 5, 1, 2, 1, 2, 3, 3]
def baseStart_1661098 : Nat := 118140960795 + 1661098 * 2 ^ 59
def prefixEnd_1661098 : Nat := 4983230072969 + 3 ^ 40 * 1661098 * 2
def baseEnd_1661098 : Nat := 379085194765443191171447

theorem tailTrace_1661098 : CollatzResearch.WordTrace tailWord_1661098 prefixEnd_1661098 379085194765443191171447 := by
  unfold tailWord_1661098
  simp only [CollatzResearch.WordTrace]
  refine ⟨15146305334033278449389987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40390147557422075865039965 15146305334033278449389987)
  ·
    refine ⟨22719458001049917674084981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15146305334033278449389987 22719458001049917674084981)
    ·
      refine ⟨2129949187598429781945467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22719458001049917674084981 2129949187598429781945467)
      ·
        refine ⟨3194923781397644672918201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2129949187598429781945467 3194923781397644672918201)
        ·
          refine ⟨2396192836048233504688651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3194923781397644672918201 2396192836048233504688651)
          ·
            refine ⟨3594289254072350257032977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2396192836048233504688651 3594289254072350257032977)
            ·
              refine ⟨2695716940554262692774733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3594289254072350257032977 2695716940554262692774733)
              ·
                refine ⟨1010893852707848509790525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2695716940554262692774733 1010893852707848509790525)
                ·
                  refine ⟨379085194765443191171447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1010893852707848509790525 379085194765443191171447)
                  ·
                    rfl

theorem cell21_1661098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_1661098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661098 prefixEnd_1661098 := by exact prefixLift 1661098
  have htrace : WordTrace (prefixWord ++ tailWord_1661098) baseStart_1661098 baseEnd_1661098 := by
    simpa [prefixWord, tailWord_1661098, baseEnd_1661098] using wordTrace_append hprefix tailTrace_1661098
  have hstable : (prefixWord ++ tailWord_1661098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661098).length < 2 ^ (prefixWord ++ tailWord_1661098).sum := by decide
  have hdescent : baseEnd_1661098 < baseStart_1661098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661106 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 7]
def baseStart_1661106 : Nat := 118140960795 + 1661106 * 2 ^ 59
def prefixEnd_1661106 : Nat := 4983230072969 + 3 ^ 40 * 1661106 * 2
def baseEnd_1661106 : Nat := 379087020474436955038097

theorem tailTrace_1661106 : CollatzResearch.WordTrace tailWord_1661106 prefixEnd_1661106 379087020474436955038097 := by
  unfold tailWord_1661106
  simp only [CollatzResearch.WordTrace]
  refine ⟨15146378280026032790962793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40390342080069420775900781 15146378280026032790962793)
  ·
    refine ⟨11359783710019524593222095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15146378280026032790962793 11359783710019524593222095)
    ·
      refine ⟨17039675565029286889833143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11359783710019524593222095 17039675565029286889833143)
      ·
        refine ⟨25559513347543930334749715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17039675565029286889833143 25559513347543930334749715)
        ·
          refine ⟨38339270021315895502124573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25559513347543930334749715 38339270021315895502124573)
          ·
            refine ⟨14377226257993460813296715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38339270021315895502124573 14377226257993460813296715)
            ·
              refine ⟨21565839386990191219945073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14377226257993460813296715 21565839386990191219945073)
              ·
                refine ⟨16174379540242643414958805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21565839386990191219945073 16174379540242643414958805)
                ·
                  refine ⟨379087020474436955038097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16174379540242643414958805 379087020474436955038097)
                  ·
                    rfl

theorem cell21_1661106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_1661106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661106 prefixEnd_1661106 := by exact prefixLift 1661106
  have htrace : WordTrace (prefixWord ++ tailWord_1661106) baseStart_1661106 baseEnd_1661106 := by
    simpa [prefixWord, tailWord_1661106, baseEnd_1661106] using wordTrace_append hprefix tailTrace_1661106
  have hstable : (prefixWord ++ tailWord_1661106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661106).length < 2 ^ (prefixWord ++ tailWord_1661106).sum := by decide
  have hdescent : baseEnd_1661106 < baseStart_1661106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661109 : List Nat := [1, 3, 3, 4, 1, 1, 8]
def baseStart_1661109 : Nat := 118140960795 + 1661109 * 2 ^ 59
def prefixEnd_1661109 : Nat := 4983230072969 + 3 ^ 40 * 1661109 * 2
def baseEnd_1661109 : Nat := 42120856123923290720899

theorem tailTrace_1661109 : CollatzResearch.WordTrace tailWord_1661109 prefixEnd_1661109 42120856123923290720899 := by
  unfold tailWord_1661109
  simp only [CollatzResearch.WordTrace]
  refine ⟨60585622539093262676210381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40390415026062175117473587 60585622539093262676210381)
  ·
    refine ⟨22719608452159973503578893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60585622539093262676210381 22719608452159973503578893)
    ·
      refine ⟨8519853169559990063842085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22719608452159973503578893 8519853169559990063842085)
      ·
        refine ⟨1597472469292498136970391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8519853169559990063842085 1597472469292498136970391)
        ·
          refine ⟨2396208703938747205455587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1597472469292498136970391 2396208703938747205455587)
          ·
            refine ⟨3594313055908120808183381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2396208703938747205455587 3594313055908120808183381)
            ·
              refine ⟨42120856123923290720899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3594313055908120808183381 42120856123923290720899)
              ·
                rfl

theorem cell21_1661109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 8].length) (baseStart_1661109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661109 prefixEnd_1661109 := by exact prefixLift 1661109
  have htrace : WordTrace (prefixWord ++ tailWord_1661109) baseStart_1661109 baseEnd_1661109 := by
    simpa [prefixWord, tailWord_1661109, baseEnd_1661109] using wordTrace_append hprefix tailTrace_1661109
  have hstable : (prefixWord ++ tailWord_1661109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661109).length < 2 ^ (prefixWord ++ tailWord_1661109).sum := by decide
  have hdescent : baseEnd_1661109 < baseStart_1661109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661137 : List Nat := [1, 2, 2, 1, 2, 2, 2, 5, 4]
def baseStart_1661137 : Nat := 118140960795 + 1661137 * 2 ^ 59
def prefixEnd_1661137 : Nat := 4983230072969 + 3 ^ 40 * 1661137 * 2
def baseEnd_1661137 : Nat := 379094095096787790021367

theorem tailTrace_1661137 : CollatzResearch.WordTrace tailWord_1661137 prefixEnd_1661137 379094095096787790021367 := by
  unfold tailWord_1661137
  simp only [CollatzResearch.WordTrace]
  refine ⟨60586643782991823458229665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40391095855327882305486443 60586643782991823458229665)
  ·
    refine ⟨45439982837243867593672249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60586643782991823458229665 45439982837243867593672249)
    ·
      refine ⟨34079987127932900695254187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45439982837243867593672249 34079987127932900695254187)
      ·
        refine ⟨51119980691899351042881281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34079987127932900695254187 51119980691899351042881281)
        ·
          refine ⟨38339985518924513282160961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51119980691899351042881281 38339985518924513282160961)
          ·
            refine ⟨28754989139193384961620721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38339985518924513282160961 28754989139193384961620721)
            ·
              refine ⟨21566241854395038721215541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28754989139193384961620721 21566241854395038721215541)
              ·
                refine ⟨2021835173849534880113957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21566241854395038721215541 2021835173849534880113957)
                ·
                  refine ⟨379094095096787790021367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2021835173849534880113957 379094095096787790021367)
                  ·
                    rfl

theorem cell21_1661137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_1661137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661137 prefixEnd_1661137 := by exact prefixLift 1661137
  have htrace : WordTrace (prefixWord ++ tailWord_1661137) baseStart_1661137 baseEnd_1661137 := by
    simpa [prefixWord, tailWord_1661137, baseEnd_1661137] using wordTrace_append hprefix tailTrace_1661137
  have hstable : (prefixWord ++ tailWord_1661137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661137).length < 2 ^ (prefixWord ++ tailWord_1661137).sum := by decide
  have hdescent : baseEnd_1661137 < baseStart_1661137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661157 : List Nat := [1, 3, 1, 4, 2, 3, 1, 3, 3]
def baseStart_1661157 : Nat := 118140960795 + 1661157 * 2 ^ 59
def prefixEnd_1661157 : Nat := 4983230072969 + 3 ^ 40 * 1661157 * 2
def baseEnd_1661157 : Nat := 379098659369272199687993

theorem tailTrace_1661157 : CollatzResearch.WordTrace tailWord_1661157 prefixEnd_1661157 379098659369272199687993 := by
  unfold tailWord_1661157
  simp only [CollatzResearch.WordTrace]
  refine ⟨60587373242919366873957725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40391582161946244582638483 60587373242919366873957725)
  ·
    refine ⟨22720264966094762577734147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60587373242919366873957725 22720264966094762577734147)
    ·
      refine ⟨34080397449142143866601221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22720264966094762577734147 34080397449142143866601221)
      ·
        refine ⟨6390074521714151974987729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34080397449142143866601221 6390074521714151974987729)
        ·
          refine ⟨4792555891285613981240797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6390074521714151974987729 4792555891285613981240797)
          ·
            refine ⟨1797208459232105242965299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4792555891285613981240797 1797208459232105242965299)
            ·
              refine ⟨2695812688848157864447949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797208459232105242965299 2695812688848157864447949)
              ·
                refine ⟨1010929758318059199167981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2695812688848157864447949 1010929758318059199167981)
                ·
                  refine ⟨379098659369272199687993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1010929758318059199167981 379098659369272199687993)
                  ·
                    rfl

theorem cell21_1661157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_1661157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661157 prefixEnd_1661157 := by exact prefixLift 1661157
  have htrace : WordTrace (prefixWord ++ tailWord_1661157) baseStart_1661157 baseEnd_1661157 := by
    simpa [prefixWord, tailWord_1661157, baseEnd_1661157] using wordTrace_append hprefix tailTrace_1661157
  have hstable : (prefixWord ++ tailWord_1661157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661157).length < 2 ^ (prefixWord ++ tailWord_1661157).sum := by decide
  have hdescent : baseEnd_1661157 < baseStart_1661157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661188 : List Nat := [2, 3, 2, 2, 3, 2, 2, 1, 4]
def baseStart_1661188 : Nat := 118140960795 + 1661188 * 2 ^ 59
def prefixEnd_1661188 : Nat := 4983230072969 + 3 ^ 40 * 1661188 * 2
def baseEnd_1661188 : Nat := 379105733991623034671263

theorem tailTrace_1661188 : CollatzResearch.WordTrace tailWord_1661188 prefixEnd_1661188 379105733991623034671263 := by
  unfold tailWord_1661188
  simp only [CollatzResearch.WordTrace]
  refine ⟨30294251952903529584168109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40392335937204706112224145 30294251952903529584168109)
  ·
    refine ⟨11360344482338823594063041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30294251952903529584168109 11360344482338823594063041)
    ·
      refine ⟨8520258361754117695547281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11360344482338823594063041 8520258361754117695547281)
      ·
        refine ⟨6390193771315588271660461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8520258361754117695547281 6390193771315588271660461)
        ·
          refine ⟨2396322664243345601872673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6390193771315588271660461 2396322664243345601872673)
          ·
            refine ⟨1797241998182509201404505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2396322664243345601872673 1797241998182509201404505)
            ·
              refine ⟨1347931498636881901053379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797241998182509201404505 1347931498636881901053379)
              ·
                refine ⟨2021897247955322851580069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1347931498636881901053379 2021897247955322851580069)
                ·
                  refine ⟨379105733991623034671263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2021897247955322851580069 379105733991623034671263)
                  ·
                    rfl

theorem cell21_1661188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_1661188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661188 prefixEnd_1661188 := by exact prefixLift 1661188
  have htrace : WordTrace (prefixWord ++ tailWord_1661188) baseStart_1661188 baseEnd_1661188 := by
    simpa [prefixWord, tailWord_1661188, baseEnd_1661188] using wordTrace_append hprefix tailTrace_1661188
  have hstable : (prefixWord ++ tailWord_1661188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661188).length < 2 ^ (prefixWord ++ tailWord_1661188).sum := by decide
  have hdescent : baseEnd_1661188 < baseStart_1661188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661351 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 5]
def baseStart_1661351 : Nat := 118140960795 + 1661351 * 2 ^ 59
def prefixEnd_1661351 : Nat := 4983230072969 + 3 ^ 40 * 1661351 * 2
def baseEnd_1661351 : Nat := 379142932812370973454263

theorem tailTrace_1661351 : CollatzResearch.WordTrace tailWord_1661351 prefixEnd_1661351 379142932812370973454263 := by
  unfold tailWord_1661351
  simp only [CollatzResearch.WordTrace]
  refine ⟨60594449004216538006519907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40396299336144358671013271 60594449004216538006519907)
  ·
    refine ⟨90891673506324807009779861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60594449004216538006519907 90891673506324807009779861)
    ·
      refine ⟨4260547195608975328583431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90891673506324807009779861 4260547195608975328583431)
      ·
        refine ⟨6390820793413462992875147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4260547195608975328583431 6390820793413462992875147)
        ·
          refine ⟨9586231190120194489312721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6390820793413462992875147 9586231190120194489312721)
          ·
            refine ⟨7189673392590145866984541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9586231190120194489312721 7189673392590145866984541)
            ·
              refine ⟨2696127522221304700119203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7189673392590145866984541 2696127522221304700119203)
              ·
                refine ⟨4044191283331957050178805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2696127522221304700119203 4044191283331957050178805)
                ·
                  refine ⟨379142932812370973454263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4044191283331957050178805 379142932812370973454263)
                  ·
                    rfl

theorem cell21_1661351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 5].length) (baseStart_1661351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661351 prefixEnd_1661351 := by exact prefixLift 1661351
  have htrace : WordTrace (prefixWord ++ tailWord_1661351) baseStart_1661351 baseEnd_1661351 := by
    simpa [prefixWord, tailWord_1661351, baseEnd_1661351] using wordTrace_append hprefix tailTrace_1661351
  have hstable : (prefixWord ++ tailWord_1661351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661351).length < 2 ^ (prefixWord ++ tailWord_1661351).sum := by decide
  have hdescent : baseEnd_1661351 < baseStart_1661351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661357 : List Nat := [1, 5, 2, 2, 3, 1, 2, 1, 4]
def baseStart_1661357 : Nat := 118140960795 + 1661357 * 2 ^ 59
def prefixEnd_1661357 : Nat := 4983230072969 + 3 ^ 40 * 1661357 * 2
def baseEnd_1661357 : Nat := 379144302094116296354251

theorem tailTrace_1661357 : CollatzResearch.WordTrace tailWord_1661357 prefixEnd_1661357 379144302094116296354251 := by
  unfold tailWord_1661357
  simp only [CollatzResearch.WordTrace]
  refine ⟨60594667842194801031238325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40396445228129867354158883 60594667842194801031238325)
  ·
    refine ⟨5680750110205762596678593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60594667842194801031238325 5680750110205762596678593)
    ·
      refine ⟨4260562582654321947508945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5680750110205762596678593 4260562582654321947508945)
      ·
        refine ⟨3195421936990741460631709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4260562582654321947508945 3195421936990741460631709)
        ·
          refine ⟨1198283226371528047736891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3195421936990741460631709 1198283226371528047736891)
          ·
            refine ⟨1797424839557292071605337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198283226371528047736891 1797424839557292071605337)
            ·
              refine ⟨1348068629667969053704003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797424839557292071605337 1348068629667969053704003)
              ·
                refine ⟨2022102944501953580556005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1348068629667969053704003 2022102944501953580556005)
                ·
                  refine ⟨379144302094116296354251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2022102944501953580556005 379144302094116296354251)
                  ·
                    rfl

theorem cell21_1661357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_1661357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661357 prefixEnd_1661357 := by exact prefixLift 1661357
  have htrace : WordTrace (prefixWord ++ tailWord_1661357) baseStart_1661357 baseEnd_1661357 := by
    simpa [prefixWord, tailWord_1661357, baseEnd_1661357] using wordTrace_append hprefix tailTrace_1661357
  have hstable : (prefixWord ++ tailWord_1661357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661357).length < 2 ^ (prefixWord ++ tailWord_1661357).sum := by decide
  have hdescent : baseEnd_1661357 < baseStart_1661357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661413 : List Nat := [1, 3, 1, 5, 2, 2, 1, 6]
def baseStart_1661413 : Nat := 118140960795 + 1661413 * 2 ^ 59
def prefixEnd_1661413 : Nat := 4983230072969 + 3 ^ 40 * 1661413 * 2
def baseEnd_1661413 : Nat := 126385694019024214473601

theorem tailTrace_1661413 : CollatzResearch.WordTrace tailWord_1661413 prefixEnd_1661413 126385694019024214473601 := by
  unfold tailWord_1661413
  simp only [CollatzResearch.WordTrace]
  refine ⟨60596710329991922595276893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40397806886661281730184595 60596710329991922595276893)
  ·
    refine ⟨22723766373746970973228835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60596710329991922595276893 22723766373746970973228835)
    ·
      refine ⟨34085649560620456459843253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22723766373746970973228835 34085649560620456459843253)
      ·
        refine ⟨3195529646308167793110305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34085649560620456459843253 3195529646308167793110305)
        ·
          refine ⟨2396647234731125844832729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3195529646308167793110305 2396647234731125844832729)
          ·
            refine ⟨1797485426048344383624547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2396647234731125844832729 1797485426048344383624547)
            ·
              refine ⟨2696228139072516575436821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797485426048344383624547 2696228139072516575436821)
              ·
                refine ⟨126385694019024214473601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2696228139072516575436821 126385694019024214473601)
                ·
                  rfl

theorem cell21_1661413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 6].length) (baseStart_1661413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661413 prefixEnd_1661413 := by exact prefixLift 1661413
  have htrace : WordTrace (prefixWord ++ tailWord_1661413) baseStart_1661413 baseEnd_1661413 := by
    simpa [prefixWord, tailWord_1661413, baseEnd_1661413] using wordTrace_append hprefix tailTrace_1661413
  have hstable : (prefixWord ++ tailWord_1661413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661413).length < 2 ^ (prefixWord ++ tailWord_1661413).sum := by decide
  have hdescent : baseEnd_1661413 < baseStart_1661413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661444 : List Nat := [2, 3, 2, 3, 1, 1, 1, 5, 3]
def baseStart_1661444 : Nat := 118140960795 + 1661444 * 2 ^ 59
def prefixEnd_1661444 : Nat := 4983230072969 + 3 ^ 40 * 1661444 * 2
def baseEnd_1661444 : Nat := 379164156679423478404073

theorem tailTrace_1661444 : CollatzResearch.WordTrace tailWord_1661444 prefixEnd_1661444 379164156679423478404073 := by
  unfold tailWord_1661444
  simp only [CollatzResearch.WordTrace]
  refine ⟨30298920496439807444827693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40398560661919743259770257 30298920496439807444827693)
  ·
    refine ⟨11362095186164927791810385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30298920496439807444827693 11362095186164927791810385)
    ·
      refine ⟨8521571389623695843857789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11362095186164927791810385 8521571389623695843857789)
      ·
        refine ⟨3195589271108885941446671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8521571389623695843857789 3195589271108885941446671)
        ·
          refine ⟨4793383906663328912170007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3195589271108885941446671 4793383906663328912170007)
          ·
            refine ⟨7190075859994993368255011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4793383906663328912170007 7190075859994993368255011)
            ·
              refine ⟨10785113789992490052382517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7190075859994993368255011 10785113789992490052382517)
              ·
                refine ⟨1011104417811795942410861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10785113789992490052382517 1011104417811795942410861)
                ·
                  refine ⟨379164156679423478404073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011104417811795942410861 379164156679423478404073)
                  ·
                    rfl

theorem cell21_1661444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_1661444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661444 prefixEnd_1661444 := by exact prefixLift 1661444
  have htrace : WordTrace (prefixWord ++ tailWord_1661444) baseStart_1661444 baseEnd_1661444 := by
    simpa [prefixWord, tailWord_1661444, baseEnd_1661444] using wordTrace_append hprefix tailTrace_1661444
  have hstable : (prefixWord ++ tailWord_1661444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661444).length < 2 ^ (prefixWord ++ tailWord_1661444).sum := by decide
  have hdescent : baseEnd_1661444 < baseStart_1661444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661545 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 7]
def baseStart_1661545 : Nat := 118140960795 + 1661545 * 2 ^ 59
def prefixEnd_1661545 : Nat := 4983230072969 + 3 ^ 40 * 1661545 * 2
def baseEnd_1661545 : Nat := 379187206255469747220533

theorem tailTrace_1661545 : CollatzResearch.WordTrace tailWord_1661545 prefixEnd_1661545 379187206255469747220533 := by
  unfold tailWord_1661545
  simp only [CollatzResearch.WordTrace]
  refine ⟨60601524765513709139082089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40401016510342472759388059 60601524765513709139082089)
  ·
    refine ⟨45451143574135281854311567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60601524765513709139082089 45451143574135281854311567)
    ·
      refine ⟨68176715361202922781467351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45451143574135281854311567 68176715361202922781467351)
      ·
        refine ⟨102265073041804384172201027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68176715361202922781467351 102265073041804384172201027)
        ·
          refine ⟨153397609562706576258301541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102265073041804384172201027 153397609562706576258301541)
          ·
            refine ⟨28762051793007483048431539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153397609562706576258301541 28762051793007483048431539)
            ·
              refine ⟨43143077689511224572647309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28762051793007483048431539 43143077689511224572647309)
              ·
                refine ⟨16178654133566709214742741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43143077689511224572647309 16178654133566709214742741)
                ·
                  refine ⟨379187206255469747220533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16178654133566709214742741 379187206255469747220533)
                  ·
                    rfl

theorem cell21_1661545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_1661545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661545 prefixEnd_1661545 := by exact prefixLift 1661545
  have htrace : WordTrace (prefixWord ++ tailWord_1661545) baseStart_1661545 baseEnd_1661545 := by
    simpa [prefixWord, tailWord_1661545, baseEnd_1661545] using wordTrace_append hprefix tailTrace_1661545
  have hstable : (prefixWord ++ tailWord_1661545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661545).length < 2 ^ (prefixWord ++ tailWord_1661545).sum := by decide
  have hdescent : baseEnd_1661545 < baseStart_1661545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661703 : List Nat := [1, 1, 4, 4, 1, 3, 2, 1, 4]
def baseStart_1661703 : Nat := 118140960795 + 1661703 * 2 ^ 59
def prefixEnd_1661703 : Nat := 4983230072969 + 3 ^ 40 * 1661703 * 2
def baseEnd_1661703 : Nat := 379223264008096583586877

theorem tailTrace_1661703 : CollatzResearch.WordTrace tailWord_1661703 prefixEnd_1661703 379223264008096583586877 := by
  unfold tailWord_1661703
  simp only [CollatzResearch.WordTrace]
  refine ⟨60607287498941302123333763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40404858332627534748889175 60607287498941302123333763)
  ·
    refine ⟨90910931248411953185000645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60607287498941302123333763 90910931248411953185000645)
    ·
      refine ⟨17045799609077241222187621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90910931248411953185000645 17045799609077241222187621)
      ·
        refine ⟨3196087426701982729160179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17045799609077241222187621 3196087426701982729160179)
        ·
          refine ⟨4794131140052974093740269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3196087426701982729160179 4794131140052974093740269)
          ·
            refine ⟨1797799177519865285152601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4794131140052974093740269 1797799177519865285152601)
            ·
              refine ⟨1348349383139898963864451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797799177519865285152601 1348349383139898963864451)
              ·
                refine ⟨2022524074709848445796677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1348349383139898963864451 2022524074709848445796677)
                ·
                  refine ⟨379223264008096583586877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2022524074709848445796677 379223264008096583586877)
                  ·
                    rfl

theorem cell21_1661703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 4].length) (baseStart_1661703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661703 prefixEnd_1661703 := by exact prefixLift 1661703
  have htrace : WordTrace (prefixWord ++ tailWord_1661703) baseStart_1661703 baseEnd_1661703 := by
    simpa [prefixWord, tailWord_1661703, baseEnd_1661703] using wordTrace_append hprefix tailTrace_1661703
  have hstable : (prefixWord ++ tailWord_1661703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661703).length < 2 ^ (prefixWord ++ tailWord_1661703).sum := by decide
  have hdescent : baseEnd_1661703 < baseStart_1661703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661745 : List Nat := [1, 2, 2, 3, 2, 1, 4, 2, 4]
def baseStart_1661745 : Nat := 118140960795 + 1661745 * 2 ^ 59
def prefixEnd_1661745 : Nat := 4983230072969 + 3 ^ 40 * 1661745 * 2
def baseEnd_1661745 : Nat := 379232848980313843886791

theorem tailTrace_1661745 : CollatzResearch.WordTrace tailWord_1661745 prefixEnd_1661745 379232848980313843886791 := by
  unfold tailWord_1661745
  simp only [CollatzResearch.WordTrace]
  refine ⟨60608819364789143296362689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40405879576526095530908459 60608819364789143296362689)
  ·
    refine ⟨45456614523591857472272017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60608819364789143296362689 45456614523591857472272017)
    ·
      refine ⟨34092460892693893104204013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45456614523591857472272017 34092460892693893104204013)
      ·
        refine ⟨12784672834760209914076505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34092460892693893104204013 12784672834760209914076505)
        ·
          refine ⟨9588504626070157435557379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12784672834760209914076505 9588504626070157435557379)
          ·
            refine ⟨14382756939105236153336069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9588504626070157435557379 14382756939105236153336069)
            ·
              refine ⟨2696766926082231778750513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14382756939105236153336069 2696766926082231778750513)
              ·
                refine ⟨2022575194561673834062885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2696766926082231778750513 2022575194561673834062885)
                ·
                  refine ⟨379232848980313843886791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2022575194561673834062885 379232848980313843886791)
                  ·
                    rfl

theorem cell21_1661745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_1661745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661745 prefixEnd_1661745 := by exact prefixLift 1661745
  have htrace : WordTrace (prefixWord ++ tailWord_1661745) baseStart_1661745 baseEnd_1661745 := by
    simpa [prefixWord, tailWord_1661745, baseEnd_1661745] using wordTrace_append hprefix tailTrace_1661745
  have hstable : (prefixWord ++ tailWord_1661745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661745).length < 2 ^ (prefixWord ++ tailWord_1661745).sum := by decide
  have hdescent : baseEnd_1661745 < baseStart_1661745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661759 : List Nat := [1, 1, 2, 2, 5, 1, 3, 6]
def baseStart_1661759 : Nat := 118140960795 + 1661759 * 2 ^ 59
def prefixEnd_1661759 : Nat := 4983230072969 + 3 ^ 40 * 1661759 * 2
def baseEnd_1661759 : Nat := 126412014657017643551143

theorem tailTrace_1661759 : CollatzResearch.WordTrace tailWord_1661759 prefixEnd_1661759 126412014657017643551143 := by
  unfold tailWord_1661759
  simp only [CollatzResearch.WordTrace]
  refine ⟨60609329986738423687372331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40406219991158949124914887 60609329986738423687372331)
  ·
    refine ⟨90913994980107635531058497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60609329986738423687372331 90913994980107635531058497)
    ·
      refine ⟨68185496235080726648293873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90913994980107635531058497 68185496235080726648293873)
      ·
        refine ⟨51139122176310544986220405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68185496235080726648293873 51139122176310544986220405)
        ·
          refine ⟨4794292704029113592458163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51139122176310544986220405 4794292704029113592458163)
          ·
            refine ⟨7191439056043670388687245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4794292704029113592458163 7191439056043670388687245)
            ·
              refine ⟨2696789646016376395757717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7191439056043670388687245 2696789646016376395757717)
              ·
                refine ⟨126412014657017643551143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2696789646016376395757717 126412014657017643551143)
                ·
                  rfl

theorem cell21_1661759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 6].length) (baseStart_1661759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661759 prefixEnd_1661759 := by exact prefixLift 1661759
  have htrace : WordTrace (prefixWord ++ tailWord_1661759) baseStart_1661759 baseEnd_1661759 := by
    simpa [prefixWord, tailWord_1661759, baseEnd_1661759] using wordTrace_append hprefix tailTrace_1661759
  have hstable : (prefixWord ++ tailWord_1661759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661759).length < 2 ^ (prefixWord ++ tailWord_1661759).sum := by decide
  have hdescent : baseEnd_1661759 < baseStart_1661759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661804 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 6]
def baseStart_1661804 : Nat := 118140960795 + 1661804 * 2 ^ 59
def prefixEnd_1661804 : Nat := 4983230072969 + 3 ^ 40 * 1661804 * 2
def baseEnd_1661804 : Nat := 379246313584142852403337

theorem tailTrace_1661804 : CollatzResearch.WordTrace tailWord_1661804 prefixEnd_1661804 379246313584142852403337 := by
  unfold tailWord_1661804
  simp only [CollatzResearch.WordTrace]
  refine ⟨30305485635787698186380233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40407314181050264248506977 30305485635787698186380233)
  ·
    refine ⟨22729114226840773639785175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30305485635787698186380233 22729114226840773639785175)
    ·
      refine ⟨34093671340261160459677763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22729114226840773639785175 34093671340261160459677763)
      ·
        refine ⟨51140507010391740689516645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34093671340261160459677763 51140507010391740689516645)
        ·
          refine ⟨9588845064448451379284371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51140507010391740689516645 9588845064448451379284371)
          ·
            refine ⟨14383267596672677068926557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9588845064448451379284371 14383267596672677068926557)
            ·
              refine ⟨5393725348752253900847459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14383267596672677068926557 5393725348752253900847459)
              ·
                refine ⟨8090588023128380851271189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5393725348752253900847459 8090588023128380851271189)
                ·
                  refine ⟨379246313584142852403337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8090588023128380851271189 379246313584142852403337)
                  ·
                    rfl

theorem cell21_1661804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_1661804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661804 prefixEnd_1661804 := by exact prefixLift 1661804
  have htrace : WordTrace (prefixWord ++ tailWord_1661804) baseStart_1661804 baseEnd_1661804 := by
    simpa [prefixWord, tailWord_1661804, baseEnd_1661804] using wordTrace_append hprefix tailTrace_1661804
  have hstable : (prefixWord ++ tailWord_1661804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661804).length < 2 ^ (prefixWord ++ tailWord_1661804).sum := by decide
  have hdescent : baseEnd_1661804 < baseStart_1661804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661818 : List Nat := [3, 1, 1, 1, 1, 1, 3, 10]
def baseStart_1661818 : Nat := 118140960795 + 1661818 * 2 ^ 59
def prefixEnd_1661818 : Nat := 4983230072969 + 3 ^ 40 * 1661818 * 2
def baseEnd_1661818 : Nat := 126416502858293979723325

theorem tailTrace_1661818 : CollatzResearch.WordTrace tailWord_1661818 prefixEnd_1661818 126416502858293979723325 := by
  unfold tailWord_1661818
  simp only [CollatzResearch.WordTrace]
  refine ⟨15152870473381169190942527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40407654595683117842513405 15152870473381169190942527)
  ·
    refine ⟨22729305710071753786413791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15152870473381169190942527 22729305710071753786413791)
    ·
      refine ⟨34093958565107630679620687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22729305710071753786413791 34093958565107630679620687)
      ·
        refine ⟨51140937847661446019431031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34093958565107630679620687 51140937847661446019431031)
        ·
          refine ⟨76711406771492169029146547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51140937847661446019431031 76711406771492169029146547)
          ·
            refine ⟨115067110157238253543719821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76711406771492169029146547 115067110157238253543719821)
            ·
              refine ⟨43150166308964345078894933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115067110157238253543719821 43150166308964345078894933)
              ·
                refine ⟨126416502858293979723325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43150166308964345078894933 126416502858293979723325)
                ·
                  rfl

theorem cell21_1661818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_1661818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661818 prefixEnd_1661818 := by exact prefixLift 1661818
  have htrace : WordTrace (prefixWord ++ tailWord_1661818) baseStart_1661818 baseEnd_1661818 := by
    simpa [prefixWord, tailWord_1661818, baseEnd_1661818] using wordTrace_append hprefix tailTrace_1661818
  have hstable : (prefixWord ++ tailWord_1661818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661818).length < 2 ^ (prefixWord ++ tailWord_1661818).sum := by decide
  have hdescent : baseEnd_1661818 < baseStart_1661818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661835 : List Nat := [1, 1, 1, 1, 4, 2, 6, 5]
def baseStart_1661835 : Nat := 118140960795 + 1661835 * 2 ^ 59
def prefixEnd_1661835 : Nat := 4983230072969 + 3 ^ 40 * 1661835 * 2
def baseEnd_1661835 : Nat := 126417796068831229128869

theorem tailTrace_1661835 : CollatzResearch.WordTrace tailWord_1661835 prefixEnd_1661835 126417796068831229128869 := by
  unfold tailWord_1661835
  simp only [CollatzResearch.WordTrace]
  refine ⟨60612101934463088667138959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40408067956308725778092639 60612101934463088667138959)
  ·
    refine ⟨90918152901694633000708439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60612101934463088667138959 90918152901694633000708439)
    ·
      refine ⟨136377229352541949501062659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90918152901694633000708439 136377229352541949501062659)
      ·
        refine ⟨204565844028812924251593989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136377229352541949501062659 204565844028812924251593989)
        ·
          refine ⟨38356095755402423297173873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204565844028812924251593989 38356095755402423297173873)
          ·
            refine ⟨28767071816551817472880405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38356095755402423297173873 28767071816551817472880405)
            ·
              refine ⟨1348456491400866444041269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28767071816551817472880405 1348456491400866444041269)
              ·
                refine ⟨126417796068831229128869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1348456491400866444041269 126417796068831229128869)
                ·
                  rfl

theorem cell21_1661835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 5].length) (baseStart_1661835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661835 prefixEnd_1661835 := by exact prefixLift 1661835
  have htrace : WordTrace (prefixWord ++ tailWord_1661835) baseStart_1661835 baseEnd_1661835 := by
    simpa [prefixWord, tailWord_1661835, baseEnd_1661835] using wordTrace_append hprefix tailTrace_1661835
  have hstable : (prefixWord ++ tailWord_1661835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661835).length < 2 ^ (prefixWord ++ tailWord_1661835).sum := by decide
  have hdescent : baseEnd_1661835 < baseStart_1661835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661852 : List Nat := [2, 2, 3, 3, 2, 2, 7]
def baseStart_1661852 : Nat := 118140960795 + 1661852 * 2 ^ 59
def prefixEnd_1661852 : Nat := 4983230072969 + 3 ^ 40 * 1661852 * 2
def baseEnd_1661852 : Nat := 42139696426456159511471

theorem tailTrace_1661852 : CollatzResearch.WordTrace tailWord_1661852 prefixEnd_1661852 42139696426456159511471 := by
  unfold tailWord_1661852
  simp only [CollatzResearch.WordTrace]
  refine ⟨30306360987700750285253905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40408481316934333713671873 30306360987700750285253905)
  ·
    refine ⟨22729770740775562713940429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30306360987700750285253905 22729770740775562713940429)
    ·
      refine ⟨8523664027790836017727661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22729770740775562713940429 8523664027790836017727661)
      ·
        refine ⟨3196374010421563506647873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8523664027790836017727661 3196374010421563506647873)
        ·
          refine ⟨2397280507816172629985905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3196374010421563506647873 2397280507816172629985905)
          ·
            refine ⟨1797960380862129472489429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2397280507816172629985905 1797960380862129472489429)
            ·
              refine ⟨42139696426456159511471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1797960380862129472489429 42139696426456159511471)
              ·
                rfl

theorem cell21_1661852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 7].length) (baseStart_1661852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661852 prefixEnd_1661852 := by exact prefixLift 1661852
  have htrace : WordTrace (prefixWord ++ tailWord_1661852) baseStart_1661852 baseEnd_1661852 := by
    simpa [prefixWord, tailWord_1661852, baseEnd_1661852] using wordTrace_append hprefix tailTrace_1661852
  have hstable : (prefixWord ++ tailWord_1661852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661852).length < 2 ^ (prefixWord ++ tailWord_1661852).sum := by decide
  have hdescent : baseEnd_1661852 < baseStart_1661852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661869 : List Nat := [1, 5, 2, 3, 1, 1, 2, 6]
def baseStart_1661869 : Nat := 118140960795 + 1661869 * 2 ^ 59
def prefixEnd_1661869 : Nat := 4983230072969 + 3 ^ 40 * 1661869 * 2
def baseEnd_1661869 : Nat := 126420382489905727939957

theorem tailTrace_1661869 : CollatzResearch.WordTrace tailWord_1661869 prefixEnd_1661869 126420382489905727939957 := by
  unfold tailWord_1661869
  simp only [CollatzResearch.WordTrace]
  refine ⟨60613342016339912473876661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40408894677559941649251107 60613342016339912473876661)
  ·
    refine ⟨5682500814031866794425937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60613342016339912473876661 5682500814031866794425937)
    ·
      refine ⟨4261875610523900095819453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5682500814031866794425937 4261875610523900095819453)
      ·
        refine ⟨1598203353946462535932295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4261875610523900095819453 1598203353946462535932295)
        ·
          refine ⟨2397305030919693803898443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1598203353946462535932295 2397305030919693803898443)
          ·
            refine ⟨3595957546379540705847665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2397305030919693803898443 3595957546379540705847665)
            ·
              refine ⟨2696968159784655529385749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3595957546379540705847665 2696968159784655529385749)
              ·
                refine ⟨126420382489905727939957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2696968159784655529385749 126420382489905727939957)
                ·
                  rfl

theorem cell21_1661869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 6].length) (baseStart_1661869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661869 prefixEnd_1661869 := by exact prefixLift 1661869
  have htrace : WordTrace (prefixWord ++ tailWord_1661869) baseStart_1661869 baseEnd_1661869 := by
    simpa [prefixWord, tailWord_1661869, baseEnd_1661869] using wordTrace_append hprefix tailTrace_1661869
  have hstable : (prefixWord ++ tailWord_1661869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661869).length < 2 ^ (prefixWord ++ tailWord_1661869).sum := by decide
  have hdescent : baseEnd_1661869 < baseStart_1661869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661917 : List Nat := [1, 4, 3, 1, 2, 3, 2, 2, 3]
def baseStart_1661917 : Nat := 118140960795 + 1661917 * 2 ^ 59
def prefixEnd_1661917 : Nat := 4983230072969 + 3 ^ 40 * 1661917 * 2
def baseEnd_1661917 : Nat := 379272101723679767019773

theorem tailTrace_1661917 : CollatzResearch.WordTrace tailWord_1661917 prefixEnd_1661917 379272101723679767019773 := by
  unfold tailWord_1661917
  simp only [CollatzResearch.WordTrace]
  refine ⟨60615092720166016671624005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40410061813444011114416003 60615092720166016671624005)
  ·
    refine ⟨11365329885031128125929501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60615092720166016671624005 11365329885031128125929501)
    ·
      refine ⟨4261998706886673047223563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11365329885031128125929501 4261998706886673047223563)
      ·
        refine ⟨6392998060330009570835345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4261998706886673047223563 6392998060330009570835345)
        ·
          refine ⟨4794748545247507178126509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6392998060330009570835345 4794748545247507178126509)
          ·
            refine ⟨1798030704467815191797441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4794748545247507178126509 1798030704467815191797441)
            ·
              refine ⟨1348523028350861393848081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1798030704467815191797441 1348523028350861393848081)
              ·
                refine ⟨1011392271263146045386061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1348523028350861393848081 1011392271263146045386061)
                ·
                  refine ⟨379272101723679767019773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011392271263146045386061 379272101723679767019773)
                  ·
                    rfl

theorem cell21_1661917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_1661917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661917 prefixEnd_1661917 := by exact prefixLift 1661917
  have htrace : WordTrace (prefixWord ++ tailWord_1661917) baseStart_1661917 baseEnd_1661917 := by
    simpa [prefixWord, tailWord_1661917, baseEnd_1661917] using wordTrace_append hprefix tailTrace_1661917
  have hstable : (prefixWord ++ tailWord_1661917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661917).length < 2 ^ (prefixWord ++ tailWord_1661917).sum := by decide
  have hdescent : baseEnd_1661917 < baseStart_1661917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661939 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 10]
def baseStart_1661939 : Nat := 118140960795 + 1661939 * 2 ^ 59
def prefixEnd_1661939 : Nat := 4983230072969 + 3 ^ 40 * 1661939 * 2
def baseEnd_1661939 : Nat := 379277122423412617653061

theorem tailTrace_1661939 : CollatzResearch.WordTrace tailWord_1661939 prefixEnd_1661939 379277122423412617653061 := by
  unfold tailWord_1661939
  simp only [CollatzResearch.WordTrace]
  refine ⟨60615895126086314428924871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40410596750724209619283247 60615895126086314428924871)
  ·
    refine ⟨90923842689129471643387307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60615895126086314428924871 90923842689129471643387307)
    ·
      refine ⟨136385764033694207465080961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90923842689129471643387307 136385764033694207465080961)
      ·
        refine ⟨102289323025270655598810721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136385764033694207465080961 102289323025270655598810721)
        ·
          refine ⟨76716992268952991699108041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102289323025270655598810721 76716992268952991699108041)
          ·
            refine ⟨57537744201714743774331031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76716992268952991699108041 57537744201714743774331031)
            ·
              refine ⟨86306616302572115661496547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57537744201714743774331031 86306616302572115661496547)
              ·
                refine ⟨129459924453858173492244821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86306616302572115661496547 129459924453858173492244821)
                ·
                  refine ⟨379277122423412617653061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 129459924453858173492244821 379277122423412617653061)
                  ·
                    rfl

theorem cell21_1661939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 10].length) (baseStart_1661939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661939 prefixEnd_1661939 := by exact prefixLift 1661939
  have htrace : WordTrace (prefixWord ++ tailWord_1661939) baseStart_1661939 baseEnd_1661939 := by
    simpa [prefixWord, tailWord_1661939, baseEnd_1661939] using wordTrace_append hprefix tailTrace_1661939
  have hstable : (prefixWord ++ tailWord_1661939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661939).length < 2 ^ (prefixWord ++ tailWord_1661939).sum := by decide
  have hdescent : baseEnd_1661939 < baseStart_1661939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661942 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_1661942 : Nat := 118140960795 + 1661942 * 2 ^ 59
def prefixEnd_1661942 : Nat := 4983230072969 + 3 ^ 40 * 1661942 * 2
def baseEnd_1661942 : Nat := 379277807064285279103055

theorem tailTrace_1661942 : CollatzResearch.WordTrace tailWord_1661942 prefixEnd_1661942 379277807064285279103055 := by
  unfold tailWord_1661942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3788500284067215371330255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40410669696716963960856053 3788500284067215371330255)
  ·
    refine ⟨5682750426100823056995383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3788500284067215371330255 5682750426100823056995383)
    ·
      refine ⟨8524125639151234585493075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5682750426100823056995383 8524125639151234585493075)
      ·
        refine ⟨12786188458726851878239613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8524125639151234585493075 12786188458726851878239613)
        ·
          refine ⟨4794820672022569454339855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12786188458726851878239613 4794820672022569454339855)
          ·
            refine ⟨7192231008033854181509783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4794820672022569454339855 7192231008033854181509783)
            ·
              refine ⟨10788346512050781272264675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7192231008033854181509783 10788346512050781272264675)
              ·
                refine ⟨16182519768076171908397013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10788346512050781272264675 16182519768076171908397013)
                ·
                  refine ⟨379277807064285279103055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16182519768076171908397013 379277807064285279103055)
                  ·
                    rfl

theorem cell21_1661942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_1661942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661942 prefixEnd_1661942 := by exact prefixLift 1661942
  have htrace : WordTrace (prefixWord ++ tailWord_1661942) baseStart_1661942 baseEnd_1661942 := by
    simpa [prefixWord, tailWord_1661942, baseEnd_1661942] using wordTrace_append hprefix tailTrace_1661942
  have hstable : (prefixWord ++ tailWord_1661942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661942).length < 2 ^ (prefixWord ++ tailWord_1661942).sum := by decide
  have hdescent : baseEnd_1661942 < baseStart_1661942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661959 : List Nat := [1, 1, 4, 3, 1, 1, 4, 3, 3]
def baseStart_1661959 : Nat := 118140960795 + 1661959 * 2 ^ 59
def prefixEnd_1661959 : Nat := 4983230072969 + 3 ^ 40 * 1661959 * 2
def baseEnd_1661959 : Nat := 379281686695897027319687

theorem tailTrace_1661959 : CollatzResearch.WordTrace tailWord_1661959 prefixEnd_1661959 379281686695897027319687 := by
  unfold tailWord_1661959
  simp only [CollatzResearch.WordTrace]
  refine ⟨60616624586013857844652931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40411083057342571896435287 60616624586013857844652931)
  ·
    refine ⟨90924936879020786766979397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60616624586013857844652931 90924936879020786766979397)
    ·
      refine ⟨17048425664816397518808637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90924936879020786766979397 17048425664816397518808637)
      ·
        refine ⟨6393159624306149069553239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17048425664816397518808637 6393159624306149069553239)
        ·
          refine ⟨9589739436459223604329859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6393159624306149069553239 9589739436459223604329859)
          ·
            refine ⟨14384609154688835406494789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9589739436459223604329859 14384609154688835406494789)
            ·
              refine ⟨2697114216504156638717773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14384609154688835406494789 2697114216504156638717773)
              ·
                refine ⟨1011417831189058739519165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2697114216504156638717773 1011417831189058739519165)
                ·
                  refine ⟨379281686695897027319687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011417831189058739519165 379281686695897027319687)
                  ·
                    rfl

theorem cell21_1661959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 3].length) (baseStart_1661959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661959 prefixEnd_1661959 := by exact prefixLift 1661959
  have htrace : WordTrace (prefixWord ++ tailWord_1661959) baseStart_1661959 baseEnd_1661959 := by
    simpa [prefixWord, tailWord_1661959, baseEnd_1661959] using wordTrace_append hprefix tailTrace_1661959
  have hstable : (prefixWord ++ tailWord_1661959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661959).length < 2 ^ (prefixWord ++ tailWord_1661959).sum := by decide
  have hdescent : baseEnd_1661959 < baseStart_1661959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661973 : List Nat := [1, 3, 2, 1, 4, 1, 3, 2, 4]
def baseStart_1661973 : Nat := 118140960795 + 1661973 * 2 ^ 59
def prefixEnd_1661973 : Nat := 4983230072969 + 3 ^ 40 * 1661973 * 2
def baseEnd_1661973 : Nat := 379284881686636114086325

theorem tailTrace_1661973 : CollatzResearch.WordTrace tailWord_1661973 prefixEnd_1661973 379284881686636114086325 := by
  unfold tailWord_1661973
  simp only [CollatzResearch.WordTrace]
  refine ⟨60617135207963138235662573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40411423471975425490441715 60617135207963138235662573)
  ·
    refine ⟨22731425702986176838373465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60617135207963138235662573 22731425702986176838373465)
    ·
      refine ⟨17048569277239632628780099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22731425702986176838373465 17048569277239632628780099)
      ·
        refine ⟨25572853915859448943170149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17048569277239632628780099 25572853915859448943170149)
        ·
          refine ⟨4794910109223646676844403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25572853915859448943170149 4794910109223646676844403)
          ·
            refine ⟨7192365163835470015266605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4794910109223646676844403 7192365163835470015266605)
            ·
              refine ⟨2697136936438301255724977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7192365163835470015266605 2697136936438301255724977)
              ·
                refine ⟨2022852702328725941793733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2697136936438301255724977 2022852702328725941793733)
                ·
                  refine ⟨379284881686636114086325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2022852702328725941793733 379284881686636114086325)
                  ·
                    rfl

theorem cell21_1661973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_1661973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1661973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1661973 prefixEnd_1661973 := by exact prefixLift 1661973
  have htrace : WordTrace (prefixWord ++ tailWord_1661973) baseStart_1661973 baseEnd_1661973 := by
    simpa [prefixWord, tailWord_1661973, baseEnd_1661973] using wordTrace_append hprefix tailTrace_1661973
  have hstable : (prefixWord ++ tailWord_1661973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661973).length < 2 ^ (prefixWord ++ tailWord_1661973).sum := by decide
  have hdescent : baseEnd_1661973 < baseStart_1661973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662001 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 5]
def baseStart_1662001 : Nat := 118140960795 + 1662001 * 2 ^ 59
def prefixEnd_1662001 : Nat := 4983230072969 + 3 ^ 40 * 1662001 * 2
def baseEnd_1662001 : Nat := 379291271668114287619601

theorem tailTrace_1662001 : CollatzResearch.WordTrace tailWord_1662001 prefixEnd_1662001 379291271668114287619601 := by
  unfold tailWord_1662001
  simp only [CollatzResearch.WordTrace]
  refine ⟨60618156451861699017681857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40412104301241132678454571 60618156451861699017681857)
  ·
    refine ⟨45463617338896274263261393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60618156451861699017681857 45463617338896274263261393)
    ·
      refine ⟨34097713004172205697446045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45463617338896274263261393 34097713004172205697446045)
      ·
        refine ⟨12786642376564577136542267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34097713004172205697446045 12786642376564577136542267)
        ·
          refine ⟨19179963564846865704813401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12786642376564577136542267 19179963564846865704813401)
          ·
            refine ⟨14384972673635149278610051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19179963564846865704813401 14384972673635149278610051)
            ·
              refine ⟨21577459010452723917915077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14384972673635149278610051 21577459010452723917915077)
              ·
                refine ⟨4045773564459885734609077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21577459010452723917915077 4045773564459885734609077)
                ·
                  refine ⟨379291271668114287619601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4045773564459885734609077 379291271668114287619601)
                  ·
                    rfl

theorem cell21_1662001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_1662001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662001 prefixEnd_1662001 := by exact prefixLift 1662001
  have htrace : WordTrace (prefixWord ++ tailWord_1662001) baseStart_1662001 baseEnd_1662001 := by
    simpa [prefixWord, tailWord_1662001, baseEnd_1662001] using wordTrace_append hprefix tailTrace_1662001
  have hstable : (prefixWord ++ tailWord_1662001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662001).length < 2 ^ (prefixWord ++ tailWord_1662001).sum := by decide
  have hdescent : baseEnd_1662001 < baseStart_1662001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662004 : List Nat := [2, 5, 1, 2, 1, 2, 1, 7]
def baseStart_1662004 : Nat := 118140960795 + 1662004 * 2 ^ 59
def prefixEnd_1662004 : Nat := 4983230072969 + 3 ^ 40 * 1662004 * 2
def baseEnd_1662004 : Nat := 126430652102995649689865

theorem tailTrace_1662004 : CollatzResearch.WordTrace tailWord_1662004 prefixEnd_1662004 126430652102995649689865 := by
  unfold tailWord_1662004
  simp only [CollatzResearch.WordTrace]
  refine ⟨30309132935425415265020533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40412177247233887020027377 30309132935425415265020533)
  ·
    refine ⟨2841481212696132681095675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30309132935425415265020533 2841481212696132681095675)
    ·
      refine ⟨4262221819044199021643513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2841481212696132681095675 4262221819044199021643513)
      ·
        refine ⟨3196666364283149266232635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4262221819044199021643513 3196666364283149266232635)
        ·
          refine ⟨4794999546424723899348953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3196666364283149266232635 4794999546424723899348953)
          ·
            refine ⟨3596249659818542924511715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4794999546424723899348953 3596249659818542924511715)
            ·
              refine ⟨5394374489727814386767573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3596249659818542924511715 5394374489727814386767573)
              ·
                refine ⟨126430652102995649689865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5394374489727814386767573 126430652102995649689865)
                ·
                  rfl

theorem cell21_1662004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 7].length) (baseStart_1662004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662004 prefixEnd_1662004 := by exact prefixLift 1662004
  have htrace : WordTrace (prefixWord ++ tailWord_1662004) baseStart_1662004 baseEnd_1662004 := by
    simpa [prefixWord, tailWord_1662004, baseEnd_1662004] using wordTrace_append hprefix tailTrace_1662004
  have hstable : (prefixWord ++ tailWord_1662004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662004).length < 2 ^ (prefixWord ++ tailWord_1662004).sum := by decide
  have hdescent : baseEnd_1662004 < baseStart_1662004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662049 : List Nat := [1, 2, 3, 1, 1, 2, 6, 1, 4]
def baseStart_1662049 : Nat := 118140960795 + 1662049 * 2 ^ 59
def prefixEnd_1662049 : Nat := 4983230072969 + 3 ^ 40 * 1662049 * 2
def baseEnd_1662049 : Nat := 379302225922076870819503

theorem tailTrace_1662049 : CollatzResearch.WordTrace tailWord_1662049 prefixEnd_1662049 379302225922076870819503 := by
  unfold tailWord_1662049
  simp only [CollatzResearch.WordTrace]
  refine ⟨60619907155687803215429201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40413271437125202143619467 60619907155687803215429201)
  ·
    refine ⟨45464930366765852411571901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60619907155687803215429201 45464930366765852411571901)
    ·
      refine ⟨17049348887537194654339463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45464930366765852411571901 17049348887537194654339463)
      ·
        refine ⟨25574023331305791981509195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17049348887537194654339463 25574023331305791981509195)
        ·
          refine ⟨38361034996958687972263793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25574023331305791981509195 38361034996958687972263793)
          ·
            refine ⟨28770776247719015979197845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38361034996958687972263793 28770776247719015979197845)
            ·
              refine ⟨1348630136611828874024899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28770776247719015979197845 1348630136611828874024899)
              ·
                refine ⟨2022945204917743311037349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1348630136611828874024899 2022945204917743311037349)
                ·
                  refine ⟨379302225922076870819503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2022945204917743311037349 379302225922076870819503)
                  ·
                    rfl

theorem cell21_1662049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 4].length) (baseStart_1662049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662049 prefixEnd_1662049 := by exact prefixLift 1662049
  have htrace : WordTrace (prefixWord ++ tailWord_1662049) baseStart_1662049 baseEnd_1662049 := by
    simpa [prefixWord, tailWord_1662049, baseEnd_1662049] using wordTrace_append hprefix tailTrace_1662049
  have hstable : (prefixWord ++ tailWord_1662049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662049).length < 2 ^ (prefixWord ++ tailWord_1662049).sum := by decide
  have hdescent : baseEnd_1662049 < baseStart_1662049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662091 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 6]
def baseStart_1662091 : Nat := 118140960795 + 1662091 * 2 ^ 59
def prefixEnd_1662091 : Nat := 4983230072969 + 3 ^ 40 * 1662091 * 2
def baseEnd_1662091 : Nat := 379311810894294131119417

theorem tailTrace_1662091 : CollatzResearch.WordTrace tailWord_1662091 prefixEnd_1662091 379311810894294131119417 := by
  unfold tailWord_1662091
  simp only [CollatzResearch.WordTrace]
  refine ⟨60621439021535644388458127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40414292681023762925638751 60621439021535644388458127)
  ·
    refine ⟨90932158532303466582687191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60621439021535644388458127 90932158532303466582687191)
    ·
      refine ⟨136398237798455199874030787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90932158532303466582687191 136398237798455199874030787)
      ·
        refine ⟨204597356697682799811046181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136398237798455199874030787 204597356697682799811046181)
        ·
          refine ⟨38362004380815524964571159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204597356697682799811046181 38362004380815524964571159)
          ·
            refine ⟨57543006571223287446856739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38362004380815524964571159 57543006571223287446856739)
            ·
              refine ⟨86314509856834931170285109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57543006571223287446856739 86314509856834931170285109)
              ·
                refine ⟨8091985299078274797214229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86314509856834931170285109 8091985299078274797214229)
                ·
                  refine ⟨379311810894294131119417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8091985299078274797214229 379311810894294131119417)
                  ·
                    rfl

theorem cell21_1662091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 6].length) (baseStart_1662091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662091 prefixEnd_1662091 := by exact prefixLift 1662091
  have htrace : WordTrace (prefixWord ++ tailWord_1662091) baseStart_1662091 baseEnd_1662091 := by
    simpa [prefixWord, tailWord_1662091, baseEnd_1662091] using wordTrace_append hprefix tailTrace_1662091
  have hstable : (prefixWord ++ tailWord_1662091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662091).length < 2 ^ (prefixWord ++ tailWord_1662091).sum := by decide
  have hdescent : baseEnd_1662091 < baseStart_1662091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662142 : List Nat := [4, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_1662142 : Nat := 118140960795 + 1662142 * 2 ^ 59
def prefixEnd_1662142 : Nat := 4983230072969 + 3 ^ 40 * 1662142 * 2
def baseEnd_1662142 : Nat := 379323449789129375769313

theorem tailTrace_1662142 : CollatzResearch.WordTrace tailWord_1662142 prefixEnd_1662142 379323449789129375769313 := by
  unfold tailWord_1662142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7577912393043860012320585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40415532762900586732376453 7577912393043860012320585)
  ·
    refine ⟨5683434294782895009240439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7577912393043860012320585 5683434294782895009240439)
    ·
      refine ⟨8525151442174342513860659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5683434294782895009240439 8525151442174342513860659)
      ·
        refine ⟨12787727163261513770790989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8525151442174342513860659 12787727163261513770790989)
        ·
          refine ⟨4795397686223067664046621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12787727163261513770790989 4795397686223067664046621)
          ·
            refine ⟨1798274132333650374017483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4795397686223067664046621 1798274132333650374017483)
            ·
              refine ⟨2697411198500475561026225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1798274132333650374017483 2697411198500475561026225)
              ·
                refine ⟨2023058398875356670769669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2697411198500475561026225 2023058398875356670769669)
                ·
                  refine ⟨379323449789129375769313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2023058398875356670769669 379323449789129375769313)
                  ·
                    rfl

theorem cell21_1662142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_1662142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662142 prefixEnd_1662142 := by exact prefixLift 1662142
  have htrace : WordTrace (prefixWord ++ tailWord_1662142) baseStart_1662142 baseEnd_1662142 := by
    simpa [prefixWord, tailWord_1662142, baseEnd_1662142] using wordTrace_append hprefix tailTrace_1662142
  have hstable : (prefixWord ++ tailWord_1662142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662142).length < 2 ^ (prefixWord ++ tailWord_1662142).sum := by decide
  have hdescent : baseEnd_1662142 < baseStart_1662142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662173 : List Nat := [1, 4, 3, 2, 2, 2, 2, 5]
def baseStart_1662173 : Nat := 118140960795 + 1662173 * 2 ^ 59
def prefixEnd_1662173 : Nat := 4983230072969 + 3 ^ 40 * 1662173 * 2
def baseEnd_1662173 : Nat := 126443508137160070250861

theorem tailTrace_1662173 : CollatzResearch.WordTrace tailWord_1662173 prefixEnd_1662173 126443508137160070250861 := by
  unfold tailWord_1662173
  simp only [CollatzResearch.WordTrace]
  refine ⟨60624429807238572392943173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40416286538159048261962115 60624429807238572392943173)
  ·
    refine ⟨11367080588857232323676845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60624429807238572392943173 11367080588857232323676845)
    ·
      refine ⟨4262655220821462121378817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11367080588857232323676845 4262655220821462121378817)
      ·
        refine ⟨3196991415616096591034113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4262655220821462121378817 3196991415616096591034113)
        ·
          refine ⟨2397743561712072443275585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3196991415616096591034113 2397743561712072443275585)
          ·
            refine ⟨1798307671284054332456689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2397743561712072443275585 1798307671284054332456689)
            ·
              refine ⟨1348730753463040749342517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1798307671284054332456689 1348730753463040749342517)
              ·
                refine ⟨126443508137160070250861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1348730753463040749342517 126443508137160070250861)
                ·
                  rfl

theorem cell21_1662173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 5].length) (baseStart_1662173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662173 prefixEnd_1662173 := by exact prefixLift 1662173
  have htrace : WordTrace (prefixWord ++ tailWord_1662173) baseStart_1662173 baseEnd_1662173 := by
    simpa [prefixWord, tailWord_1662173, baseEnd_1662173] using wordTrace_append hprefix tailTrace_1662173
  have hstable : (prefixWord ++ tailWord_1662173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662173).length < 2 ^ (prefixWord ++ tailWord_1662173).sum := by decide
  have hdescent : baseEnd_1662173 < baseStart_1662173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662187 : List Nat := [1, 1, 1, 1, 2, 8, 1, 3, 3]
def baseStart_1662187 : Nat := 118140960795 + 1662187 * 2 ^ 59
def prefixEnd_1662187 : Nat := 4983230072969 + 3 ^ 40 * 1662187 * 2
def baseEnd_1662187 : Nat := 379333719402219297519221

theorem tailTrace_1662187 : CollatzResearch.WordTrace tailWord_1662187 prefixEnd_1662187 379333719402219297519221 := by
  unfold tailWord_1662187
  simp only [CollatzResearch.WordTrace]
  refine ⟨60624940429187852783952815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40416626952791901855968543 60624940429187852783952815)
  ·
    refine ⟨90937410643781779175929223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60624940429187852783952815 90937410643781779175929223)
    ·
      refine ⟨136406115965672668763893835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90937410643781779175929223 136406115965672668763893835)
      ·
        refine ⟨204609173948509003145840753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136406115965672668763893835 204609173948509003145840753)
        ·
          refine ⟨153456880461381752359380565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204609173948509003145840753 153456880461381752359380565)
          ·
            refine ⟨1798322817906817410461491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 153456880461381752359380565 1798322817906817410461491)
            ·
              refine ⟨2697484226860226115692237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1798322817906817410461491 2697484226860226115692237)
              ·
                refine ⟨1011556585072584793384589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2697484226860226115692237 1011556585072584793384589)
                ·
                  refine ⟨379333719402219297519221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011556585072584793384589 379333719402219297519221)
                  ·
                    rfl

theorem cell21_1662187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 3].length) (baseStart_1662187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662187 prefixEnd_1662187 := by exact prefixLift 1662187
  have htrace : WordTrace (prefixWord ++ tailWord_1662187) baseStart_1662187 baseEnd_1662187 := by
    simpa [prefixWord, tailWord_1662187, baseEnd_1662187] using wordTrace_append hprefix tailTrace_1662187
  have hstable : (prefixWord ++ tailWord_1662187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662187).length < 2 ^ (prefixWord ++ tailWord_1662187).sum := by decide
  have hdescent : baseEnd_1662187 < baseStart_1662187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662204 : List Nat := [2, 2, 2, 1, 5, 1, 3, 2, 3]
def baseStart_1662204 : Nat := 118140960795 + 1662204 * 2 ^ 59
def prefixEnd_1662204 : Nat := 4983230072969 + 3 ^ 40 * 1662204 * 2
def baseEnd_1662204 : Nat := 379337599033831045735853

theorem tailTrace_1662204 : CollatzResearch.WordTrace tailWord_1662204 prefixEnd_1662204 379337599033831045735853 := by
  unfold tailWord_1662204
  simp only [CollatzResearch.WordTrace]
  refine ⟨30312780235063132343660833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40417040313417509791547777 30312780235063132343660833)
  ·
    refine ⟨22734585176297349257745625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30312780235063132343660833 22734585176297349257745625)
    ·
      refine ⟨17050938882223011943309219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22734585176297349257745625 17050938882223011943309219)
      ·
        refine ⟨25576408323334517914963829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17050938882223011943309219 25576408323334517914963829)
        ·
          refine ⟨2397788280312611054527859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25576408323334517914963829 2397788280312611054527859)
          ·
            refine ⟨3596682420468916581791789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2397788280312611054527859 3596682420468916581791789)
            ·
              refine ⟨1348755907675843718171921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3596682420468916581791789 1348755907675843718171921)
              ·
                refine ⟨1011566930756882788628941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1348755907675843718171921 1011566930756882788628941)
                ·
                  refine ⟨379337599033831045735853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011566930756882788628941 379337599033831045735853)
                  ·
                    rfl

theorem cell21_1662204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_1662204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662204 prefixEnd_1662204 := by exact prefixLift 1662204
  have htrace : WordTrace (prefixWord ++ tailWord_1662204) baseStart_1662204 baseEnd_1662204 := by
    simpa [prefixWord, tailWord_1662204, baseEnd_1662204] using wordTrace_append hprefix tailTrace_1662204
  have hstable : (prefixWord ++ tailWord_1662204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662204).length < 2 ^ (prefixWord ++ tailWord_1662204).sum := by decide
  have hdescent : baseEnd_1662204 < baseStart_1662204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662319 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 6]
def baseStart_1662319 : Nat := 118140960795 + 1662319 * 2 ^ 59
def prefixEnd_1662319 : Nat := 4983230072969 + 3 ^ 40 * 1662319 * 2
def baseEnd_1662319 : Nat := 379363843600616401318951

theorem tailTrace_1662319 : CollatzResearch.WordTrace tailWord_1662319 prefixEnd_1662319 379363843600616401318951 := by
  unfold tailWord_1662319
  simp only [CollatzResearch.WordTrace]
  refine ⟨60629754864709639327758011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40419836576473092885172007 60629754864709639327758011)
  ·
    refine ⟨90944632297064458991637017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60629754864709639327758011 90944632297064458991637017)
    ·
      refine ⟨68208474222798344243727763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90944632297064458991637017 68208474222798344243727763)
      ·
        refine ⟨102312711334197516365591645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68208474222798344243727763 102312711334197516365591645)
        ·
          refine ⟨38367266750324068637096867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102312711334197516365591645 38367266750324068637096867)
          ·
            refine ⟨57550900125486102955645301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38367266750324068637096867 57550900125486102955645301)
            ·
              refine ⟨5395396886764322152091747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57550900125486102955645301 5395396886764322152091747)
              ·
                refine ⟨8093095330146483228137621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5395396886764322152091747 8093095330146483228137621)
                ·
                  refine ⟨379363843600616401318951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8093095330146483228137621 379363843600616401318951)
                  ·
                    rfl

theorem cell21_1662319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 6].length) (baseStart_1662319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662319 prefixEnd_1662319 := by exact prefixLift 1662319
  have htrace : WordTrace (prefixWord ++ tailWord_1662319) baseStart_1662319 baseEnd_1662319 := by
    simpa [prefixWord, tailWord_1662319, baseEnd_1662319] using wordTrace_append hprefix tailTrace_1662319
  have hstable : (prefixWord ++ tailWord_1662319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662319).length < 2 ^ (prefixWord ++ tailWord_1662319).sum := by decide
  have hdescent : baseEnd_1662319 < baseStart_1662319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662322 : List Nat := [3, 2, 1, 2, 1, 2, 1, 6, 3]
def baseStart_1662322 : Nat := 118140960795 + 1662322 * 2 ^ 59
def prefixEnd_1662322 : Nat := 4983230072969 + 3 ^ 40 * 1662322 * 2
def baseEnd_1662322 : Nat := 379364528241489062768945

theorem tailTrace_1662322 : CollatzResearch.WordTrace tailWord_1662322 prefixEnd_1662322 379364528241489062768945 := by
  unfold tailWord_1662322
  simp only [CollatzResearch.WordTrace]
  refine ⟨15157466070924692710029305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40419909522465847226744813 15157466070924692710029305)
  ·
    refine ⟨11368099553193519532521979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15157466070924692710029305 11368099553193519532521979)
    ·
      refine ⟨17052149329790279298782969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11368099553193519532521979 17052149329790279298782969)
      ·
        refine ⟨12789111997342709474087227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17052149329790279298782969 12789111997342709474087227)
        ·
          refine ⟨19183667996014064211130841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12789111997342709474087227 19183667996014064211130841)
          ·
            refine ⟨14387750997010548158348131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19183667996014064211130841 14387750997010548158348131)
            ·
              refine ⟨21581626495515822237522197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14387750997010548158348131 21581626495515822237522197)
              ·
                refine ⟨1011638741977304167383853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21581626495515822237522197 1011638741977304167383853)
                ·
                  refine ⟨379364528241489062768945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011638741977304167383853 379364528241489062768945)
                  ·
                    rfl

theorem cell21_1662322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_1662322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662322 prefixEnd_1662322 := by exact prefixLift 1662322
  have htrace : WordTrace (prefixWord ++ tailWord_1662322) baseStart_1662322 baseEnd_1662322 := by
    simpa [prefixWord, tailWord_1662322, baseEnd_1662322] using wordTrace_append hprefix tailTrace_1662322
  have hstable : (prefixWord ++ tailWord_1662322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662322).length < 2 ^ (prefixWord ++ tailWord_1662322).sum := by decide
  have hdescent : baseEnd_1662322 < baseStart_1662322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662356 : List Nat := [2, 4, 2, 1, 2, 3, 1, 3, 3]
def baseStart_1662356 : Nat := 118140960795 + 1662356 * 2 ^ 59
def prefixEnd_1662356 : Nat := 4983230072969 + 3 ^ 40 * 1662356 * 2
def baseEnd_1662356 : Nat := 379372287504712559202209

theorem tailTrace_1662356 : CollatzResearch.WordTrace tailWord_1662356 prefixEnd_1662356 379372287504712559202209 := by
  unfold tailWord_1662356
  simp only [CollatzResearch.WordTrace]
  refine ⟨30315552182787797323427461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40420736243717063097903281 30315552182787797323427461)
  ·
    refine ⟨5684166034272711998142649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30315552182787797323427461 5684166034272711998142649)
    ·
      refine ⟨4263124525704533998606987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5684166034272711998142649 4263124525704533998606987)
      ·
        refine ⟨6394686788556800997910481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4263124525704533998606987 6394686788556800997910481)
        ·
          refine ⟨4796015091417600748432861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6394686788556800997910481 4796015091417600748432861)
          ·
            refine ⟨1798505659281600280662323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4796015091417600748432861 1798505659281600280662323)
            ·
              refine ⟨2697758488922400420993485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1798505659281600280662323 2697758488922400420993485)
              ·
                refine ⟨1011659433345900157872557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2697758488922400420993485 1011659433345900157872557)
                ·
                  refine ⟨379372287504712559202209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011659433345900157872557 379372287504712559202209)
                  ·
                    rfl

theorem cell21_1662356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_1662356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662356 prefixEnd_1662356 := by exact prefixLift 1662356
  have htrace : WordTrace (prefixWord ++ tailWord_1662356) baseStart_1662356 baseEnd_1662356 := by
    simpa [prefixWord, tailWord_1662356, baseEnd_1662356] using wordTrace_append hprefix tailTrace_1662356
  have hstable : (prefixWord ++ tailWord_1662356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662356).length < 2 ^ (prefixWord ++ tailWord_1662356).sum := by decide
  have hdescent : baseEnd_1662356 < baseStart_1662356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662429 : List Nat := [1, 4, 3, 1, 1, 3, 2, 2, 4]
def baseStart_1662429 : Nat := 118140960795 + 1662429 * 2 ^ 59
def prefixEnd_1662429 : Nat := 4983230072969 + 3 ^ 40 * 1662429 * 2
def baseEnd_1662429 : Nat := 379388947099280654485393

theorem tailTrace_1662429 : CollatzResearch.WordTrace tailWord_1662429 prefixEnd_1662429 379388947099280654485393 := by
  unfold tailWord_1662429
  simp only [CollatzResearch.WordTrace]
  refine ⟨60633766894311128114262341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40422511262874085409508227 60633766894311128114262341)
  ·
    refine ⟨11368831292683336521424189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60633766894311128114262341 11368831292683336521424189)
    ·
      refine ⟨4263311734756251195534071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11368831292683336521424189 4263311734756251195534071)
      ·
        refine ⟨6394967602134376793301107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4263311734756251195534071 6394967602134376793301107)
        ·
          refine ⟨9592451403201565189951661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6394967602134376793301107 9592451403201565189951661)
          ·
            refine ⟨3597169276200586946231873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9592451403201565189951661 3597169276200586946231873)
            ·
              refine ⟨2697876957150440209673905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3597169276200586946231873 2697876957150440209673905)
              ·
                refine ⟨2023407717862830157255429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2697876957150440209673905 2023407717862830157255429)
                ·
                  refine ⟨379388947099280654485393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2023407717862830157255429 379388947099280654485393)
                  ·
                    rfl

theorem cell21_1662429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_1662429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662429 prefixEnd_1662429 := by exact prefixLift 1662429
  have htrace : WordTrace (prefixWord ++ tailWord_1662429) baseStart_1662429 baseEnd_1662429 := by
    simpa [prefixWord, tailWord_1662429, baseEnd_1662429] using wordTrace_append hprefix tailTrace_1662429
  have hstable : (prefixWord ++ tailWord_1662429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662429).length < 2 ^ (prefixWord ++ tailWord_1662429).sum := by decide
  have hdescent : baseEnd_1662429 < baseStart_1662429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662474 : List Nat := [3, 1, 2, 2, 2, 2, 1, 5, 3]
def baseStart_1662474 : Nat := 118140960795 + 1662474 * 2 ^ 59
def prefixEnd_1662474 : Nat := 4983230072969 + 3 ^ 40 * 1662474 * 2
def baseEnd_1662474 : Nat := 379399216712370576235301

theorem tailTrace_1662474 : CollatzResearch.WordTrace tailWord_1662474 prefixEnd_1662474 379399216712370576235301 := by
  unfold tailWord_1662474
  simp only [CollatzResearch.WordTrace]
  refine ⟨15158852044787025199912619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40423605452765400533100317 15158852044787025199912619)
  ·
    refine ⟨22738278067180537799868929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15158852044787025199912619 22738278067180537799868929)
    ·
      refine ⟨17053708550385403349901697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22738278067180537799868929 17053708550385403349901697)
      ·
        refine ⟨12790281412789052512426273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17053708550385403349901697 12790281412789052512426273)
        ·
          refine ⟨9592711059591789384319705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12790281412789052512426273 9592711059591789384319705)
          ·
            refine ⟨7194533294693842038239779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9592711059591789384319705 7194533294693842038239779)
            ·
              refine ⟨10791799942040763057359669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7194533294693842038239779 10791799942040763057359669)
              ·
                refine ⟨1011731244566321536627469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10791799942040763057359669 1011731244566321536627469)
                ·
                  refine ⟨379399216712370576235301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011731244566321536627469 379399216712370576235301)
                  ·
                    rfl

theorem cell21_1662474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_1662474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662474 prefixEnd_1662474 := by exact prefixLift 1662474
  have htrace : WordTrace (prefixWord ++ tailWord_1662474) baseStart_1662474 baseEnd_1662474 := by
    simpa [prefixWord, tailWord_1662474, baseEnd_1662474] using wordTrace_append hprefix tailTrace_1662474
  have hstable : (prefixWord ++ tailWord_1662474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662474).length < 2 ^ (prefixWord ++ tailWord_1662474).sum := by decide
  have hdescent : baseEnd_1662474 < baseStart_1662474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662488 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 6]
def baseStart_1662488 : Nat := 118140960795 + 1662488 * 2 ^ 59
def prefixEnd_1662488 : Nat := 4983230072969 + 3 ^ 40 * 1662488 * 2
def baseEnd_1662488 : Nat := 379402411703109663001939

theorem tailTrace_1662488 : CollatzResearch.WordTrace tailWord_1662488 prefixEnd_1662488 379402411703109663001939 := by
  unfold tailWord_1662488
  simp only [CollatzResearch.WordTrace]
  refine ⟨30317959400548690595330059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40423945867398254127106745 30317959400548690595330059)
  ·
    refine ⟨45476939100823035892995089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30317959400548690595330059 45476939100823035892995089)
    ·
      refine ⟨34107704325617276919746317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45476939100823035892995089 34107704325617276919746317)
      ·
        refine ⟨12790389122106478844904869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34107704325617276919746317 12790389122106478844904869)
        ·
          refine ⟨2398197960394964783419663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12790389122106478844904869 2398197960394964783419663)
          ·
            refine ⟨3597296940592447175129495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2398197960394964783419663 3597296940592447175129495)
            ·
              refine ⟨5395945410888670762694243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3597296940592447175129495 5395945410888670762694243)
              ·
                refine ⟨8093918116333006144041365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5395945410888670762694243 8093918116333006144041365)
                ·
                  refine ⟨379402411703109663001939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8093918116333006144041365 379402411703109663001939)
                  ·
                    rfl

theorem cell21_1662488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_1662488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662488 prefixEnd_1662488 := by exact prefixLift 1662488
  have htrace : WordTrace (prefixWord ++ tailWord_1662488) baseStart_1662488 baseEnd_1662488 := by
    simpa [prefixWord, tailWord_1662488, baseEnd_1662488] using wordTrace_append hprefix tailTrace_1662488
  have hstable : (prefixWord ++ tailWord_1662488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662488).length < 2 ^ (prefixWord ++ tailWord_1662488).sum := by decide
  have hdescent : baseEnd_1662488 < baseStart_1662488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662519 : List Nat := [1, 1, 3, 1, 2, 6, 2, 5]
def baseStart_1662519 : Nat := 118140960795 + 1662519 * 2 ^ 59
def prefixEnd_1662519 : Nat := 4983230072969 + 3 ^ 40 * 1662519 * 2
def baseEnd_1662519 : Nat := 126469828775153499328403

theorem tailTrace_1662519 : CollatzResearch.WordTrace tailWord_1662519 prefixEnd_1662519 126469828775153499328403 := by
  unfold tailWord_1662519
  simp only [CollatzResearch.WordTrace]
  refine ⟨60637049463985073485038611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40424699642656715656692407 60637049463985073485038611)
  ·
    refine ⟨90955574195977610227557917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60637049463985073485038611 90955574195977610227557917)
    ·
      refine ⟨34108340323491603835334219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90955574195977610227557917 34108340323491603835334219)
      ·
        refine ⟨51162510485237405753001329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34108340323491603835334219 51162510485237405753001329)
        ·
          refine ⟨38371882863928054314750997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51162510485237405753001329 38371882863928054314750997)
          ·
            refine ⟨1798682009246627546003953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38371882863928054314750997 1798682009246627546003953)
            ·
              refine ⟨1349011506934970659502965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1798682009246627546003953 1349011506934970659502965)
              ·
                refine ⟨126469828775153499328403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1349011506934970659502965 126469828775153499328403)
                ·
                  rfl

theorem cell21_1662519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 5].length) (baseStart_1662519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662519 prefixEnd_1662519 := by exact prefixLift 1662519
  have htrace : WordTrace (prefixWord ++ tailWord_1662519) baseStart_1662519 baseEnd_1662519 := by
    simpa [prefixWord, tailWord_1662519, baseEnd_1662519] using wordTrace_append hprefix tailTrace_1662519
  have hstable : (prefixWord ++ tailWord_1662519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662519).length < 2 ^ (prefixWord ++ tailWord_1662519).sum := by decide
  have hdescent : baseEnd_1662519 < baseStart_1662519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662564 : List Nat := [2, 3, 1, 1, 2, 4, 1, 3, 4]
def baseStart_1662564 : Nat := 118140960795 + 1662564 * 2 ^ 59
def prefixEnd_1662564 : Nat := 4983230072969 + 3 ^ 40 * 1662564 * 2
def baseEnd_1662564 : Nat := 379419755938550419735117

theorem tailTrace_1662564 : CollatzResearch.WordTrace tailWord_1662564 prefixEnd_1662564 379419755938550419735117 := by
  unfold tailWord_1662564
  simp only [CollatzResearch.WordTrace]
  refine ⟨30319345374411023085213373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40425793832548030780284497 30319345374411023085213373)
  ·
    refine ⟨11369754515404133656955015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30319345374411023085213373 11369754515404133656955015)
    ·
      refine ⟨17054631773106200485432523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11369754515404133656955015 17054631773106200485432523)
      ·
        refine ⟨25581947659659300728148785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17054631773106200485432523 25581947659659300728148785)
        ·
          refine ⟨19186460744744475546111589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25581947659659300728148785 19186460744744475546111589)
          ·
            refine ⟨3597461389639589164895923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19186460744744475546111589 3597461389639589164895923)
            ·
              refine ⟨5396192084459383747343885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3597461389639589164895923 5396192084459383747343885)
              ·
                refine ⟨2023572031672268905253957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5396192084459383747343885 2023572031672268905253957)
                ·
                  refine ⟨379419755938550419735117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2023572031672268905253957 379419755938550419735117)
                  ·
                    rfl

theorem cell21_1662564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_1662564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662564 prefixEnd_1662564 := by exact prefixLift 1662564
  have htrace : WordTrace (prefixWord ++ tailWord_1662564) baseStart_1662564 baseEnd_1662564 := by
    simpa [prefixWord, tailWord_1662564, baseEnd_1662564] using wordTrace_append hprefix tailTrace_1662564
  have hstable : (prefixWord ++ tailWord_1662564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662564).length < 2 ^ (prefixWord ++ tailWord_1662564).sum := by decide
  have hdescent : baseEnd_1662564 < baseStart_1662564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662578 : List Nat := [3, 2, 1, 2, 3, 1, 2, 7]
def baseStart_1662578 : Nat := 118140960795 + 1662578 * 2 ^ 59
def prefixEnd_1662578 : Nat := 4983230072969 + 3 ^ 40 * 1662578 * 2
def baseEnd_1662578 : Nat := 126474316976429835500585

theorem tailTrace_1662578 : CollatzResearch.WordTrace tailWord_1662578 prefixEnd_1662578 126474316976429835500585 := by
  unfold tailWord_1662578
  simp only [CollatzResearch.WordTrace]
  refine ⟨15159800342692831640359097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40426134247180884374290925 15159800342692831640359097)
  ·
    refine ⟨11369850257019623730269323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15159800342692831640359097 11369850257019623730269323)
    ·
      refine ⟨17054775385529435595403985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11369850257019623730269323 17054775385529435595403985)
      ·
        refine ⟨12791081539147076696552989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17054775385529435595403985 12791081539147076696552989)
        ·
          refine ⟨4796655577180153761207371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12791081539147076696552989 4796655577180153761207371)
          ·
            refine ⟨7194983365770230641811057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4796655577180153761207371 7194983365770230641811057)
            ·
              refine ⟨5396237524327672981358293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7194983365770230641811057 5396237524327672981358293)
              ·
                refine ⟨126474316976429835500585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5396237524327672981358293 126474316976429835500585)
                ·
                  rfl

theorem cell21_1662578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_1662578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662578 prefixEnd_1662578 := by exact prefixLift 1662578
  have htrace : WordTrace (prefixWord ++ tailWord_1662578) baseStart_1662578 baseEnd_1662578 := by
    simpa [prefixWord, tailWord_1662578, baseEnd_1662578] using wordTrace_append hprefix tailTrace_1662578
  have hstable : (prefixWord ++ tailWord_1662578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662578).length < 2 ^ (prefixWord ++ tailWord_1662578).sum := by decide
  have hdescent : baseEnd_1662578 < baseStart_1662578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662612 : List Nat := [2, 4, 2, 2, 2, 2, 1, 6]
def baseStart_1662612 : Nat := 118140960795 + 1662612 * 2 ^ 59
def prefixEnd_1662612 : Nat := 4983230072969 + 3 ^ 40 * 1662612 * 2
def baseEnd_1662612 : Nat := 126476903397504334311673

theorem tailTrace_1662612 : CollatzResearch.WordTrace tailWord_1662612 prefixEnd_1662612 126476903397504334311673 := by
  unfold tailWord_1662612
  simp only [CollatzResearch.WordTrace]
  refine ⟨30320220726324075184087045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40426960968432100245449393 30320220726324075184087045)
  ·
    refine ⟨5685041386185764097016321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30320220726324075184087045 5685041386185764097016321)
    ·
      refine ⟨4263781039639323072762241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5685041386185764097016321 4263781039639323072762241)
      ·
        refine ⟨3197835779729492304571681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4263781039639323072762241 3197835779729492304571681)
        ·
          refine ⟨2398376834797119228428761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3197835779729492304571681 2398376834797119228428761)
          ·
            refine ⟨1798782626097839421321571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2398376834797119228428761 1798782626097839421321571)
            ·
              refine ⟨2698173939146759131982357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1798782626097839421321571 2698173939146759131982357)
              ·
                refine ⟨126476903397504334311673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2698173939146759131982357 126476903397504334311673)
                ·
                  rfl

theorem cell21_1662612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 6].length) (baseStart_1662612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662612 prefixEnd_1662612 := by exact prefixLift 1662612
  have htrace : WordTrace (prefixWord ++ tailWord_1662612) baseStart_1662612 baseEnd_1662612 := by
    simpa [prefixWord, tailWord_1662612, baseEnd_1662612] using wordTrace_append hprefix tailTrace_1662612
  have hstable : (prefixWord ++ tailWord_1662612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662612).length < 2 ^ (prefixWord ++ tailWord_1662612).sum := by decide
  have hdescent : baseEnd_1662612 < baseStart_1662612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662654 : List Nat := [4, 2, 1, 1, 2, 3, 8]
def baseStart_1662654 : Nat := 118140960795 + 1662654 * 2 ^ 59
def prefixEnd_1662654 : Nat := 4983230072969 + 3 ^ 40 * 1662654 * 2
def baseEnd_1662654 : Nat := 42160032796081140359437

theorem tailTrace_1662654 : CollatzResearch.WordTrace tailWord_1662654 prefixEnd_1662654 42160032796081140359437 := by
  unfold tailWord_1662654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7580246664811998942650377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40427982212330661027468677 7580246664811998942650377)
  ·
    refine ⟨5685184998608999206987783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7580246664811998942650377 5685184998608999206987783)
    ·
      refine ⟨8527777497913498810481675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5685184998608999206987783 8527777497913498810481675)
      ·
        refine ⟨12791666246870248215722513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8527777497913498810481675 12791666246870248215722513)
        ·
          refine ⟨9593749685152686161791885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12791666246870248215722513 9593749685152686161791885)
          ·
            refine ⟨3597656131932257310671957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9593749685152686161791885 3597656131932257310671957)
            ·
              refine ⟨42160032796081140359437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3597656131932257310671957 42160032796081140359437)
              ·
                rfl

theorem cell21_1662654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 8].length) (baseStart_1662654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662654 prefixEnd_1662654 := by exact prefixLift 1662654
  have htrace : WordTrace (prefixWord ++ tailWord_1662654) baseStart_1662654 baseEnd_1662654 := by
    simpa [prefixWord, tailWord_1662654, baseEnd_1662654] using wordTrace_append hprefix tailTrace_1662654
  have hstable : (prefixWord ++ tailWord_1662654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662654).length < 2 ^ (prefixWord ++ tailWord_1662654).sum := by decide
  have hdescent : baseEnd_1662654 < baseStart_1662654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662730 : List Nat := [3, 1, 2, 2, 1, 4, 2, 6]
def baseStart_1662730 : Nat := 118140960795 + 1662730 * 2 ^ 59
def prefixEnd_1662730 : Nat := 4983230072969 + 3 ^ 40 * 1662730 * 2
def baseEnd_1662730 : Nat := 126485879800057006656037

theorem tailTrace_1662730 : CollatzResearch.WordTrace tailWord_1662730 prefixEnd_1662730 126485879800057006656037 := by
  unfold tailWord_1662730
  simp only [CollatzResearch.WordTrace]
  refine ⟨15161186316555164130242411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40429830177480437680646429 15161186316555164130242411)
  ·
    refine ⟨22741779474832746195363617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15161186316555164130242411 22741779474832746195363617)
    ·
      refine ⟨17056334606124559646522713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22741779474832746195363617 17056334606124559646522713)
      ·
        refine ⟨12792250954593419734892035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17056334606124559646522713 12792250954593419734892035)
        ·
          refine ⟨19188376431890129602338053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12792250954593419734892035 19188376431890129602338053)
          ·
            refine ⟨3597820580979399300438385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19188376431890129602338053 3597820580979399300438385)
            ·
              refine ⟨2698365435734549475328789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3597820580979399300438385 2698365435734549475328789)
              ·
                refine ⟨126485879800057006656037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2698365435734549475328789 126485879800057006656037)
                ·
                  rfl

theorem cell21_1662730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_1662730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662730 prefixEnd_1662730 := by exact prefixLift 1662730
  have htrace : WordTrace (prefixWord ++ tailWord_1662730) baseStart_1662730 baseEnd_1662730 := by
    simpa [prefixWord, tailWord_1662730, baseEnd_1662730] using wordTrace_append hprefix tailTrace_1662730
  have hstable : (prefixWord ++ tailWord_1662730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662730).length < 2 ^ (prefixWord ++ tailWord_1662730).sum := by decide
  have hdescent : baseEnd_1662730 < baseStart_1662730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662744 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 5]
def baseStart_1662744 : Nat := 118140960795 + 1662744 * 2 ^ 59
def prefixEnd_1662744 : Nat := 4983230072969 + 3 ^ 40 * 1662744 * 2
def baseEnd_1662744 : Nat := 379460834390910106734749

theorem tailTrace_1662744 : CollatzResearch.WordTrace tailWord_1662744 prefixEnd_1662744 379460834390910106734749 := by
  unfold tailWord_1662744
  simp only [CollatzResearch.WordTrace]
  refine ⟨30322627944084968455989643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40430170592113291274652857 30322627944084968455989643)
  ·
    refine ⟨45483941916127452683984465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30322627944084968455989643 45483941916127452683984465)
    ·
      refine ⟨34112956437095589512988349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45483941916127452683984465 34112956437095589512988349)
      ·
        refine ⟨12792358663910846067370631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34112956437095589512988349 12792358663910846067370631)
        ·
          refine ⟨19188537995866269101055947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12792358663910846067370631 19188537995866269101055947)
          ·
            refine ⟨28782806993799403651583921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19188537995866269101055947 28782806993799403651583921)
            ·
              refine ⟨21587105245349552738687941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28782806993799403651583921 21587105245349552738687941)
              ·
                refine ⟨4047582233503041138503989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21587105245349552738687941 4047582233503041138503989)
                ·
                  refine ⟨379460834390910106734749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4047582233503041138503989 379460834390910106734749)
                  ·
                    rfl

theorem cell21_1662744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_1662744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662744 prefixEnd_1662744 := by exact prefixLift 1662744
  have htrace : WordTrace (prefixWord ++ tailWord_1662744) baseStart_1662744 baseEnd_1662744 := by
    simpa [prefixWord, tailWord_1662744, baseEnd_1662744] using wordTrace_append hprefix tailTrace_1662744
  have hstable : (prefixWord ++ tailWord_1662744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662744).length < 2 ^ (prefixWord ++ tailWord_1662744).sum := by decide
  have hdescent : baseEnd_1662744 < baseStart_1662744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662778 : List Nat := [3, 1, 1, 1, 5, 2, 1, 4, 3]
def baseStart_1662778 : Nat := 118140960795 + 1662778 * 2 ^ 59
def prefixEnd_1662778 : Nat := 4983230072969 + 3 ^ 40 * 1662778 * 2
def baseEnd_1662778 : Nat := 379468593654133603168013

theorem tailTrace_1662778 : CollatzResearch.WordTrace tailWord_1662778 prefixEnd_1662778 379468593654133603168013 := by
  unfold tailWord_1662778
  simp only [CollatzResearch.WordTrace]
  refine ⟨15161623992511690179679247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40430997313364507145811325 15161623992511690179679247)
  ·
    refine ⟨22742435988767535269518871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15161623992511690179679247 22742435988767535269518871)
    ·
      refine ⟨34113653983151302904278307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22742435988767535269518871 34113653983151302904278307)
      ·
        refine ⟨51170480974726954356417461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34113653983151302904278307 51170480974726954356417461)
        ·
          refine ⟨4797232591380651970914137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51170480974726954356417461 4797232591380651970914137)
          ·
            refine ⟨3597924443535488978185603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4797232591380651970914137 3597924443535488978185603)
            ·
              refine ⟨5396886665303233467278405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3597924443535488978185603 5396886665303233467278405)
              ·
                refine ⟨1011916249744356275114701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5396886665303233467278405 1011916249744356275114701)
                ·
                  refine ⟨379468593654133603168013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011916249744356275114701 379468593654133603168013)
                  ·
                    rfl

theorem cell21_1662778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_1662778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662778 prefixEnd_1662778 := by exact prefixLift 1662778
  have htrace : WordTrace (prefixWord ++ tailWord_1662778) baseStart_1662778 baseEnd_1662778 := by
    simpa [prefixWord, tailWord_1662778, baseEnd_1662778] using wordTrace_append hprefix tailTrace_1662778
  have hstable : (prefixWord ++ tailWord_1662778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662778).length < 2 ^ (prefixWord ++ tailWord_1662778).sum := by decide
  have hdescent : baseEnd_1662778 < baseStart_1662778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662826 : List Nat := [3, 1, 3, 4, 1, 2, 1, 2, 4]
def baseStart_1662826 : Nat := 118140960795 + 1662826 * 2 ^ 59
def prefixEnd_1662826 : Nat := 4983230072969 + 3 ^ 40 * 1662826 * 2
def baseEnd_1662826 : Nat := 379479547908096186367915

theorem tailTrace_1662826 : CollatzResearch.WordTrace tailWord_1662826 prefixEnd_1662826 379479547908096186367915 := by
  unfold tailWord_1662826
  simp only [CollatzResearch.WordTrace]
  refine ⟨15162061668468216229116083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40432164449248576610976221 15162061668468216229116083)
  ·
    refine ⟨22743092502702324343674125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15162061668468216229116083 22743092502702324343674125)
    ·
      refine ⟨8528659688513371628877797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22743092502702324343674125 8528659688513371628877797)
      ·
        refine ⟨1599123691596257180414587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8528659688513371628877797 1599123691596257180414587)
        ·
          refine ⟨2398685537394385770621881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599123691596257180414587 2398685537394385770621881)
          ·
            refine ⟨1799014153045789327966411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2398685537394385770621881 1799014153045789327966411)
            ·
              refine ⟨2698521229568683991949617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799014153045789327966411 2698521229568683991949617)
              ·
                refine ⟨2023890922176512993962213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2698521229568683991949617 2023890922176512993962213)
                ·
                  refine ⟨379479547908096186367915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2023890922176512993962213 379479547908096186367915)
                  ·
                    rfl

theorem cell21_1662826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_1662826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662826 prefixEnd_1662826 := by exact prefixLift 1662826
  have htrace : WordTrace (prefixWord ++ tailWord_1662826) baseStart_1662826 baseEnd_1662826 := by
    simpa [prefixWord, tailWord_1662826, baseEnd_1662826] using wordTrace_append hprefix tailTrace_1662826
  have hstable : (prefixWord ++ tailWord_1662826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662826).length < 2 ^ (prefixWord ++ tailWord_1662826).sum := by decide
  have hdescent : baseEnd_1662826 < baseStart_1662826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662837 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 5]
def baseStart_1662837 : Nat := 118140960795 + 1662837 * 2 ^ 59
def prefixEnd_1662837 : Nat := 4983230072969 + 3 ^ 40 * 1662837 * 2
def baseEnd_1662837 : Nat := 379482058257962611684559

theorem tailTrace_1662837 : CollatzResearch.WordTrace tailWord_1662837 prefixEnd_1662837 379482058257962611684559 := by
  unfold tailWord_1662837
  simp only [CollatzResearch.WordTrace]
  refine ⟨60648647876833013795114765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40432431917888675863409843 60648647876833013795114765)
  ·
    refine ⟨22743242953812380173168037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60648647876833013795114765 22743242953812380173168037)
    ·
      refine ⟨4264358053839821282469007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22743242953812380173168037 4264358053839821282469007)
      ·
        refine ⟨6396537080759731923703511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4264358053839821282469007 6396537080759731923703511)
        ·
          refine ⟨9594805621139597885555267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6396537080759731923703511 9594805621139597885555267)
          ·
            refine ⟨14392208431709396828332901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9594805621139597885555267 14392208431709396828332901)
            ·
              refine ⟨2698539080945511905312419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14392208431709396828332901 2698539080945511905312419)
              ·
                refine ⟨4047808621418267857968629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2698539080945511905312419 4047808621418267857968629)
                ·
                  refine ⟨379482058257962611684559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4047808621418267857968629 379482058257962611684559)
                  ·
                    rfl

theorem cell21_1662837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_1662837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662837 prefixEnd_1662837 := by exact prefixLift 1662837
  have htrace : WordTrace (prefixWord ++ tailWord_1662837) baseStart_1662837 baseEnd_1662837 := by
    simpa [prefixWord, tailWord_1662837, baseEnd_1662837] using wordTrace_append hprefix tailTrace_1662837
  have hstable : (prefixWord ++ tailWord_1662837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662837).length < 2 ^ (prefixWord ++ tailWord_1662837).sum := by decide
  have hdescent : baseEnd_1662837 < baseStart_1662837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662888 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 5]
def baseStart_1662888 : Nat := 118140960795 + 1662888 * 2 ^ 59
def prefixEnd_1662888 : Nat := 4983230072969 + 3 ^ 40 * 1662888 * 2
def baseEnd_1662888 : Nat := 379493697152797856334455

theorem tailTrace_1662888 : CollatzResearch.WordTrace tailWord_1662888 prefixEnd_1662888 379493697152797856334455 := by
  unfold tailWord_1662888
  simp only [CollatzResearch.WordTrace]
  refine ⟨30325253999824124752610659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40433671999765499670147545 30325253999824124752610659)
  ·
    refine ⟨45487880999736187128915989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30325253999824124752610659 45487880999736187128915989)
    ·
      refine ⟨2132244421862633771667937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45487880999736187128915989 2132244421862633771667937)
      ·
        refine ⟨1599183316396975328750953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2132244421862633771667937 1599183316396975328750953)
        ·
          refine ⟨1199387487297731496563215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1599183316396975328750953 1199387487297731496563215)
          ·
            refine ⟨1799081230946597244844823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199387487297731496563215 1799081230946597244844823)
            ·
              refine ⟨2698621846419895867267235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799081230946597244844823 2698621846419895867267235)
              ·
                refine ⟨4047932769629843800900853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2698621846419895867267235 4047932769629843800900853)
                ·
                  refine ⟨379493697152797856334455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4047932769629843800900853 379493697152797856334455)
                  ·
                    rfl

theorem cell21_1662888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 5].length) (baseStart_1662888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662888 prefixEnd_1662888 := by exact prefixLift 1662888
  have htrace : WordTrace (prefixWord ++ tailWord_1662888) baseStart_1662888 baseEnd_1662888 := by
    simpa [prefixWord, tailWord_1662888, baseEnd_1662888] using wordTrace_append hprefix tailTrace_1662888
  have hstable : (prefixWord ++ tailWord_1662888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662888).length < 2 ^ (prefixWord ++ tailWord_1662888).sum := by decide
  have hdescent : baseEnd_1662888 < baseStart_1662888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662941 : List Nat := [1, 4, 3, 1, 12]
def baseStart_1662941 : Nat := 118140960795 + 1662941 * 2 ^ 59
def prefixEnd_1662941 : Nat := 4983230072969 + 3 ^ 40 * 1662941 * 2
def baseEnd_1662941 : Nat := 4685256697220759777173

theorem tailTrace_1662941 : CollatzResearch.WordTrace tailWord_1662941 prefixEnd_1662941 4685256697220759777173 := by
  unfold tailWord_1662941
  simp only [CollatzResearch.WordTrace]
  refine ⟨60652441068456239556900677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40434960712304159704600451 60652441068456239556900677)
  ·
    refine ⟨11372332700335544916918877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60652441068456239556900677 11372332700335544916918877)
    ·
      refine ⟨4264624762625829343844579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11372332700335544916918877 4264624762625829343844579)
      ·
        refine ⟨6396937143938744015766869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4264624762625829343844579 6396937143938744015766869)
        ·
          refine ⟨4685256697220759777173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6396937143938744015766869 4685256697220759777173)
          ·
            rfl

theorem cell21_1662941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 12].length) (baseStart_1662941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662941 prefixEnd_1662941 := by exact prefixLift 1662941
  have htrace : WordTrace (prefixWord ++ tailWord_1662941) baseStart_1662941 baseEnd_1662941 := by
    simpa [prefixWord, tailWord_1662941, baseEnd_1662941] using wordTrace_append hprefix tailTrace_1662941
  have hstable : (prefixWord ++ tailWord_1662941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662941).length < 2 ^ (prefixWord ++ tailWord_1662941).sum := by decide
  have hdescent : baseEnd_1662941 < baseStart_1662941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662947 : List Nat := [1, 1, 1, 6, 1, 4, 2, 2, 3]
def baseStart_1662947 : Nat := 118140960795 + 1662947 * 2 ^ 59
def prefixEnd_1662947 : Nat := 4983230072969 + 3 ^ 40 * 1662947 * 2
def baseEnd_1662947 : Nat := 379507161756626864851001

theorem tailTrace_1662947 : CollatzResearch.WordTrace tailWord_1662947 prefixEnd_1662947 379507161756626864851001 := by
  unfold tailWord_1662947
  simp only [CollatzResearch.WordTrace]
  refine ⟨60652659906434502581619095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40435106604289668387746063 60652659906434502581619095)
  ·
    refine ⟨90978989859651753872428643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60652659906434502581619095 90978989859651753872428643)
    ·
      refine ⟨136468484789477630808642965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90978989859651753872428643 136468484789477630808642965)
      ·
        refine ⟨6396960224506763944155139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136468484789477630808642965 6396960224506763944155139)
        ·
          refine ⟨9595440336760145916232709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6396960224506763944155139 9595440336760145916232709)
          ·
            refine ⟨1799145063142527359293633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9595440336760145916232709 1799145063142527359293633)
            ·
              refine ⟨1349358797356895519470225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1799145063142527359293633 1349358797356895519470225)
              ·
                refine ⟨1012019098017671639602669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1349358797356895519470225 1012019098017671639602669)
                ·
                  refine ⟨379507161756626864851001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1012019098017671639602669 379507161756626864851001)
                  ·
                    rfl

theorem cell21_1662947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 3].length) (baseStart_1662947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662947 prefixEnd_1662947 := by exact prefixLift 1662947
  have htrace : WordTrace (prefixWord ++ tailWord_1662947) baseStart_1662947 baseEnd_1662947 := by
    simpa [prefixWord, tailWord_1662947, baseEnd_1662947] using wordTrace_append hprefix tailTrace_1662947
  have hstable : (prefixWord ++ tailWord_1662947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662947).length < 2 ^ (prefixWord ++ tailWord_1662947).sum := by decide
  have hdescent : baseEnd_1662947 < baseStart_1662947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662955 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 9]
def baseStart_1662955 : Nat := 118140960795 + 1662955 * 2 ^ 59
def prefixEnd_1662955 : Nat := 4983230072969 + 3 ^ 40 * 1662955 * 2
def baseEnd_1662955 : Nat := 379508987465620628717651

theorem tailTrace_1662955 : CollatzResearch.WordTrace tailWord_1662955 prefixEnd_1662955 379508987465620628717651 := by
  unfold tailWord_1662955
  simp only [CollatzResearch.WordTrace]
  refine ⟨60652951690405519947910319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40435301126937013298606879 60652951690405519947910319)
  ·
    refine ⟨90979427535608279921865479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60652951690405519947910319 90979427535608279921865479)
    ·
      refine ⟨136469141303412419882798219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90979427535608279921865479 136469141303412419882798219)
      ·
        refine ⟨204703711955118629824197329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136469141303412419882798219 204703711955118629824197329)
        ·
          refine ⟨153527783966338972368147997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204703711955118629824197329 153527783966338972368147997)
          ·
            refine ⟨57572918987377114638055499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153527783966338972368147997 57572918987377114638055499)
            ·
              refine ⟨86359378481065671957083249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57572918987377114638055499 86359378481065671957083249)
              ·
                refine ⟨64769533860799253967812437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86359378481065671957083249 64769533860799253967812437)
                ·
                  refine ⟨379508987465620628717651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64769533860799253967812437 379508987465620628717651)
                  ·
                    rfl

theorem cell21_1662955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 9].length) (baseStart_1662955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662955 prefixEnd_1662955 := by exact prefixLift 1662955
  have htrace : WordTrace (prefixWord ++ tailWord_1662955) baseStart_1662955 baseEnd_1662955 := by
    simpa [prefixWord, tailWord_1662955, baseEnd_1662955] using wordTrace_append hprefix tailTrace_1662955
  have hstable : (prefixWord ++ tailWord_1662955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662955).length < 2 ^ (prefixWord ++ tailWord_1662955).sum := by decide
  have hdescent : baseEnd_1662955 < baseStart_1662955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662958 : List Nat := [4, 1, 2, 1, 3, 1, 3, 6]
def baseStart_1662958 : Nat := 118140960795 + 1662958 * 2 ^ 59
def prefixEnd_1662958 : Nat := 4983230072969 + 3 ^ 40 * 1662958 * 2
def baseEnd_1662958 : Nat := 126503224035497763389215

theorem tailTrace_1662958 : CollatzResearch.WordTrace tailWord_1662958 prefixEnd_1662958 126503224035497763389215 := by
  unfold tailWord_1662958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7581632638674331432533691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40435374072929767640179685 7581632638674331432533691)
  ·
    refine ⟨11372448958011497148800537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7581632638674331432533691 11372448958011497148800537)
    ·
      refine ⟨8529336718508622861600403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11372448958011497148800537 8529336718508622861600403)
      ·
        refine ⟨12794005077762934292400605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8529336718508622861600403 12794005077762934292400605)
        ·
          refine ⟨4797751904161100359650227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12794005077762934292400605 4797751904161100359650227)
          ·
            refine ⟨7196627856241650539475341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4797751904161100359650227 7196627856241650539475341)
            ·
              refine ⟨2698735446090618952303253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7196627856241650539475341 2698735446090618952303253)
              ·
                refine ⟨126503224035497763389215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2698735446090618952303253 126503224035497763389215)
                ·
                  rfl

theorem cell21_1662958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_1662958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662958 prefixEnd_1662958 := by exact prefixLift 1662958
  have htrace : WordTrace (prefixWord ++ tailWord_1662958) baseStart_1662958 baseEnd_1662958 := by
    simpa [prefixWord, tailWord_1662958, baseEnd_1662958] using wordTrace_append hprefix tailTrace_1662958
  have hstable : (prefixWord ++ tailWord_1662958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662958).length < 2 ^ (prefixWord ++ tailWord_1662958).sum := by decide
  have hdescent : baseEnd_1662958 < baseStart_1662958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662972 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 5]
def baseStart_1662972 : Nat := 118140960795 + 1662972 * 2 ^ 59
def prefixEnd_1662972 : Nat := 4983230072969 + 3 ^ 40 * 1662972 * 2
def baseEnd_1662972 : Nat := 379512867097232376934283

theorem tailTrace_1662972 : CollatzResearch.WordTrace tailWord_1662972 prefixEnd_1662972 379512867097232376934283 := by
  unfold tailWord_1662972
  simp only [CollatzResearch.WordTrace]
  refine ⟨30326785865671965925639585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40435714487562621234186113 30326785865671965925639585)
  ·
    refine ⟨22745089399253974444229689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30326785865671965925639585 22745089399253974444229689)
    ·
      refine ⟨17058817049440480833172267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22745089399253974444229689 17058817049440480833172267)
      ·
        refine ⟨25588225574160721249758401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17058817049440480833172267 25588225574160721249758401)
        ·
          refine ⟨19191169180620540937318801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25588225574160721249758401 19191169180620540937318801)
          ·
            refine ⟨14393376885465405702989101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19191169180620540937318801 14393376885465405702989101)
            ·
              refine ⟨5397516332049527138620913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14393376885465405702989101 5397516332049527138620913)
              ·
                refine ⟨4048137249037145353965685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5397516332049527138620913 4048137249037145353965685)
                ·
                  refine ⟨379512867097232376934283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4048137249037145353965685 379512867097232376934283)
                  ·
                    rfl

theorem cell21_1662972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_1662972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1662972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1662972 prefixEnd_1662972 := by exact prefixLift 1662972
  have htrace : WordTrace (prefixWord ++ tailWord_1662972) baseStart_1662972 baseEnd_1662972 := by
    simpa [prefixWord, tailWord_1662972, baseEnd_1662972] using wordTrace_append hprefix tailTrace_1662972
  have hstable : (prefixWord ++ tailWord_1662972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662972).length < 2 ^ (prefixWord ++ tailWord_1662972).sum := by decide
  have hdescent : baseEnd_1662972 < baseStart_1662972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663079 : List Nat := [1, 1, 5, 1, 1, 2, 3, 3, 4]
def baseStart_1663079 : Nat := 118140960795 + 1663079 * 2 ^ 59
def prefixEnd_1663079 : Nat := 4983230072969 + 3 ^ 40 * 1663079 * 2
def baseEnd_1663079 : Nat := 379537285955023968650731

theorem tailTrace_1663079 : CollatzResearch.WordTrace tailWord_1663079 prefixEnd_1663079 379537285955023968650731 := by
  unfold tailWord_1663079
  simp only [CollatzResearch.WordTrace]
  refine ⟨60657474341956289125424291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40438316227970859416949527 60657474341956289125424291)
  ·
    refine ⟨90986211512934433688136437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60657474341956289125424291 90986211512934433688136437)
    ·
      refine ⟨8529957329337603158262791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90986211512934433688136437 8529957329337603158262791)
      ·
        refine ⟨12794935994006404737394187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8529957329337603158262791 12794935994006404737394187)
        ·
          refine ⟨19192403991009607106091281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12794935994006404737394187 19192403991009607106091281)
          ·
            refine ⟨14394302993257205329568461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19192403991009607106091281 14394302993257205329568461)
            ·
              refine ⟨5397863622471451998588173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14394302993257205329568461 5397863622471451998588173)
              ·
                refine ⟨2024198858426794499470565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5397863622471451998588173 2024198858426794499470565)
                ·
                  refine ⟨379537285955023968650731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2024198858426794499470565 379537285955023968650731)
                  ·
                    rfl

theorem cell21_1663079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 4].length) (baseStart_1663079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1663079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1663079 prefixEnd_1663079 := by exact prefixLift 1663079
  have htrace : WordTrace (prefixWord ++ tailWord_1663079) baseStart_1663079 baseEnd_1663079 := by
    simpa [prefixWord, tailWord_1663079, baseEnd_1663079] using wordTrace_append hprefix tailTrace_1663079
  have hstable : (prefixWord ++ tailWord_1663079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663079).length < 2 ^ (prefixWord ++ tailWord_1663079).sum := by decide
  have hdescent : baseEnd_1663079 < baseStart_1663079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663127 : List Nat := [1, 1, 3, 3, 5, 1, 1, 6]
def baseStart_1663127 : Nat := 118140960795 + 1663127 * 2 ^ 59
def prefixEnd_1663127 : Nat := 4983230072969 + 3 ^ 40 * 1663127 * 2
def baseEnd_1663127 : Nat := 126516080069662183950211

theorem tailTrace_1663127 : CollatzResearch.WordTrace tailWord_1663127 prefixEnd_1663127 126516080069662183950211 := by
  unfold tailWord_1663127
  simp only [CollatzResearch.WordTrace]
  refine ⟨60659225045782393323171635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40439483363854928882114423 60659225045782393323171635)
  ·
    refine ⟨90988837568673589984757453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60659225045782393323171635 90988837568673589984757453)
    ·
      refine ⟨34120814088252596244284045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90988837568673589984757453 34120814088252596244284045)
      ·
        refine ⟨12795305283094723591606517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34120814088252596244284045 12795305283094723591606517)
        ·
          refine ⟨1199559870290130336713111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12795305283094723591606517 1199559870290130336713111)
          ·
            refine ⟨1799339805435195505069667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199559870290130336713111 1799339805435195505069667)
            ·
              refine ⟨2699009708152793257604501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799339805435195505069667 2699009708152793257604501)
              ·
                refine ⟨126516080069662183950211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2699009708152793257604501 126516080069662183950211)
                ·
                  rfl

theorem cell21_1663127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 6].length) (baseStart_1663127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1663127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1663127 prefixEnd_1663127 := by exact prefixLift 1663127
  have htrace : WordTrace (prefixWord ++ tailWord_1663127) baseStart_1663127 baseEnd_1663127 := by
    simpa [prefixWord, tailWord_1663127, baseEnd_1663127] using wordTrace_append hprefix tailTrace_1663127
  have hstable : (prefixWord ++ tailWord_1663127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663127).length < 2 ^ (prefixWord ++ tailWord_1663127).sum := by decide
  have hdescent : baseEnd_1663127 < baseStart_1663127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663172 : List Nat := [2, 3, 3, 1, 2, 1, 3, 2, 4]
def baseStart_1663172 : Nat := 118140960795 + 1663172 * 2 ^ 59
def prefixEnd_1663172 : Nat := 4983230072969 + 3 ^ 40 * 1663172 * 2
def baseEnd_1663172 : Nat := 379558509822076473600541

theorem tailTrace_1663172 : CollatzResearch.WordTrace tailWord_1663172 prefixEnd_1663172 379558509822076473600541 := by
  unfold tailWord_1663172
  simp only [CollatzResearch.WordTrace]
  refine ⟨30330433165309683004279885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40440577553746244005706513 30330433165309683004279885)
  ·
    refine ⟨11373912436991131126604957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30330433165309683004279885 11373912436991131126604957)
    ·
      refine ⟨4265217163871674172476859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11373912436991131126604957 4265217163871674172476859)
      ·
        refine ⟨6397825745807511258715289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4265217163871674172476859 6397825745807511258715289)
        ·
          refine ⟨4798369309355633444036467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6397825745807511258715289 4798369309355633444036467)
          ·
            refine ⟨7197553964033450166054701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4798369309355633444036467 7197553964033450166054701)
            ·
              refine ⟨2699082736512543812270513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7197553964033450166054701 2699082736512543812270513)
              ·
                refine ⟨2024312052384407859202885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2699082736512543812270513 2024312052384407859202885)
                ·
                  refine ⟨379558509822076473600541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2024312052384407859202885 379558509822076473600541)
                  ·
                    rfl

theorem cell21_1663172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_1663172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1663172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1663172 prefixEnd_1663172 := by exact prefixLift 1663172
  have htrace : WordTrace (prefixWord ++ tailWord_1663172) baseStart_1663172 baseEnd_1663172 := by
    simpa [prefixWord, tailWord_1663172, baseEnd_1663172] using wordTrace_append hprefix tailTrace_1663172
  have hstable : (prefixWord ++ tailWord_1663172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663172).length < 2 ^ (prefixWord ++ tailWord_1663172).sum := by decide
  have hdescent : baseEnd_1663172 < baseStart_1663172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663189 : List Nat := [1, 3, 2, 4, 2, 1, 3, 1, 4]
def baseStart_1663189 : Nat := 118140960795 + 1663189 * 2 ^ 59
def prefixEnd_1663189 : Nat := 4983230072969 + 3 ^ 40 * 1663189 * 2
def baseEnd_1663189 : Nat := 379562389453688221817173

theorem tailTrace_1663189 : CollatzResearch.WordTrace tailWord_1663189 prefixEnd_1663189 379562389453688221817173 := by
  unfold tailWord_1663189
  simp only [CollatzResearch.WordTrace]
  refine ⟨60661486371557777911928621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40440990914371851941285747 60661486371557777911928621)
  ·
    refine ⟨22748057389334166716973233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60661486371557777911928621 22748057389334166716973233)
    ·
      refine ⟨17061043042000625037729925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22748057389334166716973233 17061043042000625037729925)
      ·
        refine ⟨3198945570375117194574361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17061043042000625037729925 3198945570375117194574361)
        ·
          refine ⟨2399209177781337895930771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3198945570375117194574361 2399209177781337895930771)
          ·
            refine ⟨3598813766672006843896157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399209177781337895930771 3598813766672006843896157)
            ·
              refine ⟨1349555162502002566461059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3598813766672006843896157 1349555162502002566461059)
              ·
                refine ⟨2024332743753003849691589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349555162502002566461059 2024332743753003849691589)
                ·
                  refine ⟨379562389453688221817173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2024332743753003849691589 379562389453688221817173)
                  ·
                    rfl

theorem cell21_1663189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_1663189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1663189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1663189 prefixEnd_1663189 := by exact prefixLift 1663189
  have htrace : WordTrace (prefixWord ++ tailWord_1663189) baseStart_1663189 baseEnd_1663189 := by
    simpa [prefixWord, tailWord_1663189, baseEnd_1663189] using wordTrace_append hprefix tailTrace_1663189
  have hstable : (prefixWord ++ tailWord_1663189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663189).length < 2 ^ (prefixWord ++ tailWord_1663189).sum := by decide
  have hdescent : baseEnd_1663189 < baseStart_1663189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663217 : List Nat := [1, 2, 2, 2, 2, 1, 5, 3, 3]
def baseStart_1663217 : Nat := 118140960795 + 1663217 * 2 ^ 59
def prefixEnd_1663217 : Nat := 4983230072969 + 3 ^ 40 * 1663217 * 2
def baseEnd_1663217 : Nat := 379568779435166395350449

theorem tailTrace_1663217 : CollatzResearch.WordTrace tailWord_1663217 prefixEnd_1663217 379568779435166395350449 := by
  unfold tailWord_1663217
  simp only [CollatzResearch.WordTrace]
  refine ⟨60662507615456338693947905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40441671743637559129298603 60662507615456338693947905)
  ·
    refine ⟨45496880711592254020460929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60662507615456338693947905 45496880711592254020460929)
    ·
      refine ⟨34122660533694190515345697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45496880711592254020460929 34122660533694190515345697)
      ·
        refine ⟨25591995400270642886509273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34122660533694190515345697 25591995400270642886509273)
        ·
          refine ⟨19193996550202982164881955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25591995400270642886509273 19193996550202982164881955)
          ·
            refine ⟨28790994825304473247322933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19193996550202982164881955 28790994825304473247322933)
            ·
              refine ⟨2699155764872294366936525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28790994825304473247322933 2699155764872294366936525)
              ·
                refine ⟨1012183411827110387601197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2699155764872294366936525 1012183411827110387601197)
                ·
                  refine ⟨379568779435166395350449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1012183411827110387601197 379568779435166395350449)
                  ·
                    rfl

theorem cell21_1663217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 3].length) (baseStart_1663217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1663217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1663217 prefixEnd_1663217 := by exact prefixLift 1663217
  have htrace : WordTrace (prefixWord ++ tailWord_1663217) baseStart_1663217 baseEnd_1663217 := by
    simpa [prefixWord, tailWord_1663217, baseEnd_1663217] using wordTrace_append hprefix tailTrace_1663217
  have hstable : (prefixWord ++ tailWord_1663217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663217).length < 2 ^ (prefixWord ++ tailWord_1663217).sum := by decide
  have hdescent : baseEnd_1663217 < baseStart_1663217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663234 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1663234 : Nat := 118140960795 + 1663234 * 2 ^ 59
def prefixEnd_1663234 : Nat := 4983230072969 + 3 ^ 40 * 1663234 * 2
def baseEnd_1663234 : Nat := 379572659066778143567081

theorem tailTrace_1663234 : CollatzResearch.WordTrace tailWord_1663234 prefixEnd_1663234 379572659066778143567081 := by
  unfold tailWord_1663234
  simp only [CollatzResearch.WordTrace]
  refine ⟨15165781914098687649329189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40442085104263167064877837 15165781914098687649329189)
  ·
    refine ⟨2843584108893503934249223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15165781914098687649329189 2843584108893503934249223)
    ·
      refine ⟨4265376163340255901373835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2843584108893503934249223 4265376163340255901373835)
      ·
        refine ⟨6398064245010383852060753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4265376163340255901373835 6398064245010383852060753)
        ·
          refine ⟨4798548183757787889045565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6398064245010383852060753 4798548183757787889045565)
          ·
            refine ⟨1799455568909170458392087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4798548183757787889045565 1799455568909170458392087)
            ·
              refine ⟨2699183353363755687588131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799455568909170458392087 2699183353363755687588131)
              ·
                refine ⟨4048775030045633531382197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2699183353363755687588131 4048775030045633531382197)
                ·
                  refine ⟨379572659066778143567081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4048775030045633531382197 379572659066778143567081)
                  ·
                    rfl

theorem cell21_1663234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1663234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1663234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1663234 prefixEnd_1663234 := by exact prefixLift 1663234
  have htrace : WordTrace (prefixWord ++ tailWord_1663234) baseStart_1663234 baseEnd_1663234 := by
    simpa [prefixWord, tailWord_1663234, baseEnd_1663234] using wordTrace_append hprefix tailTrace_1663234
  have hstable : (prefixWord ++ tailWord_1663234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663234).length < 2 ^ (prefixWord ++ tailWord_1663234).sum := by decide
  have hdescent : baseEnd_1663234 < baseStart_1663234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663259 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 5]
def baseStart_1663259 : Nat := 118140960795 + 1663259 * 2 ^ 59
def prefixEnd_1663259 : Nat := 4983230072969 + 3 ^ 40 * 1663259 * 2
def baseEnd_1663259 : Nat := 379578364407383655650363

theorem tailTrace_1663259 : CollatzResearch.WordTrace tailWord_1663259 prefixEnd_1663259 379578364407383655650363 := by
  unfold tailWord_1663259
  simp only [CollatzResearch.WordTrace]
  refine ⟨60664039481304179866976831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40442692987536119911317887 60664039481304179866976831)
  ·
    refine ⟨90996059221956269800465247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60664039481304179866976831 90996059221956269800465247)
    ·
      refine ⟨136494088832934404700697871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90996059221956269800465247 136494088832934404700697871)
      ·
        refine ⟨204741133249401607051046807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136494088832934404700697871 204741133249401607051046807)
        ·
          refine ⟨307111699874102410576570211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204741133249401607051046807 307111699874102410576570211)
          ·
            refine ⟨460667549811153615864855317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307111699874102410576570211 460667549811153615864855317)
            ·
              refine ⟨21593791397397825743665093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 460667549811153615864855317 21593791397397825743665093)
              ·
                refine ⟨4048835887012092326937205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21593791397397825743665093 4048835887012092326937205)
                ·
                  refine ⟨379578364407383655650363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4048835887012092326937205 379578364407383655650363)
                  ·
                    rfl

theorem cell21_1663259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 5].length) (baseStart_1663259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1663259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1663259 prefixEnd_1663259 := by exact prefixLift 1663259
  have htrace : WordTrace (prefixWord ++ tailWord_1663259) baseStart_1663259 baseEnd_1663259 := by
    simpa [prefixWord, tailWord_1663259, baseEnd_1663259] using wordTrace_append hprefix tailTrace_1663259
  have hstable : (prefixWord ++ tailWord_1663259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663259).length < 2 ^ (prefixWord ++ tailWord_1663259).sum := by decide
  have hdescent : baseEnd_1663259 < baseStart_1663259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663386 : List Nat := [3, 1, 1, 4, 1, 4, 1, 3, 3]
def baseStart_1663386 : Nat := 118140960795 + 1663386 * 2 ^ 59
def prefixEnd_1663386 : Nat := 4983230072969 + 3 ^ 40 * 1663386 * 2
def baseEnd_1663386 : Nat := 379607347537659657033437

theorem tailTrace_1663386 : CollatzResearch.WordTrace tailWord_1663386 prefixEnd_1663386 379607347537659657033437 := by
  unfold tailWord_1663386
  simp only [CollatzResearch.WordTrace]
  refine ⟨15167167887961020139212503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40445781034562720371233341 15167167887961020139212503)
  ·
    refine ⟨22750751831941530208818755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15167167887961020139212503 22750751831941530208818755)
    ·
      refine ⟨34126127747912295313228133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22750751831941530208818755 34126127747912295313228133)
      ·
        refine ⟨6398648952733555371230275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34126127747912295313228133 6398648952733555371230275)
        ·
          refine ⟨9597973429100333056845413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6398648952733555371230275 9597973429100333056845413)
          ·
            refine ⟨1799620017956312448158515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9597973429100333056845413 1799620017956312448158515)
            ·
              refine ⟨2699430026934468672237773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799620017956312448158515 2699430026934468672237773)
              ·
                refine ⟨1012286260100425752089165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2699430026934468672237773 1012286260100425752089165)
                ·
                  refine ⟨379607347537659657033437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1012286260100425752089165 379607347537659657033437)
                  ·
                    rfl

theorem cell21_1663386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_1663386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1663386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1663386 prefixEnd_1663386 := by exact prefixLift 1663386
  have htrace : WordTrace (prefixWord ++ tailWord_1663386) baseStart_1663386 baseEnd_1663386 := by
    simpa [prefixWord, tailWord_1663386, baseEnd_1663386] using wordTrace_append hprefix tailTrace_1663386
  have hstable : (prefixWord ++ tailWord_1663386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663386).length < 2 ^ (prefixWord ++ tailWord_1663386).sum := by decide
  have hdescent : baseEnd_1663386 < baseStart_1663386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663487 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 5]
def baseStart_1663487 : Nat := 118140960795 + 1663487 * 2 ^ 59
def prefixEnd_1663487 : Nat := 4983230072969 + 3 ^ 40 * 1663487 * 2
def baseEnd_1663487 : Nat := 379630397113705925849897

theorem tailTrace_1663487 : CollatzResearch.WordTrace tailWord_1663487 prefixEnd_1663487 379630397113705925849897 := by
  unfold tailWord_1663487
  simp only [CollatzResearch.WordTrace]
  refine ⟨60672355324478174806276715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40448236882985449870851143 60672355324478174806276715)
  ·
    refine ⟨91008532986717262209415073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60672355324478174806276715 91008532986717262209415073)
    ·
      refine ⟨68256399740037946657061305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91008532986717262209415073 68256399740037946657061305)
      ·
        refine ⟨51192299805028459992795979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68256399740037946657061305 51192299805028459992795979)
        ·
          refine ⟨76788449707542689989193969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51192299805028459992795979 76788449707542689989193969)
          ·
            refine ⟨57591337280657017491895477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76788449707542689989193969 57591337280657017491895477)
            ·
              refine ⟨5399187870061595389865201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57591337280657017491895477 5399187870061595389865201)
              ·
                refine ⟨4049390902546196542398901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5399187870061595389865201 4049390902546196542398901)
                ·
                  refine ⟨379630397113705925849897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4049390902546196542398901 379630397113705925849897)
                  ·
                    rfl

theorem cell21_1663487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 5].length) (baseStart_1663487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1663487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1663487 prefixEnd_1663487 := by exact prefixLift 1663487
  have htrace : WordTrace (prefixWord ++ tailWord_1663487) baseStart_1663487 baseEnd_1663487 := by
    simpa [prefixWord, tailWord_1663487, baseEnd_1663487] using wordTrace_append hprefix tailTrace_1663487
  have hstable : (prefixWord ++ tailWord_1663487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663487).length < 2 ^ (prefixWord ++ tailWord_1663487).sum := by decide
  have hdescent : baseEnd_1663487 < baseStart_1663487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663549 : List Nat := [1, 4, 1, 3, 2, 2, 1, 7]
def baseStart_1663549 : Nat := 118140960795 + 1663549 * 2 ^ 59
def prefixEnd_1663549 : Nat := 4983230072969 + 3 ^ 40 * 1663549 * 2
def baseEnd_1663549 : Nat := 126548182119469198605479

theorem tailTrace_1663549 : CollatzResearch.WordTrace tailWord_1663549 prefixEnd_1663549 126548182119469198605479 := by
  unfold tailWord_1663549
  simp only [CollatzResearch.WordTrace]
  refine ⟨60674616650253559395033701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40449744433502372930022467 60674616650253559395033701)
  ·
    refine ⟨11376490621922542386568819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60674616650253559395033701 11376490621922542386568819)
    ·
      refine ⟨17064735932883813579853229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11376490621922542386568819 17064735932883813579853229)
      ·
        refine ⟨6399275974831430092444961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17064735932883813579853229 6399275974831430092444961)
        ·
          refine ⟨4799456981123572569333721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6399275974831430092444961 4799456981123572569333721)
          ·
            refine ⟨3599592735842679427000291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4799456981123572569333721 3599592735842679427000291)
            ·
              refine ⟨5399389103764019140500437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3599592735842679427000291 5399389103764019140500437)
              ·
                refine ⟨126548182119469198605479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5399389103764019140500437 126548182119469198605479)
                ·
                  rfl

theorem cell21_1663549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 7].length) (baseStart_1663549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1663549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1663549 prefixEnd_1663549 := by exact prefixLift 1663549
  have htrace : WordTrace (prefixWord ++ tailWord_1663549) baseStart_1663549 baseEnd_1663549 := by
    simpa [prefixWord, tailWord_1663549, baseEnd_1663549] using wordTrace_append hprefix tailTrace_1663549
  have hstable : (prefixWord ++ tailWord_1663549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663549).length < 2 ^ (prefixWord ++ tailWord_1663549).sum := by decide
  have hdescent : baseEnd_1663549 < baseStart_1663549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663586 : List Nat := [3, 3, 2, 3, 1, 2, 2, 1, 4]
def baseStart_1663586 : Nat := 118140960795 + 1663586 * 2 ^ 59
def prefixEnd_1663586 : Nat := 4983230072969 + 3 ^ 40 * 1663586 * 2
def baseEnd_1663586 : Nat := 379652990262503753699695

theorem tailTrace_1663586 : CollatzResearch.WordTrace tailWord_1663586 prefixEnd_1663586 379652990262503753699695 := by
  unfold tailWord_1663586
  simp only [CollatzResearch.WordTrace]
  refine ⟨15168991537779878678532653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40450644100746343142753741 15168991537779878678532653)
  ·
    refine ⟨5688371826667454504449745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15168991537779878678532653 5688371826667454504449745)
    ·
      refine ⟨4266278870000590878337309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5688371826667454504449745 4266278870000590878337309)
      ·
        refine ⟨1599854576250221579376491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4266278870000590878337309 1599854576250221579376491)
        ·
          refine ⟨2399781864375332369064737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599854576250221579376491 2399781864375332369064737)
          ·
            refine ⟨1799836398281499276798553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2399781864375332369064737 1799836398281499276798553)
            ·
              refine ⟨1349877298711124457598915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1799836398281499276798553 1349877298711124457598915)
              ·
                refine ⟨2024815948066686686398373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349877298711124457598915 2024815948066686686398373)
                ·
                  refine ⟨379652990262503753699695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2024815948066686686398373 379652990262503753699695)
                  ·
                    rfl

theorem cell21_1663586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_1663586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1663586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1663586 prefixEnd_1663586 := by exact prefixLift 1663586
  have htrace : WordTrace (prefixWord ++ tailWord_1663586) baseStart_1663586 baseEnd_1663586 := by
    simpa [prefixWord, tailWord_1663586, baseEnd_1663586] using wordTrace_append hprefix tailTrace_1663586
  have hstable : (prefixWord ++ tailWord_1663586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663586).length < 2 ^ (prefixWord ++ tailWord_1663586).sum := by decide
  have hdescent : baseEnd_1663586 < baseStart_1663586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663639 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 5]
def baseStart_1663639 : Nat := 118140960795 + 1663639 * 2 ^ 59
def prefixEnd_1663639 : Nat := 4983230072969 + 3 ^ 40 * 1663639 * 2
def baseEnd_1663639 : Nat := 379665085584587439316253

theorem tailTrace_1663639 : CollatzResearch.WordTrace tailWord_1663639 prefixEnd_1663639 379665085584587439316253 := by
  unfold tailWord_1663639
  simp only [CollatzResearch.WordTrace]
  refine ⟨60677899219927504765809971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40451932813285003177206647 60677899219927504765809971)
  ·
    refine ⟨91016848829891257148714957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60677899219927504765809971 91016848829891257148714957)
    ·
      refine ⟨34131318311209221430768109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91016848829891257148714957 34131318311209221430768109)
      ·
        refine ⟨12799244366703458036538041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34131318311209221430768109 12799244366703458036538041)
        ·
          refine ⟨9599433275027593527403531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12799244366703458036538041 9599433275027593527403531)
          ·
            refine ⟨14399149912541390291105297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9599433275027593527403531 14399149912541390291105297)
            ·
              refine ⟨10799362434406042718328973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14399149912541390291105297 10799362434406042718328973)
              ·
                refine ⟨4049760912902266019373365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10799362434406042718328973 4049760912902266019373365)
                ·
                  refine ⟨379665085584587439316253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4049760912902266019373365 379665085584587439316253)
                  ·
                    rfl

theorem cell21_1663639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 5].length) (baseStart_1663639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1663639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1663639 prefixEnd_1663639 := by exact prefixLift 1663639
  have htrace : WordTrace (prefixWord ++ tailWord_1663639) baseStart_1663639 baseEnd_1663639 := by
    simpa [prefixWord, tailWord_1663639, baseEnd_1663639] using wordTrace_append hprefix tailTrace_1663639
  have hstable : (prefixWord ++ tailWord_1663639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663639).length < 2 ^ (prefixWord ++ tailWord_1663639).sum := by decide
  have hdescent : baseEnd_1663639 < baseStart_1663639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663653 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 8]
def baseStart_1663653 : Nat := 118140960795 + 1663653 * 2 ^ 59
def prefixEnd_1663653 : Nat := 4983230072969 + 3 ^ 40 * 1663653 * 2
def baseEnd_1663653 : Nat := 379668280575326526082891

theorem tailTrace_1663653 : CollatzResearch.WordTrace tailWord_1663653 prefixEnd_1663653 379668280575326526082891 := by
  unfold tailWord_1663653
  simp only [CollatzResearch.WordTrace]
  refine ⟨60678409841876785156819613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40452273227917856771213075 60678409841876785156819613)
  ·
    refine ⟨22754403690703794433807355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60678409841876785156819613 22754403690703794433807355)
    ·
      refine ⟨34131605536055691650711033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22754403690703794433807355 34131605536055691650711033)
      ·
        refine ⟨25598704152041768738033275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34131605536055691650711033 25598704152041768738033275)
        ·
          refine ⟨38398056228062653107049913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25598704152041768738033275 38398056228062653107049913)
          ·
            refine ⟨28798542171046989830287435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38398056228062653107049913 28798542171046989830287435)
            ·
              refine ⟨43197813256570484745431153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28798542171046989830287435 43197813256570484745431153)
              ·
                refine ⟨32398359942427863559073365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43197813256570484745431153 32398359942427863559073365)
                ·
                  refine ⟨379668280575326526082891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32398359942427863559073365 379668280575326526082891)
                  ·
                    rfl

theorem cell21_1663653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_1663653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1663653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1663653 prefixEnd_1663653 := by exact prefixLift 1663653
  have htrace : WordTrace (prefixWord ++ tailWord_1663653) baseStart_1663653 baseEnd_1663653 := by
    simpa [prefixWord, tailWord_1663653, baseEnd_1663653] using wordTrace_append hprefix tailTrace_1663653
  have hstable : (prefixWord ++ tailWord_1663653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663653).length < 2 ^ (prefixWord ++ tailWord_1663653).sum := by decide
  have hdescent : baseEnd_1663653 < baseStart_1663653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663729 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 8]
def baseStart_1663729 : Nat := 118140960795 + 1663729 * 2 ^ 59
def prefixEnd_1663729 : Nat := 4983230072969 + 3 ^ 40 * 1663729 * 2
def baseEnd_1663729 : Nat := 379685624810767282816069

theorem tailTrace_1663729 : CollatzResearch.WordTrace tailWord_1663729 prefixEnd_1663729 379685624810767282816069 := by
  unfold tailWord_1663729
  simp only [CollatzResearch.WordTrace]
  refine ⟨60681181789601450136586241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40454121193067633424390827 60681181789601450136586241)
  ·
    refine ⟨45510886342201087602439681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60681181789601450136586241 45510886342201087602439681)
    ·
      refine ⟨34133164756650815701829761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45510886342201087602439681 34133164756650815701829761)
      ·
        refine ⟨25599873567488111776372321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34133164756650815701829761 25599873567488111776372321)
        ·
          refine ⟨19199905175616083832279241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25599873567488111776372321 19199905175616083832279241)
          ·
            refine ⟨14399928881712062874209431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19199905175616083832279241 14399928881712062874209431)
            ·
              refine ⟨21599893322568094311314147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14399928881712062874209431 21599893322568094311314147)
              ·
                refine ⟨32399839983852141466971221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21599893322568094311314147 32399839983852141466971221)
                ·
                  refine ⟨379685624810767282816069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32399839983852141466971221 379685624810767282816069)
                  ·
                    rfl

theorem cell21_1663729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_1663729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1663729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1663729 prefixEnd_1663729 := by exact prefixLift 1663729
  have htrace : WordTrace (prefixWord ++ tailWord_1663729) baseStart_1663729 baseEnd_1663729 := by
    simpa [prefixWord, tailWord_1663729, baseEnd_1663729] using wordTrace_append hprefix tailTrace_1663729
  have hstable : (prefixWord ++ tailWord_1663729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663729).length < 2 ^ (prefixWord ++ tailWord_1663729).sum := by decide
  have hdescent : baseEnd_1663729 < baseStart_1663729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663842 : List Nat := [3, 3, 2, 1, 3, 1, 2, 3, 3]
def baseStart_1663842 : Nat := 118140960795 + 1663842 * 2 ^ 59
def prefixEnd_1663842 : Nat := 4983230072969 + 3 ^ 40 * 1663842 * 2
def baseEnd_1663842 : Nat := 379711412950304197432505

theorem tailTrace_1663842 : CollatzResearch.WordTrace tailWord_1663842 prefixEnd_1663842 379711412950304197432505 := by
  unfold tailWord_1663842
  simp only [CollatzResearch.WordTrace]
  refine ⟨15171325809548017608862445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40456868825461380290299853 15171325809548017608862445)
  ·
    refine ⟨5689247178580506603323417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15171325809548017608862445 5689247178580506603323417)
    ·
      refine ⟨4266935383935379952492563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5689247178580506603323417 4266935383935379952492563)
      ·
        refine ⟨6400403075903069928738845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4266935383935379952492563 6400403075903069928738845)
        ·
          refine ⟨2400151153463651223277067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6400403075903069928738845 2400151153463651223277067)
          ·
            refine ⟨3600226730195476834915601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2400151153463651223277067 3600226730195476834915601)
            ·
              refine ⟨2700170047646607626186701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3600226730195476834915601 2700170047646607626186701)
              ·
                refine ⟨1012563767867477859820013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2700170047646607626186701 1012563767867477859820013)
                ·
                  refine ⟨379711412950304197432505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1012563767867477859820013 379711412950304197432505)
                  ·
                    rfl

theorem cell21_1663842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_1663842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1663842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1663842 prefixEnd_1663842 := by exact prefixLift 1663842
  have htrace : WordTrace (prefixWord ++ tailWord_1663842) baseStart_1663842 baseEnd_1663842 := by
    simpa [prefixWord, tailWord_1663842, baseEnd_1663842] using wordTrace_append hprefix tailTrace_1663842
  have hstable : (prefixWord ++ tailWord_1663842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663842).length < 2 ^ (prefixWord ++ tailWord_1663842).sum := by decide
  have hdescent : baseEnd_1663842 < baseStart_1663842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664036 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 5]
def baseStart_1664036 : Nat := 118140960795 + 1664036 * 2 ^ 59
def prefixEnd_1664036 : Nat := 4983230072969 + 3 ^ 40 * 1664036 * 2
def baseEnd_1664036 : Nat := 379755686393402971198775

theorem tailTrace_1664036 : CollatzResearch.WordTrace tailWord_1664036 prefixEnd_1664036 379755686393402971198775 := by
  unfold tailWord_1664036
  simp only [CollatzResearch.WordTrace]
  refine ⟨30346189499744620784005981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40461585999659494378674641 30346189499744620784005981)
  ·
    refine ⟨11379821062404232794002243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30346189499744620784005981 11379821062404232794002243)
    ·
      refine ⟨17069731593606349191003365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11379821062404232794002243 17069731593606349191003365)
      ·
        refine ⟨3200574673801190473313131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17069731593606349191003365 3200574673801190473313131)
        ·
          refine ⟨4800862010701785709969697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3200574673801190473313131 4800862010701785709969697)
          ·
            refine ⟨3600646508026339282477273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4800862010701785709969697 3600646508026339282477273)
            ·
              refine ⟨2700484881019754461857955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3600646508026339282477273 2700484881019754461857955)
              ·
                refine ⟨4050727321529631692786933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2700484881019754461857955 4050727321529631692786933)
                ·
                  refine ⟨379755686393402971198775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4050727321529631692786933 379755686393402971198775)
                  ·
                    rfl

theorem cell21_1664036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_1664036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1664036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1664036 prefixEnd_1664036 := by exact prefixLift 1664036
  have htrace : WordTrace (prefixWord ++ tailWord_1664036) baseStart_1664036 baseEnd_1664036 := by
    simpa [prefixWord, tailWord_1664036, baseEnd_1664036] using wordTrace_append hprefix tailTrace_1664036
  have hstable : (prefixWord ++ tailWord_1664036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664036).length < 2 ^ (prefixWord ++ tailWord_1664036).sum := by decide
  have hdescent : baseEnd_1664036 < baseStart_1664036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664070 : List Nat := [6, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_1664070 : Nat := 118140960795 + 1664070 * 2 ^ 59
def prefixEnd_1664070 : Nat := 4983230072969 + 3 ^ 40 * 1664070 * 2
def baseEnd_1664070 : Nat := 379763445656626467632039

theorem tailTrace_1664070 : CollatzResearch.WordTrace tailWord_1664070 prefixEnd_1664070 379763445656626467632039 := by
  unfold tailWord_1664070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1896675596292689542960927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40462412720910710249833109 1896675596292689542960927)
  ·
    refine ⟨2845013394439034314441391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1896675596292689542960927 2845013394439034314441391)
    ·
      refine ⟨4267520091658551471662087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2845013394439034314441391 4267520091658551471662087)
      ·
        refine ⟨6401280137487827207493131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4267520091658551471662087 6401280137487827207493131)
        ·
          refine ⟨9601920206231740811239697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6401280137487827207493131 9601920206231740811239697)
          ·
            refine ⟨7201440154673805608429773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9601920206231740811239697 7201440154673805608429773)
            ·
              refine ⟨2700540058002677103161165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7201440154673805608429773 2700540058002677103161165)
              ·
                refine ⟨1012702521751003913685437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2700540058002677103161165 1012702521751003913685437)
                ·
                  refine ⟨379763445656626467632039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1012702521751003913685437 379763445656626467632039)
                  ·
                    rfl

theorem cell21_1664070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_1664070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1664070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1664070 prefixEnd_1664070 := by exact prefixLift 1664070
  have htrace : WordTrace (prefixWord ++ tailWord_1664070) baseStart_1664070 baseEnd_1664070 := by
    simpa [prefixWord, tailWord_1664070, baseEnd_1664070] using wordTrace_append hprefix tailTrace_1664070
  have hstable : (prefixWord ++ tailWord_1664070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664070).length < 2 ^ (prefixWord ++ tailWord_1664070).sum := by decide
  have hdescent : baseEnd_1664070 < baseStart_1664070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664146 : List Nat := [3, 2, 3, 1, 1, 4, 2, 2, 3]
def baseStart_1664146 : Nat := 118140960795 + 1664146 * 2 ^ 59
def prefixEnd_1664146 : Nat := 4983230072969 + 3 ^ 40 * 1664146 * 2
def baseEnd_1664146 : Nat := 379780789892067224365217

theorem tailTrace_1664146 : CollatzResearch.WordTrace tailWord_1664146 prefixEnd_1664146 379780789892067224365217 := by
  unfold tailWord_1664146
  simp only [CollatzResearch.WordTrace]
  refine ⟨15174097757272682588629073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40464260686060486903010861 15174097757272682588629073)
  ·
    refine ⟨11380573317954511941471805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15174097757272682588629073 11380573317954511941471805)
    ·
      refine ⟨4267714994232941978051927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11380573317954511941471805 4267714994232941978051927)
      ·
        refine ⟨6401572491349412967077891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4267714994232941978051927 6401572491349412967077891)
        ·
          refine ⟨9602358737024119450616837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6401572491349412967077891 9602358737024119450616837)
          ·
            refine ⟨1800442263192022396990657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9602358737024119450616837 1800442263192022396990657)
            ·
              refine ⟨1350331697394016797742993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1800442263192022396990657 1350331697394016797742993)
              ·
                refine ⟨1012748773045512598307245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1350331697394016797742993 1012748773045512598307245)
                ·
                  refine ⟨379780789892067224365217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1012748773045512598307245 379780789892067224365217)
                  ·
                    rfl

theorem cell21_1664146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_1664146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1664146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1664146 prefixEnd_1664146 := by exact prefixLift 1664146
  have htrace : WordTrace (prefixWord ++ tailWord_1664146) baseStart_1664146 baseEnd_1664146 := by
    simpa [prefixWord, tailWord_1664146, baseEnd_1664146] using wordTrace_append hprefix tailTrace_1664146
  have hstable : (prefixWord ++ tailWord_1664146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664146).length < 2 ^ (prefixWord ++ tailWord_1664146).sum := by decide
  have hdescent : baseEnd_1664146 < baseStart_1664146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664188 : List Nat := [2, 2, 2, 3, 2, 1, 1, 5, 3]
def baseStart_1664188 : Nat := 118140960795 + 1664188 * 2 ^ 59
def prefixEnd_1664188 : Nat := 4983230072969 + 3 ^ 40 * 1664188 * 2
def baseEnd_1664188 : Nat := 379790374864284484665131

theorem tailTrace_1664188 : CollatzResearch.WordTrace tailWord_1664188 prefixEnd_1664188 379790374864284484665131 := by
  unfold tailWord_1664188
  simp only [CollatzResearch.WordTrace]
  refine ⟨30348961447469285763772609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40465281929959047685030145 30348961447469285763772609)
  ·
    refine ⟨22761721085601964322829457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30348961447469285763772609 22761721085601964322829457)
    ·
      refine ⟨17071290814201473242122093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22761721085601964322829457 17071290814201473242122093)
      ·
        refine ⟨6401734055325552465795785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17071290814201473242122093 6401734055325552465795785)
        ·
          refine ⟨4801300541494164349346839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6401734055325552465795785 4801300541494164349346839)
          ·
            refine ⟨7201950812241246524020259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4801300541494164349346839 7201950812241246524020259)
            ·
              refine ⟨10802926218361869786030389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7201950812241246524020259 10802926218361869786030389)
              ·
                refine ⟨1012774332971425292440349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10802926218361869786030389 1012774332971425292440349)
                ·
                  refine ⟨379790374864284484665131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1012774332971425292440349 379790374864284484665131)
                  ·
                    rfl

theorem cell21_1664188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_1664188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1664188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1664188 prefixEnd_1664188 := by exact prefixLift 1664188
  have htrace : WordTrace (prefixWord ++ tailWord_1664188) baseStart_1664188 baseEnd_1664188 := by
    simpa [prefixWord, tailWord_1664188, baseEnd_1664188] using wordTrace_append hprefix tailTrace_1664188
  have hstable : (prefixWord ++ tailWord_1664188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664188).length < 2 ^ (prefixWord ++ tailWord_1664188).sum := by decide
  have hdescent : baseEnd_1664188 < baseStart_1664188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664194 : List Nat := [3, 5, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1664194 : Nat := 118140960795 + 1664194 * 2 ^ 59
def prefixEnd_1664194 : Nat := 4983230072969 + 3 ^ 40 * 1664194 * 2
def baseEnd_1664194 : Nat := 379791744146029807565119

theorem tailTrace_1664194 : CollatzResearch.WordTrace tailWord_1664194 prefixEnd_1664194 379791744146029807565119 := by
  unfold tailWord_1664194
  simp only [CollatzResearch.WordTrace]
  refine ⟨15174535433229208638065909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40465427821944556368175757 15174535433229208638065909)
  ·
    refine ⟨1422612696865238309818679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15174535433229208638065909 1422612696865238309818679)
    ·
      refine ⟨2133919045297857464728019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1422612696865238309818679 2133919045297857464728019)
      ·
        refine ⟨3200878567946786197092029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2133919045297857464728019 3200878567946786197092029)
        ·
          refine ⟨1200329462980044823909511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3200878567946786197092029 1200329462980044823909511)
          ·
            refine ⟨1800494194470067235864267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200329462980044823909511 1800494194470067235864267)
            ·
              refine ⟨2700741291705100853796401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800494194470067235864267 2700741291705100853796401)
              ·
                refine ⟨2025555968778825640347301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2700741291705100853796401 2025555968778825640347301)
                ·
                  refine ⟨379791744146029807565119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2025555968778825640347301 379791744146029807565119)
                  ·
                    rfl

theorem cell21_1664194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1664194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1664194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1664194 prefixEnd_1664194 := by exact prefixLift 1664194
  have htrace : WordTrace (prefixWord ++ tailWord_1664194) baseStart_1664194 baseEnd_1664194 := by
    simpa [prefixWord, tailWord_1664194, baseEnd_1664194] using wordTrace_append hprefix tailTrace_1664194
  have hstable : (prefixWord ++ tailWord_1664194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664194).length < 2 ^ (prefixWord ++ tailWord_1664194).sum := by decide
  have hdescent : baseEnd_1664194 < baseStart_1664194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664202 : List Nat := [3, 1, 2, 1, 3, 2, 3, 2, 4]
def baseStart_1664202 : Nat := 118140960795 + 1664202 * 2 ^ 59
def prefixEnd_1664202 : Nat := 4983230072969 + 3 ^ 40 * 1664202 * 2
def baseEnd_1664202 : Nat := 379793569855023571431769

theorem tailTrace_1664202 : CollatzResearch.WordTrace tailWord_1664202 prefixEnd_1664202 379793569855023571431769 := by
  unfold tailWord_1664202
  simp only [CollatzResearch.WordTrace]
  refine ⟨15174608379221962979638715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40465622344591901279036573 15174608379221962979638715)
  ·
    refine ⟨22761912568832944469458073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15174608379221962979638715 22761912568832944469458073)
    ·
      refine ⟨17071434426624708352093555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22761912568832944469458073 17071434426624708352093555)
      ·
        refine ⟨25607151639937062528140333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17071434426624708352093555 25607151639937062528140333)
        ·
          refine ⟨9602681864976398448052625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25607151639937062528140333 9602681864976398448052625)
          ·
            refine ⟨7202011398732298836039469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9602681864976398448052625 7202011398732298836039469)
            ·
              refine ⟨2700754274524612063514801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7202011398732298836039469 2700754274524612063514801)
              ·
                refine ⟨2025565705893459047636101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2700754274524612063514801 2025565705893459047636101)
                ·
                  refine ⟨379793569855023571431769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2025565705893459047636101 379793569855023571431769)
                  ·
                    rfl

theorem cell21_1664202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_1664202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1664202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1664202 prefixEnd_1664202 := by exact prefixLift 1664202
  have htrace : WordTrace (prefixWord ++ tailWord_1664202) baseStart_1664202 baseEnd_1664202 := by
    simpa [prefixWord, tailWord_1664202, baseEnd_1664202] using wordTrace_append hprefix tailTrace_1664202
  have hstable : (prefixWord ++ tailWord_1664202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664202).length < 2 ^ (prefixWord ++ tailWord_1664202).sum := by decide
  have hdescent : baseEnd_1664202 < baseStart_1664202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664261 : List Nat := [1, 3, 1, 1, 2, 1, 4, 4, 4]
def baseStart_1664261 : Nat := 118140960795 + 1664261 * 2 ^ 59
def prefixEnd_1664261 : Nat := 4983230072969 + 3 ^ 40 * 1664261 * 2
def baseEnd_1664261 : Nat := 379807034458852579948315

theorem tailTrace_1664261 : CollatzResearch.WordTrace tailWord_1664261 prefixEnd_1664261 379807034458852579948315 := by
  unfold tailWord_1664261
  simp only [CollatzResearch.WordTrace]
  refine ⟨60700585423674104994952637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40467056949116069996635091 60700585423674104994952637)
  ·
    refine ⟨22762719533877789373107239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60700585423674104994952637 22762719533877789373107239)
    ·
      refine ⟨34144079300816684059660859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22762719533877789373107239 34144079300816684059660859)
      ·
        refine ⟨51216118951225026089491289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34144079300816684059660859 51216118951225026089491289)
        ·
          refine ⟨38412089213418769567118467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51216118951225026089491289 38412089213418769567118467)
          ·
            refine ⟨57618133820128154350677701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38412089213418769567118467 57618133820128154350677701)
            ·
              refine ⟨10803400091274028940752069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57618133820128154350677701 10803400091274028940752069)
              ·
                refine ⟨2025637517113880426391013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10803400091274028940752069 2025637517113880426391013)
                ·
                  refine ⟨379807034458852579948315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2025637517113880426391013 379807034458852579948315)
                  ·
                    rfl

theorem cell21_1664261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_1664261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1664261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1664261 prefixEnd_1664261 := by exact prefixLift 1664261
  have htrace : WordTrace (prefixWord ++ tailWord_1664261) baseStart_1664261 baseEnd_1664261 := by
    simpa [prefixWord, tailWord_1664261, baseEnd_1664261] using wordTrace_append hprefix tailTrace_1664261
  have hstable : (prefixWord ++ tailWord_1664261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664261).length < 2 ^ (prefixWord ++ tailWord_1664261).sum := by decide
  have hdescent : baseEnd_1664261 < baseStart_1664261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664264 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 5]
def baseStart_1664264 : Nat := 118140960795 + 1664264 * 2 ^ 59
def prefixEnd_1664264 : Nat := 4983230072969 + 3 ^ 40 * 1664264 * 2
def baseEnd_1664264 : Nat := 379807719099725241398309

theorem tailTrace_1664264 : CollatzResearch.WordTrace tailWord_1664264 prefixEnd_1664264 379807719099725241398309 := by
  unfold tailWord_1664264
  simp only [CollatzResearch.WordTrace]
  refine ⟨30350347421331618253655923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40467129895108824338207897 30350347421331618253655923)
  ·
    refine ⟨45525521131997427380483885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30350347421331618253655923 45525521131997427380483885)
    ·
      refine ⟨17072070424499035267681457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45525521131997427380483885 17072070424499035267681457)
      ·
        refine ⟨12804052818374276450761093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17072070424499035267681457 12804052818374276450761093)
        ·
          refine ⟨2400759903445176834517705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12804052818374276450761093 2400759903445176834517705)
          ·
            refine ⟨1800569927583882625888279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2400759903445176834517705 1800569927583882625888279)
            ·
              refine ⟨2700854891375823938832419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800569927583882625888279 2700854891375823938832419)
              ·
                refine ⟨4051282337063735908248629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2700854891375823938832419 4051282337063735908248629)
                ·
                  refine ⟨379807719099725241398309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4051282337063735908248629 379807719099725241398309)
                  ·
                    rfl

theorem cell21_1664264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_1664264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1664264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1664264 prefixEnd_1664264 := by exact prefixLift 1664264
  have htrace : WordTrace (prefixWord ++ tailWord_1664264) baseStart_1664264 baseEnd_1664264 := by
    simpa [prefixWord, tailWord_1664264, baseEnd_1664264] using wordTrace_append hprefix tailTrace_1664264
  have hstable : (prefixWord ++ tailWord_1664264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664264).length < 2 ^ (prefixWord ++ tailWord_1664264).sum := by decide
  have hdescent : baseEnd_1664264 < baseStart_1664264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664337 : List Nat := [1, 2, 2, 1, 4, 1, 1, 5, 4]
def baseStart_1664337 : Nat := 118140960795 + 1664337 * 2 ^ 59
def prefixEnd_1664337 : Nat := 4983230072969 + 3 ^ 40 * 1664337 * 2
def baseEnd_1664337 : Nat := 379824378694293336681493

theorem tailTrace_1664337 : CollatzResearch.WordTrace tailWord_1664337 prefixEnd_1664337 379824378694293336681493 := by
  unfold tailWord_1664337
  simp only [CollatzResearch.WordTrace]
  refine ⟨60703357371398769974719265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40468904914265846649812843 60703357371398769974719265)
  ·
    refine ⟨45527518028549077481039449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60703357371398769974719265 45527518028549077481039449)
    ·
      refine ⟨34145638521411808110779587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45527518028549077481039449 34145638521411808110779587)
      ·
        refine ⟨51218457782117712166169381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34145638521411808110779587 51218457782117712166169381)
        ·
          refine ⟨9603460834147071031156759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51218457782117712166169381 9603460834147071031156759)
          ·
            refine ⟨14405191251220606546735139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9603460834147071031156759 14405191251220606546735139)
            ·
              refine ⟨21607786876830909820102709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14405191251220606546735139 21607786876830909820102709)
              ·
                refine ⟨2025730019702897795634629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21607786876830909820102709 2025730019702897795634629)
                ·
                  refine ⟨379824378694293336681493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2025730019702897795634629 379824378694293336681493)
                  ·
                    rfl

theorem cell21_1664337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_1664337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1664337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1664337 prefixEnd_1664337 := by exact prefixLift 1664337
  have htrace : WordTrace (prefixWord ++ tailWord_1664337) baseStart_1664337 baseEnd_1664337 := by
    simpa [prefixWord, tailWord_1664337, baseEnd_1664337] using wordTrace_append hprefix tailTrace_1664337
  have hstable : (prefixWord ++ tailWord_1664337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664337).length < 2 ^ (prefixWord ++ tailWord_1664337).sum := by decide
  have hdescent : baseEnd_1664337 < baseStart_1664337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664413 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 6]
def baseStart_1664413 : Nat := 118140960795 + 1664413 * 2 ^ 59
def prefixEnd_1664413 : Nat := 4983230072969 + 3 ^ 40 * 1664413 * 2
def baseEnd_1664413 : Nat := 379841722929734093414671

theorem tailTrace_1664413 : CollatzResearch.WordTrace tailWord_1664413 prefixEnd_1664413 379841722929734093414671 := by
  unfold tailWord_1664413
  simp only [CollatzResearch.WordTrace]
  refine ⟨60706129319123434954485893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40470752879415623302990595 60706129319123434954485893)
  ·
    refine ⟨11382399247335644053966105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60706129319123434954485893 11382399247335644053966105)
    ·
      refine ⟨8536799435501733040474579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11382399247335644053966105 8536799435501733040474579)
      ·
        refine ⟨12805199153252599560711869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8536799435501733040474579 12805199153252599560711869)
        ·
          refine ⟨4801949682469724835266951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12805199153252599560711869 4801949682469724835266951)
          ·
            refine ⟨7202924523704587252900427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4801949682469724835266951 7202924523704587252900427)
            ·
              refine ⟨10804386785556880879350641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7202924523704587252900427 10804386785556880879350641)
              ·
                refine ⟨8103290089167660659512981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10804386785556880879350641 8103290089167660659512981)
                ·
                  refine ⟨379841722929734093414671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8103290089167660659512981 379841722929734093414671)
                  ·
                    rfl

theorem cell21_1664413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_1664413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1664413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1664413 prefixEnd_1664413 := by exact prefixLift 1664413
  have htrace : WordTrace (prefixWord ++ tailWord_1664413) baseStart_1664413 baseEnd_1664413 := by
    simpa [prefixWord, tailWord_1664413, baseEnd_1664413] using wordTrace_append hprefix tailTrace_1664413
  have hstable : (prefixWord ++ tailWord_1664413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664413).length < 2 ^ (prefixWord ++ tailWord_1664413).sum := by decide
  have hdescent : baseEnd_1664413 < baseStart_1664413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664472 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 8]
def baseStart_1664472 : Nat := 118140960795 + 1664472 * 2 ^ 59
def prefixEnd_1664472 : Nat := 4983230072969 + 3 ^ 40 * 1664472 * 2
def baseEnd_1664472 : Nat := 379855187533563101931217

theorem tailTrace_1664472 : CollatzResearch.WordTrace tailWord_1664472 prefixEnd_1664472 379855187533563101931217 := by
  unfold tailWord_1664472
  simp only [CollatzResearch.WordTrace]
  refine ⟨30354140612954844015441835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40472187483939792020589113 30354140612954844015441835)
  ·
    refine ⟨45531210919432266023162753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30354140612954844015441835 45531210919432266023162753)
    ·
      refine ⟨34148408189574199517372065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45531210919432266023162753 34148408189574199517372065)
      ·
        refine ⟨25611306142180649638029049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34148408189574199517372065 25611306142180649638029049)
        ·
          refine ⟨19208479606635487228521787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25611306142180649638029049 19208479606635487228521787)
          ·
            refine ⟨28812719409953230842782681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19208479606635487228521787 28812719409953230842782681)
            ·
              refine ⟨21609539557464923132087011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28812719409953230842782681 21609539557464923132087011)
              ·
                refine ⟨32414309336197384698130517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21609539557464923132087011 32414309336197384698130517)
                ·
                  refine ⟨379855187533563101931217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32414309336197384698130517 379855187533563101931217)
                  ·
                    rfl

theorem cell21_1664472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_1664472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1664472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1664472 prefixEnd_1664472 := by exact prefixLift 1664472
  have htrace : WordTrace (prefixWord ++ tailWord_1664472) baseStart_1664472 baseEnd_1664472 := by
    simpa [prefixWord, tailWord_1664472, baseEnd_1664472] using wordTrace_append hprefix tailTrace_1664472
  have hstable : (prefixWord ++ tailWord_1664472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664472).length < 2 ^ (prefixWord ++ tailWord_1664472).sum := by decide
  have hdescent : baseEnd_1664472 < baseStart_1664472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664672 : List Nat := [2, 1, 1, 4, 3, 3, 1, 6]
def baseStart_1664672 : Nat := 118140960795 + 1664672 * 2 ^ 59
def prefixEnd_1664672 : Nat := 4983230072969 + 3 ^ 40 * 1664672 * 2
def baseEnd_1664672 : Nat := 126633610086135732865825

theorem tailTrace_1664672 : CollatzResearch.WordTrace tailWord_1664672 prefixEnd_1664672 126633610086135732865825 := by
  unfold tailWord_1664672
  simp only [CollatzResearch.WordTrace]
  refine ⟨30357787912592561094082135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40477050550123414792109513 30357787912592561094082135)
  ·
    refine ⟨45536681868888841641123203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30357787912592561094082135 45536681868888841641123203)
    ·
      refine ⟨68305022803333262461684805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45536681868888841641123203 68305022803333262461684805)
      ·
        refine ⟨12807191775624986711565901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68305022803333262461684805 12807191775624986711565901)
        ·
          refine ⟨4802696915859370016837213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12807191775624986711565901 4802696915859370016837213)
          ·
            refine ⟨1801011343447263756313955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4802696915859370016837213 1801011343447263756313955)
            ·
              refine ⟨2701517015170895634470933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1801011343447263756313955 2701517015170895634470933)
              ·
                refine ⟨126633610086135732865825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2701517015170895634470933 126633610086135732865825)
                ·
                  rfl

theorem cell21_1664672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 6].length) (baseStart_1664672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1664672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1664672 prefixEnd_1664672 := by exact prefixLift 1664672
  have htrace : WordTrace (prefixWord ++ tailWord_1664672) baseStart_1664672 baseEnd_1664672 := by
    simpa [prefixWord, tailWord_1664672, baseEnd_1664672] using wordTrace_append hprefix tailTrace_1664672
  have hstable : (prefixWord ++ tailWord_1664672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664672).length < 2 ^ (prefixWord ++ tailWord_1664672).sum := by decide
  have hdescent : baseEnd_1664672 < baseStart_1664672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664703 : List Nat := [1, 1, 2, 2, 2, 3, 4, 3, 3]
def baseStart_1664703 : Nat := 118140960795 + 1664703 * 2 ^ 59
def prefixEnd_1664703 : Nat := 4983230072969 + 3 ^ 40 * 1664703 * 2
def baseEnd_1664703 : Nat := 379907904880758033580745

theorem tailTrace_1664703 : CollatzResearch.WordTrace tailWord_1664703 prefixEnd_1664703 379907904880758033580745 := by
  unfold tailWord_1664703
  simp only [CollatzResearch.WordTrace]
  refine ⟨60716706488072814482542763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40477804325381876321695175 60716706488072814482542763)
  ·
    refine ⟨91075059732109221723814145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60716706488072814482542763 91075059732109221723814145)
    ·
      refine ⟨68306294799081916292860609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91075059732109221723814145 68306294799081916292860609)
      ·
        refine ⟨51229721099311437219645457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68306294799081916292860609 51229721099311437219645457)
        ·
          refine ⟨38422290824483577914734093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51229721099311437219645457 38422290824483577914734093)
          ·
            refine ⟨14408359059181341718025285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38422290824483577914734093 14408359059181341718025285)
            ·
              refine ⟨2701567323596501572129741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14408359059181341718025285 2701567323596501572129741)
              ·
                refine ⟨1013087746348688089548653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2701567323596501572129741 1013087746348688089548653)
                ·
                  refine ⟨379907904880758033580745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013087746348688089548653 379907904880758033580745)
                  ·
                    rfl

theorem cell21_1664703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 3].length) (baseStart_1664703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1664703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1664703 prefixEnd_1664703 := by exact prefixLift 1664703
  have htrace : WordTrace (prefixWord ++ tailWord_1664703) baseStart_1664703 baseEnd_1664703 := by
    simpa [prefixWord, tailWord_1664703, baseEnd_1664703] using wordTrace_append hprefix tailTrace_1664703
  have hstable : (prefixWord ++ tailWord_1664703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664703).length < 2 ^ (prefixWord ++ tailWord_1664703).sum := by decide
  have hdescent : baseEnd_1664703 < baseStart_1664703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664706 : List Nat := [3, 5, 1, 2, 1, 1, 8]
def baseStart_1664706 : Nat := 118140960795 + 1664706 * 2 ^ 59
def prefixEnd_1664706 : Nat := 4983230072969 + 3 ^ 40 * 1664706 * 2
def baseEnd_1664706 : Nat := 42212065502403410558971

theorem tailTrace_1664706 : CollatzResearch.WordTrace tailWord_1664706 prefixEnd_1664706 42212065502403410558971 := by
  unfold tailWord_1664706
  simp only [CollatzResearch.WordTrace]
  refine ⟨15179203976765486498725493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40477877271374630663267981 15179203976765486498725493)
  ·
    refine ⟨1423050372821764359255515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15179203976765486498725493 1423050372821764359255515)
    ·
      refine ⟨2134575559232646538883273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1423050372821764359255515 2134575559232646538883273)
      ·
        refine ⟨1600931669424484904162455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2134575559232646538883273 1600931669424484904162455)
        ·
          refine ⟨2401397504136727356243683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1600931669424484904162455 2401397504136727356243683)
          ·
            refine ⟨3602096256205091034365525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401397504136727356243683 3602096256205091034365525)
            ·
              refine ⟨42212065502403410558971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3602096256205091034365525 42212065502403410558971)
              ·
                rfl

theorem cell21_1664706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 8].length) (baseStart_1664706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1664706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1664706 prefixEnd_1664706 := by exact prefixLift 1664706
  have htrace : WordTrace (prefixWord ++ tailWord_1664706) baseStart_1664706 baseEnd_1664706 := by
    simpa [prefixWord, tailWord_1664706, baseEnd_1664706] using wordTrace_append hprefix tailTrace_1664706
  have hstable : (prefixWord ++ tailWord_1664706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664706).length < 2 ^ (prefixWord ++ tailWord_1664706).sum := by decide
  have hdescent : baseEnd_1664706 < baseStart_1664706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664776 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 6]
def baseStart_1664776 : Nat := 118140960795 + 1664776 * 2 ^ 59
def prefixEnd_1664776 : Nat := 4983230072969 + 3 ^ 40 * 1664776 * 2
def baseEnd_1664776 : Nat := 379924564475326128863929

theorem tailTrace_1664776 : CollatzResearch.WordTrace tailWord_1664776 prefixEnd_1664776 379924564475326128863929 := by
  unfold tailWord_1664776
  simp only [CollatzResearch.WordTrace]
  refine ⟨30359684508404173974975091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40479579344538898633300121 30359684508404173974975091)
  ·
    refine ⟨45539526762606260962462637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30359684508404173974975091 45539526762606260962462637)
    ·
      refine ⟨17077322535977347860923489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45539526762606260962462637 17077322535977347860923489)
      ·
        refine ⟨12807991901983010895692617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17077322535977347860923489 12807991901983010895692617)
        ·
          refine ⟨9605993926487258171769463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12807991901983010895692617 9605993926487258171769463)
          ·
            refine ⟨14408990889730887257654195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9605993926487258171769463 14408990889730887257654195)
            ·
              refine ⟨21613486334596330886481293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14408990889730887257654195 21613486334596330886481293)
              ·
                refine ⟨8105057375473624082430485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21613486334596330886481293 8105057375473624082430485)
                ·
                  refine ⟨379924564475326128863929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8105057375473624082430485 379924564475326128863929)
                  ·
                    rfl

theorem cell21_1664776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_1664776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1664776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1664776 prefixEnd_1664776 := by exact prefixLift 1664776
  have htrace : WordTrace (prefixWord ++ tailWord_1664776) baseStart_1664776 baseEnd_1664776 := by
    simpa [prefixWord, tailWord_1664776, baseEnd_1664776] using wordTrace_append hprefix tailTrace_1664776
  have hstable : (prefixWord ++ tailWord_1664776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664776).length < 2 ^ (prefixWord ++ tailWord_1664776).sum := by decide
  have hdescent : baseEnd_1664776 < baseStart_1664776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664886 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_1664886 : Nat := 118140960795 + 1664886 * 2 ^ 59
def prefixEnd_1664886 : Nat := 4983230072969 + 3 ^ 40 * 1664886 * 2
def baseEnd_1664886 : Nat := 379949667973990382030371

theorem tailTrace_1664886 : CollatzResearch.WordTrace tailWord_1664886 prefixEnd_1664886 379949667973990382030371 := by
  unfold tailWord_1664886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3795211315400614796028407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40482254030939891157636341 3795211315400614796028407)
  ·
    refine ⟨5692816973100922194042611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3795211315400614796028407 5692816973100922194042611)
    ·
      refine ⟨8539225459651383291063917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5692816973100922194042611 8539225459651383291063917)
      ·
        refine ⟨3202209547369268734148969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8539225459651383291063917 3202209547369268734148969)
        ·
          refine ⟨2401657160526951550611727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3202209547369268734148969 2401657160526951550611727)
          ·
            refine ⟨3602485740790427325917591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401657160526951550611727 3602485740790427325917591)
            ·
              refine ⟨5403728611185640988876387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3602485740790427325917591 5403728611185640988876387)
              ·
                refine ⟨8105592916778461483314581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5403728611185640988876387 8105592916778461483314581)
                ·
                  refine ⟨379949667973990382030371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8105592916778461483314581 379949667973990382030371)
                  ·
                    rfl

theorem cell21_1664886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_1664886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1664886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1664886 prefixEnd_1664886 := by exact prefixLift 1664886
  have htrace : WordTrace (prefixWord ++ tailWord_1664886) baseStart_1664886 baseEnd_1664886 := by
    simpa [prefixWord, tailWord_1664886, baseEnd_1664886] using wordTrace_append hprefix tailTrace_1664886
  have hstable : (prefixWord ++ tailWord_1664886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664886).length < 2 ^ (prefixWord ++ tailWord_1664886).sum := by decide
  have hdescent : baseEnd_1664886 < baseStart_1664886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665035 : List Nat := [1, 1, 1, 1, 6, 1, 5, 5]
def baseStart_1665035 : Nat := 118140960795 + 1665035 * 2 ^ 59
def prefixEnd_1665035 : Nat := 4983230072969 + 3 ^ 40 * 1665035 * 2
def baseEnd_1665035 : Nat := 126661223934666411348911

theorem tailTrace_1665035 : CollatzResearch.WordTrace tailWord_1665035 prefixEnd_1665035 126661223934666411348911 := by
  unfold tailWord_1665035
  simp only [CollatzResearch.WordTrace]
  refine ⟨60728815522870035183628559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40485877015246690122419039 60728815522870035183628559)
  ·
    refine ⟨91093223284305052775442839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60728815522870035183628559 91093223284305052775442839)
    ·
      refine ⟨136639834926457579163164259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91093223284305052775442839 136639834926457579163164259)
      ·
        refine ⟨204959752389686368744746389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136639834926457579163164259 204959752389686368744746389)
        ·
          refine ⟨9607488393266548534909987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 204959752389686368744746389 9607488393266548534909987)
          ·
            refine ⟨14411232589899822802364981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9607488393266548534909987 14411232589899822802364981)
            ·
              refine ⟨1351053055303108387721717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14411232589899822802364981 1351053055303108387721717)
              ·
                refine ⟨126661223934666411348911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1351053055303108387721717 126661223934666411348911)
                ·
                  rfl

theorem cell21_1665035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 5].length) (baseStart_1665035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665035 prefixEnd_1665035 := by exact prefixLift 1665035
  have htrace : WordTrace (prefixWord ++ tailWord_1665035) baseStart_1665035 baseEnd_1665035 := by
    simpa [prefixWord, tailWord_1665035, baseEnd_1665035] using wordTrace_append hprefix tailTrace_1665035
  have hstable : (prefixWord ++ tailWord_1665035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665035).length < 2 ^ (prefixWord ++ tailWord_1665035).sum := by decide
  have hdescent : baseEnd_1665035 < baseStart_1665035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665066 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 5]
def baseStart_1665066 : Nat := 118140960795 + 1665066 * 2 ^ 59
def prefixEnd_1665066 : Nat := 4983230072969 + 3 ^ 40 * 1665066 * 2
def baseEnd_1665066 : Nat := 379990746426350069030003

theorem tailTrace_1665066 : CollatzResearch.WordTrace tailWord_1665066 prefixEnd_1665066 379990746426350069030003 := by
  unfold tailWord_1665066
  simp only [CollatzResearch.WordTrace]
  refine ⟨15182486546439431869501763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40486630790505151652004701 15182486546439431869501763)
  ·
    refine ⟨22773729819659147804252645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15182486546439431869501763 22773729819659147804252645)
    ·
      refine ⟨4270074341186090213297371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22773729819659147804252645 4270074341186090213297371)
      ·
        refine ⟨6405111511779135319946057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4270074341186090213297371 6405111511779135319946057)
        ·
          refine ⟨4803833633834351489959543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6405111511779135319946057 4803833633834351489959543)
          ·
            refine ⟨7205750450751527234939315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4803833633834351489959543 7205750450751527234939315)
            ·
              refine ⟨10808625676127290852408973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7205750450751527234939315 10808625676127290852408973)
              ·
                refine ⟨4053234628547734069653365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10808625676127290852408973 4053234628547734069653365)
                ·
                  refine ⟨379990746426350069030003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4053234628547734069653365 379990746426350069030003)
                  ·
                    rfl

theorem cell21_1665066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_1665066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665066 prefixEnd_1665066 := by exact prefixLift 1665066
  have htrace : WordTrace (prefixWord ++ tailWord_1665066) baseStart_1665066 baseEnd_1665066 := by
    simpa [prefixWord, tailWord_1665066, baseEnd_1665066] using wordTrace_append hprefix tailTrace_1665066
  have hstable : (prefixWord ++ tailWord_1665066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665066).length < 2 ^ (prefixWord ++ tailWord_1665066).sum := by decide
  have hdescent : baseEnd_1665066 < baseStart_1665066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665086 : List Nat := [4, 2, 1, 3, 3, 1, 2, 5]
def baseStart_1665086 : Nat := 118140960795 + 1665086 * 2 ^ 59
def prefixEnd_1665086 : Nat := 4983230072969 + 3 ^ 40 * 1665086 * 2
def baseEnd_1665086 : Nat := 126665103566278159565543

theorem tailTrace_1665086 : CollatzResearch.WordTrace tailWord_1665086 prefixEnd_1665086 126665103566278159565543 := by
  unfold tailWord_1665086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7591334455710658861716889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40487117097123513929156741 7591334455710658861716889)
  ·
    refine ⟨5693500841782994146287667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7591334455710658861716889 5693500841782994146287667)
    ·
      refine ⟨8540251262674491219431501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5693500841782994146287667 8540251262674491219431501)
      ·
        refine ⟨3202594223502934207286813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8540251262674491219431501 3202594223502934207286813)
        ·
          refine ⟨1200972833813600327732555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3202594223502934207286813 1200972833813600327732555)
          ·
            refine ⟨1801459250720400491598833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200972833813600327732555 1801459250720400491598833)
            ·
              refine ⟨1351094438040300368699125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1801459250720400491598833 1351094438040300368699125)
              ·
                refine ⟨126665103566278159565543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1351094438040300368699125 126665103566278159565543)
                ·
                  rfl

theorem cell21_1665086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_1665086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665086 prefixEnd_1665086 := by exact prefixLift 1665086
  have htrace : WordTrace (prefixWord ++ tailWord_1665086) baseStart_1665086 baseEnd_1665086 := by
    simpa [prefixWord, tailWord_1665086, baseEnd_1665086] using wordTrace_append hprefix tailTrace_1665086
  have hstable : (prefixWord ++ tailWord_1665086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665086).length < 2 ^ (prefixWord ++ tailWord_1665086).sum := by decide
  have hdescent : baseEnd_1665086 < baseStart_1665086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665117 : List Nat := [1, 4, 4, 1, 1, 2, 3, 2, 3]
def baseStart_1665117 : Nat := 118140960795 + 1665117 * 2 ^ 59
def prefixEnd_1665117 : Nat := 4983230072969 + 3 ^ 40 * 1665117 * 2
def baseEnd_1665117 : Nat := 380002385321185313679899

theorem tailTrace_1665117 : CollatzResearch.WordTrace tailWord_1665117 prefixEnd_1665117 380002385321185313679899 := by
  unfold tailWord_1665117
  simp only [CollatzResearch.WordTrace]
  refine ⟨60731806308572963188113605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40487870872381975458742403 60731806308572963188113605)
  ·
    refine ⟨11387213682857430597771301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60731806308572963188113605 11387213682857430597771301)
    ·
      refine ⟨2135102565535768237082119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11387213682857430597771301 2135102565535768237082119)
      ·
        refine ⟨3202653848303652355623179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2135102565535768237082119 3202653848303652355623179)
        ·
          refine ⟨4803980772455478533434769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3202653848303652355623179 4803980772455478533434769)
          ·
            refine ⟨3602985579341608900076077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4803980772455478533434769 3602985579341608900076077)
            ·
              refine ⟨1351119592253103337528529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3602985579341608900076077 1351119592253103337528529)
              ·
                refine ⟨1013339694189827503146397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1351119592253103337528529 1013339694189827503146397)
                ·
                  refine ⟨380002385321185313679899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013339694189827503146397 380002385321185313679899)
                  ·
                    rfl

theorem cell21_1665117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_1665117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665117 prefixEnd_1665117 := by exact prefixLift 1665117
  have htrace : WordTrace (prefixWord ++ tailWord_1665117) baseStart_1665117 baseEnd_1665117 := by
    simpa [prefixWord, tailWord_1665117, baseEnd_1665117] using wordTrace_append hprefix tailTrace_1665117
  have hstable : (prefixWord ++ tailWord_1665117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665117).length < 2 ^ (prefixWord ++ tailWord_1665117).sum := by decide
  have hdescent : baseEnd_1665117 < baseStart_1665117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665215 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 6]
def baseStart_1665215 : Nat := 118140960795 + 1665215 * 2 ^ 59
def prefixEnd_1665215 : Nat := 4983230072969 + 3 ^ 40 * 1665215 * 2
def baseEnd_1665215 : Nat := 380024750256358921046365

theorem tailTrace_1665215 : CollatzResearch.WordTrace tailWord_1665215 prefixEnd_1665215 380024750256358921046365 := by
  unfold tailWord_1665215
  simp only [CollatzResearch.WordTrace]
  refine ⟨60735380662217925925181099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40490253774811950616787399 60735380662217925925181099)
  ·
    refine ⟨91103070993326888887771649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60735380662217925925181099 91103070993326888887771649)
    ·
      refine ⟨68327303244995166665828737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91103070993326888887771649 68327303244995166665828737)
      ·
        refine ⟨51245477433746374999371553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68327303244995166665828737 51245477433746374999371553)
        ·
          refine ⟨38434108075309781249528665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51245477433746374999371553 38434108075309781249528665)
          ·
            refine ⟨28825581056482335937146499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38434108075309781249528665 28825581056482335937146499)
            ·
              refine ⟨43238371584723503905719749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28825581056482335937146499 43238371584723503905719749)
              ·
                refine ⟨8107194672135656982322453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43238371584723503905719749 8107194672135656982322453)
                ·
                  refine ⟨380024750256358921046365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8107194672135656982322453 380024750256358921046365)
                  ·
                    rfl

theorem cell21_1665215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 6].length) (baseStart_1665215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665215 prefixEnd_1665215 := by exact prefixLift 1665215
  have htrace : WordTrace (prefixWord ++ tailWord_1665215) baseStart_1665215 baseEnd_1665215 := by
    simpa [prefixWord, tailWord_1665215, baseEnd_1665215] using wordTrace_append hprefix tailTrace_1665215
  have hstable : (prefixWord ++ tailWord_1665215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665215).length < 2 ^ (prefixWord ++ tailWord_1665215).sum := by decide
  have hdescent : baseEnd_1665215 < baseStart_1665215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665249 : List Nat := [1, 2, 3, 1, 3, 1, 5, 1, 4]
def baseStart_1665249 : Nat := 118140960795 + 1665249 * 2 ^ 59
def prefixEnd_1665249 : Nat := 4983230072969 + 3 ^ 40 * 1665249 * 2
def baseEnd_1665249 : Nat := 380032509519582417479629

theorem tailTrace_1665249 : CollatzResearch.WordTrace tailWord_1665249 prefixEnd_1665249 380032509519582417479629 := by
  unfold tailWord_1665249
  simp only [CollatzResearch.WordTrace]
  refine ⟨60736620744094749731918801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40491080496063166487945867 60736620744094749731918801)
  ·
    refine ⟨45552465558071062298939101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60736620744094749731918801 45552465558071062298939101)
    ·
      refine ⟨17082174584276648362102163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45552465558071062298939101 17082174584276648362102163)
      ·
        refine ⟨25623261876414972543153245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17082174584276648362102163 25623261876414972543153245)
        ·
          refine ⟨9608723203655614703682467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25623261876414972543153245 9608723203655614703682467)
          ·
            refine ⟨14413084805483422055523701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9608723203655614703682467 14413084805483422055523701)
            ·
              refine ⟨1351226700514070817705347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14413084805483422055523701 1351226700514070817705347)
              ·
                refine ⟨2026840050771106226558021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1351226700514070817705347 2026840050771106226558021)
                ·
                  refine ⟨380032509519582417479629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2026840050771106226558021 380032509519582417479629)
                  ·
                    rfl

theorem cell21_1665249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 4].length) (baseStart_1665249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665249 prefixEnd_1665249 := by exact prefixLift 1665249
  have htrace : WordTrace (prefixWord ++ tailWord_1665249) baseStart_1665249 baseEnd_1665249 := by
    simpa [prefixWord, tailWord_1665249, baseEnd_1665249] using wordTrace_append hprefix tailTrace_1665249
  have hstable : (prefixWord ++ tailWord_1665249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665249).length < 2 ^ (prefixWord ++ tailWord_1665249).sum := by decide
  have hdescent : baseEnd_1665249 < baseStart_1665249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665263 : List Nat := [1, 1, 2, 1, 6, 1, 4, 5]
def baseStart_1665263 : Nat := 118140960795 + 1665263 * 2 ^ 59
def prefixEnd_1665263 : Nat := 4983230072969 + 3 ^ 40 * 1665263 * 2
def baseEnd_1665263 : Nat := 126678568170107168082089

theorem tailTrace_1665263 : CollatzResearch.WordTrace tailWord_1665263 prefixEnd_1665263 126678568170107168082089 := by
  unfold tailWord_1665263
  simp only [CollatzResearch.WordTrace]
  refine ⟨60737131366044030122928443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40491420910696020081952295 60737131366044030122928443)
  ·
    refine ⟨91105697049066045184392665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60737131366044030122928443 91105697049066045184392665)
    ·
      refine ⟨68329272786799533888294499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91105697049066045184392665 68329272786799533888294499)
      ·
        refine ⟨102493909180199300832441749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68329272786799533888294499 102493909180199300832441749)
        ·
          refine ⟨4804401992821842226520707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102493909180199300832441749 4804401992821842226520707)
          ·
            refine ⟨7206602989232763339781061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4804401992821842226520707 7206602989232763339781061)
            ·
              refine ⟨1351238060481143126208949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7206602989232763339781061 1351238060481143126208949)
              ·
                refine ⟨126678568170107168082089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1351238060481143126208949 126678568170107168082089)
                ·
                  rfl

theorem cell21_1665263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 5].length) (baseStart_1665263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665263 prefixEnd_1665263 := by exact prefixLift 1665263
  have htrace : WordTrace (prefixWord ++ tailWord_1665263) baseStart_1665263 baseEnd_1665263 := by
    simpa [prefixWord, tailWord_1665263, baseEnd_1665263] using wordTrace_append hprefix tailTrace_1665263
  have hstable : (prefixWord ++ tailWord_1665263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665263).length < 2 ^ (prefixWord ++ tailWord_1665263).sum := by decide
  have hdescent : baseEnd_1665263 < baseStart_1665263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665291 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 6]
def baseStart_1665291 : Nat := 118140960795 + 1665291 * 2 ^ 59
def prefixEnd_1665291 : Nat := 4983230072969 + 3 ^ 40 * 1665291 * 2
def baseEnd_1665291 : Nat := 380042094491799677779543

theorem tailTrace_1665291 : CollatzResearch.WordTrace tailWord_1665291 prefixEnd_1665291 380042094491799677779543 := by
  unfold tailWord_1665291
  simp only [CollatzResearch.WordTrace]
  refine ⟨60738152609942590904947727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40492101739961727269965151 60738152609942590904947727)
  ·
    refine ⟨91107228914913886357421591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60738152609942590904947727 91107228914913886357421591)
    ·
      refine ⟨136660843372370829536132387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91107228914913886357421591 136660843372370829536132387)
      ·
        refine ⟨204991265058556244304198581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136660843372370829536132387 204991265058556244304198581)
        ·
          refine ⟨19217931099239647903518617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204991265058556244304198581 19217931099239647903518617)
          ·
            refine ⟨14413448324429735927638963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19217931099239647903518617 14413448324429735927638963)
            ·
              refine ⟨21620172486644603891458445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14413448324429735927638963 21620172486644603891458445)
              ·
                refine ⟨8107564682491726459296917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21620172486644603891458445 8107564682491726459296917)
                ·
                  refine ⟨380042094491799677779543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8107564682491726459296917 380042094491799677779543)
                  ·
                    rfl

theorem cell21_1665291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 6].length) (baseStart_1665291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665291 prefixEnd_1665291 := by exact prefixLift 1665291
  have htrace : WordTrace (prefixWord ++ tailWord_1665291) baseStart_1665291 baseEnd_1665291 := by
    simpa [prefixWord, tailWord_1665291, baseEnd_1665291] using wordTrace_append hprefix tailTrace_1665291
  have hstable : (prefixWord ++ tailWord_1665291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665291).length < 2 ^ (prefixWord ++ tailWord_1665291).sum := by decide
  have hdescent : baseEnd_1665291 < baseStart_1665291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665345 : List Nat := [1, 2, 5, 2, 2, 2, 2, 2, 3]
def baseStart_1665345 : Nat := 118140960795 + 1665345 * 2 ^ 59
def prefixEnd_1665345 : Nat := 4983230072969 + 3 ^ 40 * 1665345 * 2
def baseEnd_1665345 : Nat := 380054418027507583879433

theorem tailTrace_1665345 : CollatzResearch.WordTrace tailWord_1665345 prefixEnd_1665345 380054418027507583879433 := by
  unfold tailWord_1665345
  simp only [CollatzResearch.WordTrace]
  refine ⟨60740122151746958127413489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40493414767831305418275659 60740122151746958127413489)
  ·
    refine ⟨45555091613810218595560117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60740122151746958127413489 45555091613810218595560117)
    ·
      refine ⟨4270789838794707993333761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45555091613810218595560117 4270789838794707993333761)
      ·
        refine ⟨3203092379096030995000321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4270789838794707993333761 3203092379096030995000321)
        ·
          refine ⟨2402319284322023246250241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3203092379096030995000321 2402319284322023246250241)
          ·
            refine ⟨1801739463241517434687681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2402319284322023246250241 1801739463241517434687681)
            ·
              refine ⟨1351304597431138076015761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1801739463241517434687681 1351304597431138076015761)
              ·
                refine ⟨1013478448073353557011821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1351304597431138076015761 1013478448073353557011821)
                ·
                  refine ⟨380054418027507583879433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013478448073353557011821 380054418027507583879433)
                  ·
                    rfl

theorem cell21_1665345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 3].length) (baseStart_1665345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665345 prefixEnd_1665345 := by exact prefixLift 1665345
  have htrace : WordTrace (prefixWord ++ tailWord_1665345) baseStart_1665345 baseEnd_1665345 := by
    simpa [prefixWord, tailWord_1665345, baseEnd_1665345] using wordTrace_append hprefix tailTrace_1665345
  have hstable : (prefixWord ++ tailWord_1665345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665345).length < 2 ^ (prefixWord ++ tailWord_1665345).sum := by decide
  have hdescent : baseEnd_1665345 < baseStart_1665345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665432 : List Nat := [2, 1, 2, 5, 1, 3, 2, 5]
def baseStart_1665432 : Nat := 118140960795 + 1665432 * 2 ^ 59
def prefixEnd_1665432 : Nat := 4983230072969 + 3 ^ 40 * 1665432 * 2
def baseEnd_1665432 : Nat := 126691424204271588643085

theorem tailTrace_1665432 : CollatzResearch.WordTrace tailWord_1665432 prefixEnd_1665432 126691424204271588643085 := by
  unfold tailWord_1665432
  simp only [CollatzResearch.WordTrace]
  refine ⟨30371647651215885992915275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40495530201621181323887033 30371647651215885992915275)
  ·
    refine ⟨45557471476823828989372913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30371647651215885992915275 45557471476823828989372913)
    ·
      refine ⟨34168103607617871742029685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45557471476823828989372913 34168103607617871742029685)
      ·
        refine ⟨3203259713214175475815283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34168103607617871742029685 3203259713214175475815283)
        ·
          refine ⟨4804889569821263213722925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3203259713214175475815283 4804889569821263213722925)
          ·
            refine ⟨1801833588682973705146097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4804889569821263213722925 1801833588682973705146097)
            ·
              refine ⟨1351375191512230278859573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1801833588682973705146097 1351375191512230278859573)
              ·
                refine ⟨126691424204271588643085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1351375191512230278859573 126691424204271588643085)
                ·
                  rfl

theorem cell21_1665432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 5].length) (baseStart_1665432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665432 prefixEnd_1665432 := by exact prefixLift 1665432
  have htrace : WordTrace (prefixWord ++ tailWord_1665432) baseStart_1665432 baseEnd_1665432 := by
    simpa [prefixWord, tailWord_1665432, baseEnd_1665432] using wordTrace_append hprefix tailTrace_1665432
  have hstable : (prefixWord ++ tailWord_1665432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665432).length < 2 ^ (prefixWord ++ tailWord_1665432).sum := by decide
  have hdescent : baseEnd_1665432 < baseStart_1665432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665443 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 6]
def baseStart_1665443 : Nat := 118140960795 + 1665443 * 2 ^ 59
def prefixEnd_1665443 : Nat := 4983230072969 + 3 ^ 40 * 1665443 * 2
def baseEnd_1665443 : Nat := 380076782962681191245899

theorem tailTrace_1665443 : CollatzResearch.WordTrace tailWord_1665443 prefixEnd_1665443 380076782962681191245899 := by
  unfold tailWord_1665443
  simp only [CollatzResearch.WordTrace]
  refine ⟨60743696505391920864480983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40495797670261280576320655 60743696505391920864480983)
  ·
    refine ⟨91115544758087881296721475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60743696505391920864480983 91115544758087881296721475)
    ·
      refine ⟨136673317137131821945082213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91115544758087881296721475 136673317137131821945082213)
      ·
        refine ⟨25626246963212216614702915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136673317137131821945082213 25626246963212216614702915)
        ·
          refine ⟨38439370444818324922054373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25626246963212216614702915 38439370444818324922054373)
          ·
            refine ⟨7207381958403435922885195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38439370444818324922054373 7207381958403435922885195)
            ·
              refine ⟨10811072937605153884327793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7207381958403435922885195 10811072937605153884327793)
              ·
                refine ⟨8108304703203865413245845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10811072937605153884327793 8108304703203865413245845)
                ·
                  refine ⟨380076782962681191245899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8108304703203865413245845 380076782962681191245899)
                  ·
                    rfl

theorem cell21_1665443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 6].length) (baseStart_1665443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665443 prefixEnd_1665443 := by exact prefixLift 1665443
  have htrace : WordTrace (prefixWord ++ tailWord_1665443) baseStart_1665443 baseEnd_1665443 := by
    simpa [prefixWord, tailWord_1665443, baseEnd_1665443] using wordTrace_append hprefix tailTrace_1665443
  have hstable : (prefixWord ++ tailWord_1665443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665443).length < 2 ^ (prefixWord ++ tailWord_1665443).sum := by decide
  have hdescent : baseEnd_1665443 < baseStart_1665443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665463 : List Nat := [1, 1, 3, 1, 3, 4, 3, 2, 3]
def baseStart_1665463 : Nat := 118140960795 + 1665463 * 2 ^ 59
def prefixEnd_1665463 : Nat := 4983230072969 + 3 ^ 40 * 1665463 * 2
def baseEnd_1665463 : Nat := 380081347235165600912525

theorem tailTrace_1665463 : CollatzResearch.WordTrace tailWord_1665463 prefixEnd_1665463 380081347235165600912525 := by
  unfold tailWord_1665463
  simp only [CollatzResearch.WordTrace]
  refine ⟨60744425965319464280209043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40496283976879642853472695 60744425965319464280209043)
  ·
    refine ⟨91116638947979196420313565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60744425965319464280209043 91116638947979196420313565)
    ·
      refine ⟨34168739605492198657617587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91116638947979196420313565 34168739605492198657617587)
      ·
        refine ⟨51253109408238297986426381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34168739605492198657617587 51253109408238297986426381)
        ·
          refine ⟨19219916028089361744909893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51253109408238297986426381 19219916028089361744909893)
          ·
            refine ⟨3603734255266755327170605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19219916028089361744909893 3603734255266755327170605)
            ·
              refine ⟨1351400345725033247688977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3603734255266755327170605 1351400345725033247688977)
              ·
                refine ⟨1013550259293774935766733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1351400345725033247688977 1013550259293774935766733)
                ·
                  refine ⟨380081347235165600912525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013550259293774935766733 380081347235165600912525)
                  ·
                    rfl

theorem cell21_1665463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 3].length) (baseStart_1665463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665463 prefixEnd_1665463 := by exact prefixLift 1665463
  have htrace : WordTrace (prefixWord ++ tailWord_1665463) baseStart_1665463 baseEnd_1665463 := by
    simpa [prefixWord, tailWord_1665463, baseEnd_1665463] using wordTrace_append hprefix tailTrace_1665463
  have hstable : (prefixWord ++ tailWord_1665463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665463).length < 2 ^ (prefixWord ++ tailWord_1665463).sum := by decide
  have hdescent : baseEnd_1665463 < baseStart_1665463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665525 : List Nat := [1, 3, 5, 1, 3, 1, 1, 6]
def baseStart_1665525 : Nat := 118140960795 + 1665525 * 2 ^ 59
def prefixEnd_1665525 : Nat := 4983230072969 + 3 ^ 40 * 1665525 * 2
def baseEnd_1665525 : Nat := 126698498826622423626355

theorem tailTrace_1665525 : CollatzResearch.WordTrace tailWord_1665525 prefixEnd_1665525 126698498826622423626355 := by
  unfold tailWord_1665525
  simp only [CollatzResearch.WordTrace]
  refine ⟨60746687291094848868966029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40497791527396565912644019 60746687291094848868966029)
  ·
    refine ⟨22780007734160568325862261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60746687291094848868966029 22780007734160568325862261)
    ·
      refine ⟨2135625725077553280549587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22780007734160568325862261 2135625725077553280549587)
      ·
        refine ⟨3203438587616329920824381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2135625725077553280549587 3203438587616329920824381)
        ·
          refine ⟨1201289470356123720309143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3203438587616329920824381 1201289470356123720309143)
          ·
            refine ⟨1801934205534185580463715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201289470356123720309143 1801934205534185580463715)
            ·
              refine ⟨2702901308301278370695573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1801934205534185580463715 2702901308301278370695573)
              ·
                refine ⟨126698498826622423626355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2702901308301278370695573 126698498826622423626355)
                ·
                  rfl

theorem cell21_1665525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 6].length) (baseStart_1665525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665525 prefixEnd_1665525 := by exact prefixLift 1665525
  have htrace : WordTrace (prefixWord ++ tailWord_1665525) baseStart_1665525 baseEnd_1665525 := by
    simpa [prefixWord, tailWord_1665525, baseEnd_1665525] using wordTrace_append hprefix tailTrace_1665525
  have hstable : (prefixWord ++ tailWord_1665525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665525).length < 2 ^ (prefixWord ++ tailWord_1665525).sum := by decide
  have hdescent : baseEnd_1665525 < baseStart_1665525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665542 : List Nat := [6, 2, 1, 1, 1, 2, 3, 5]
def baseStart_1665542 : Nat := 118140960795 + 1665542 * 2 ^ 59
def prefixEnd_1665542 : Nat := 4983230072969 + 3 ^ 40 * 1665542 * 2
def baseEnd_1665542 : Nat := 126699792037159673031899

theorem tailTrace_1665542 : CollatzResearch.WordTrace tailWord_1665542 prefixEnd_1665542 126699792037159673031899 := by
  unfold tailWord_1665542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1898353354126039399135465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40498204888022173848223253 1898353354126039399135465)
  ·
    refine ⟨1423765015594529549351599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1898353354126039399135465 1423765015594529549351599)
    ·
      refine ⟨2135647523391794324027399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1423765015594529549351599 2135647523391794324027399)
      ·
        refine ⟨3203471285087691486041099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2135647523391794324027399 3203471285087691486041099)
        ·
          refine ⟨4805206927631537229061649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3203471285087691486041099 4805206927631537229061649)
          ·
            refine ⟨3603905195723652921796237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4805206927631537229061649 3603905195723652921796237)
            ·
              refine ⟨1351464448396369845673589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3603905195723652921796237 1351464448396369845673589)
              ·
                refine ⟨126699792037159673031899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1351464448396369845673589 126699792037159673031899)
                ·
                  rfl

theorem cell21_1665542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_1665542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665542 prefixEnd_1665542 := by exact prefixLift 1665542
  have htrace : WordTrace (prefixWord ++ tailWord_1665542) baseStart_1665542 baseEnd_1665542 := by
    simpa [prefixWord, tailWord_1665542, baseEnd_1665542] using wordTrace_append hprefix tailTrace_1665542
  have hstable : (prefixWord ++ tailWord_1665542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665542).length < 2 ^ (prefixWord ++ tailWord_1665542).sum := by decide
  have hdescent : baseEnd_1665542 < baseStart_1665542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665556 : List Nat := [2, 4, 3, 1, 1, 2, 2, 3, 3]
def baseStart_1665556 : Nat := 118140960795 + 1665556 * 2 ^ 59
def prefixEnd_1665556 : Nat := 4983230072969 + 3 ^ 40 * 1665556 * 2
def baseEnd_1665556 : Nat := 380102571102218105862335

theorem tailTrace_1665556 : CollatzResearch.WordTrace tailWord_1665556 prefixEnd_1665556 380102571102218105862335 := by
  unfold tailWord_1665556
  simp only [CollatzResearch.WordTrace]
  refine ⟨30373908976991270581672261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40498545302655027442229681 30373908976991270581672261)
  ·
    refine ⟨5695107933185863234063549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30373908976991270581672261 5695107933185863234063549)
    ·
      refine ⟨2135665474944698712773831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5695107933185863234063549 2135665474944698712773831)
      ·
        refine ⟨3203498212417048069160747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2135665474944698712773831 3203498212417048069160747)
        ·
          refine ⟨4805247318625572103741121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3203498212417048069160747 4805247318625572103741121)
          ·
            refine ⟨3603935488969179077805841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4805247318625572103741121 3603935488969179077805841)
            ·
              refine ⟨2702951616726884308354381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3603935488969179077805841 2702951616726884308354381)
              ·
                refine ⟨1013606856272581615632893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2702951616726884308354381 1013606856272581615632893)
                ·
                  refine ⟨380102571102218105862335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013606856272581615632893 380102571102218105862335)
                  ·
                    rfl

theorem cell21_1665556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_1665556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665556 prefixEnd_1665556 := by exact prefixLift 1665556
  have htrace : WordTrace (prefixWord ++ tailWord_1665556) baseStart_1665556 baseEnd_1665556 := by
    simpa [prefixWord, tailWord_1665556, baseEnd_1665556] using wordTrace_append hprefix tailTrace_1665556
  have hstable : (prefixWord ++ tailWord_1665556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665556).length < 2 ^ (prefixWord ++ tailWord_1665556).sum := by decide
  have hdescent : baseEnd_1665556 < baseStart_1665556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665646 : List Nat := [4, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_1665646 : Nat := 118140960795 + 1665646 * 2 ^ 59
def prefixEnd_1665646 : Nat := 4983230072969 + 3 ^ 40 * 1665646 * 2
def baseEnd_1665646 : Nat := 380123110328397949362151

theorem tailTrace_1665646 : CollatzResearch.WordTrace tailWord_1665646 prefixEnd_1665646 380123110328397949362151 := by
  unfold tailWord_1665646
  simp only [CollatzResearch.WordTrace]
  refine ⟨7593887565457060816765099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40500733682437657689413861 7593887565457060816765099)
  ·
    refine ⟨11390831348185591225147649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7593887565457060816765099 11390831348185591225147649)
    ·
      refine ⟨8543123511139193418860737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11390831348185591225147649 8543123511139193418860737)
      ·
        refine ⟨6407342633354395064145553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8543123511139193418860737 6407342633354395064145553)
        ·
          refine ⟨4805506975015796298109165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6407342633354395064145553 4805506975015796298109165)
          ·
            refine ⟨1802065115630923611790937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4805506975015796298109165 1802065115630923611790937)
            ·
              refine ⟨1351548836723192708843203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1802065115630923611790937 1351548836723192708843203)
              ·
                refine ⟨2027323255084789063264805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1351548836723192708843203 2027323255084789063264805)
                ·
                  refine ⟨380123110328397949362151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2027323255084789063264805 380123110328397949362151)
                  ·
                    rfl

theorem cell21_1665646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_1665646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665646 prefixEnd_1665646 := by exact prefixLift 1665646
  have htrace : WordTrace (prefixWord ++ tailWord_1665646) baseStart_1665646 baseEnd_1665646 := by
    simpa [prefixWord, tailWord_1665646, baseEnd_1665646] using wordTrace_append hprefix tailTrace_1665646
  have hstable : (prefixWord ++ tailWord_1665646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665646).length < 2 ^ (prefixWord ++ tailWord_1665646).sum := by decide
  have hdescent : baseEnd_1665646 < baseStart_1665646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665688 : List Nat := [2, 1, 2, 4, 1, 1, 4, 2, 4]
def baseStart_1665688 : Nat := 118140960795 + 1665688 * 2 ^ 59
def prefixEnd_1665688 : Nat := 4983230072969 + 3 ^ 40 * 1665688 * 2
def baseEnd_1665688 : Nat := 380132695300615209662065

theorem tailTrace_1665688 : CollatzResearch.WordTrace tailWord_1665688 prefixEnd_1665688 380132695300615209662065 := by
  unfold tailWord_1665688
  simp only [CollatzResearch.WordTrace]
  refine ⟨30376316194752163853574859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40501754926336218471433145 30376316194752163853574859)
  ·
    refine ⟨45564474292128245780362289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30376316194752163853574859 45564474292128245780362289)
    ·
      refine ⟨34173355719096184335271717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45564474292128245780362289 34173355719096184335271717)
      ·
        refine ⟨6407504197330534562863447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34173355719096184335271717 6407504197330534562863447)
        ·
          refine ⟨9611256295995801844295171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6407504197330534562863447 9611256295995801844295171)
          ·
            refine ⟨14416884443993702766442757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9611256295995801844295171 14416884443993702766442757)
            ·
              refine ⟨2703165833248819268708017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14416884443993702766442757 2703165833248819268708017)
              ·
                refine ⟨2027374374936614451531013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2703165833248819268708017 2027374374936614451531013)
                ·
                  refine ⟨380132695300615209662065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2027374374936614451531013 380132695300615209662065)
                  ·
                    rfl

theorem cell21_1665688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_1665688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665688 prefixEnd_1665688 := by exact prefixLift 1665688
  have htrace : WordTrace (prefixWord ++ tailWord_1665688) baseStart_1665688 baseEnd_1665688 := by
    simpa [prefixWord, tailWord_1665688, baseEnd_1665688] using wordTrace_append hprefix tailTrace_1665688
  have hstable : (prefixWord ++ tailWord_1665688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665688).length < 2 ^ (prefixWord ++ tailWord_1665688).sum := by decide
  have hdescent : baseEnd_1665688 < baseStart_1665688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665719 : List Nat := [1, 1, 3, 1, 6, 1, 3, 5]
def baseStart_1665719 : Nat := 118140960795 + 1665719 * 2 ^ 59
def prefixEnd_1665719 : Nat := 4983230072969 + 3 ^ 40 * 1665719 * 2
def baseEnd_1665719 : Nat := 126713256640988681548445

theorem tailTrace_1665719 : CollatzResearch.WordTrace tailWord_1665719 prefixEnd_1665719 126713256640988681548445 := by
  unfold tailWord_1665719
  simp only [CollatzResearch.WordTrace]
  refine ⟨60753763052392020001528211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40502508701594680001018807 60753763052392020001528211)
  ·
    refine ⟨91130644578588030002292317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60753763052392020001528211 91130644578588030002292317)
    ·
      refine ⟨34173991716970511250859619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91130644578588030002292317 34173991716970511250859619)
      ·
        refine ⟨51260987575455766876289429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34173991716970511250859619 51260987575455766876289429)
        ·
          refine ⟨2402858792599489072326067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51260987575455766876289429 2402858792599489072326067)
          ·
            refine ⟨3604288188899233608489101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2402858792599489072326067 3604288188899233608489101)
            ·
              refine ⟨1351608070837212603183413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3604288188899233608489101 1351608070837212603183413)
              ·
                refine ⟨126713256640988681548445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1351608070837212603183413 126713256640988681548445)
                ·
                  rfl

theorem cell21_1665719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 5].length) (baseStart_1665719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665719 prefixEnd_1665719 := by exact prefixLift 1665719
  have htrace : WordTrace (prefixWord ++ tailWord_1665719) baseStart_1665719 baseEnd_1665719 := by
    simpa [prefixWord, tailWord_1665719, baseEnd_1665719] using wordTrace_append hprefix tailTrace_1665719
  have hstable : (prefixWord ++ tailWord_1665719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665719).length < 2 ^ (prefixWord ++ tailWord_1665719).sum := by decide
  have hdescent : baseEnd_1665719 < baseStart_1665719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665778 : List Nat := [3, 2, 1, 3, 1, 3, 1, 7]
def baseStart_1665778 : Nat := 118140960795 + 1665778 * 2 ^ 59
def prefixEnd_1665778 : Nat := 4983230072969 + 3 ^ 40 * 1665778 * 2
def baseEnd_1665778 : Nat := 126717744842265017720627

theorem tailTrace_1665778 : CollatzResearch.WordTrace tailWord_1665778 prefixEnd_1665778 126717744842265017720627 := by
  unfold tailWord_1665778
  simp only [CollatzResearch.WordTrace]
  refine ⟨15188978739794568269481497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40503943306118848718617325 15188978739794568269481497)
  ·
    refine ⟨11391734054845926202111123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15188978739794568269481497 11391734054845926202111123)
    ·
      refine ⟨17087601082268889303166685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11391734054845926202111123 17087601082268889303166685)
      ·
        refine ⟨6407850405850833488687507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17087601082268889303166685 6407850405850833488687507)
        ·
          refine ⟨9611775608776250233031261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6407850405850833488687507 9611775608776250233031261)
          ·
            refine ⟨3604415853291093837386723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9611775608776250233031261 3604415853291093837386723)
            ·
              refine ⟨5406623779936640756080085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604415853291093837386723 5406623779936640756080085)
              ·
                refine ⟨126717744842265017720627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5406623779936640756080085 126717744842265017720627)
                ·
                  rfl

theorem cell21_1665778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_1665778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665778 prefixEnd_1665778 := by exact prefixLift 1665778
  have htrace : WordTrace (prefixWord ++ tailWord_1665778) baseStart_1665778 baseEnd_1665778 := by
    simpa [prefixWord, tailWord_1665778, baseEnd_1665778] using wordTrace_append hprefix tailTrace_1665778
  have hstable : (prefixWord ++ tailWord_1665778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665778).length < 2 ^ (prefixWord ++ tailWord_1665778).sum := by decide
  have hdescent : baseEnd_1665778 < baseStart_1665778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665809 : List Nat := [1, 2, 2, 1, 1, 3, 2, 6, 3]
def baseStart_1665809 : Nat := 118140960795 + 1665809 * 2 ^ 59
def prefixEnd_1665809 : Nat := 4983230072969 + 3 ^ 40 * 1665809 * 2
def baseEnd_1665809 : Nat := 380160309149145888145151

theorem tailTrace_1665809 : CollatzResearch.WordTrace tailWord_1665809 prefixEnd_1665809 380160309149145888145151 := by
  unfold tailWord_1665809
  simp only [CollatzResearch.WordTrace]
  refine ⟨60757045622065965372304481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40504697081377310248202987 60757045622065965372304481)
  ·
    refine ⟨45567784216549474029228361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60757045622065965372304481 45567784216549474029228361)
    ·
      refine ⟨34175838162412105521921271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45567784216549474029228361 34175838162412105521921271)
      ·
        refine ⟨51263757243618158282881907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34175838162412105521921271 51263757243618158282881907)
        ·
          refine ⟨76895635865427237424322861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51263757243618158282881907 76895635865427237424322861)
          ·
            refine ⟨28835863449535214034121073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76895635865427237424322861 28835863449535214034121073)
            ·
              refine ⟨21626897587151410525590805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28835863449535214034121073 21626897587151410525590805)
              ·
                refine ⟨1013760824397722368387069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21626897587151410525590805 1013760824397722368387069)
                ·
                  refine ⟨380160309149145888145151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013760824397722368387069 380160309149145888145151)
                  ·
                    rfl

theorem cell21_1665809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 3].length) (baseStart_1665809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665809 prefixEnd_1665809 := by exact prefixLift 1665809
  have htrace : WordTrace (prefixWord ++ tailWord_1665809) baseStart_1665809 baseEnd_1665809 := by
    simpa [prefixWord, tailWord_1665809, baseEnd_1665809] using wordTrace_append hprefix tailTrace_1665809
  have hstable : (prefixWord ++ tailWord_1665809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665809).length < 2 ^ (prefixWord ++ tailWord_1665809).sum := by decide
  have hdescent : baseEnd_1665809 < baseStart_1665809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665854 : List Nat := [4, 2, 1, 2, 3, 9]
def baseStart_1665854 : Nat := 118140960795 + 1665854 * 2 ^ 59
def prefixEnd_1665854 : Nat := 4983230072969 + 3 ^ 40 * 1665854 * 2
def baseEnd_1665854 : Nat := 14080391806008733699817

theorem tailTrace_1665854 : CollatzResearch.WordTrace tailWord_1665854 prefixEnd_1665854 14080391806008733699817 := by
  unfold tailWord_1665854
  simp only [CollatzResearch.WordTrace]
  refine ⟨7594835863362867257211577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40505791271268625371795077 7594835863362867257211577)
  ·
    refine ⟨5696126897522150442908683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7594835863362867257211577 5696126897522150442908683)
    ·
      refine ⟨8544190346283225664363025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5696126897522150442908683 8544190346283225664363025)
      ·
        refine ⟨6408142759712419248272269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8544190346283225664363025 6408142759712419248272269)
        ·
          refine ⟨2403053534892157218102101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6408142759712419248272269 2403053534892157218102101)
          ·
            refine ⟨14080391806008733699817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2403053534892157218102101 14080391806008733699817)
            ·
              rfl

theorem cell21_1665854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 9].length) (baseStart_1665854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665854 prefixEnd_1665854 := by exact prefixLift 1665854
  have htrace : WordTrace (prefixWord ++ tailWord_1665854) baseStart_1665854 baseEnd_1665854 := by
    simpa [prefixWord, tailWord_1665854, baseEnd_1665854] using wordTrace_append hprefix tailTrace_1665854
  have hstable : (prefixWord ++ tailWord_1665854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665854).length < 2 ^ (prefixWord ++ tailWord_1665854).sum := by decide
  have hdescent : baseEnd_1665854 < baseStart_1665854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665860 : List Nat := [2, 3, 4, 2, 1, 1, 1, 4, 3]
def baseStart_1665860 : Nat := 118140960795 + 1665860 * 2 ^ 59
def prefixEnd_1665860 : Nat := 4983230072969 + 3 ^ 40 * 1665860 * 2
def baseEnd_1665860 : Nat := 380171948043981132795047

theorem tailTrace_1665860 : CollatzResearch.WordTrace tailWord_1665860 prefixEnd_1665860 380171948043981132795047 := by
  unfold tailWord_1665860
  simp only [CollatzResearch.WordTrace]
  refine ⟨30379452872440600541205517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40505937163254134054940689 30379452872440600541205517)
  ·
    refine ⟨11392294827165225202952069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30379452872440600541205517 11392294827165225202952069)
    ·
      refine ⟨2136055280093479725553513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11392294827165225202952069 2136055280093479725553513)
      ·
        refine ⟨1602041460070109794165135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2136055280093479725553513 1602041460070109794165135)
        ·
          refine ⟨2403062190105164691247703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1602041460070109794165135 2403062190105164691247703)
          ·
            refine ⟨3604593285157747036871555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2403062190105164691247703 3604593285157747036871555)
            ·
              refine ⟨5406889927736620555307333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604593285157747036871555 5406889927736620555307333)
              ·
                refine ⟨1013791861450616354120125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5406889927736620555307333 1013791861450616354120125)
                ·
                  refine ⟨380171948043981132795047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013791861450616354120125 380171948043981132795047)
                  ·
                    rfl

theorem cell21_1665860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_1665860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665860 prefixEnd_1665860 := by exact prefixLift 1665860
  have htrace : WordTrace (prefixWord ++ tailWord_1665860) baseStart_1665860 baseEnd_1665860 := by
    simpa [prefixWord, tailWord_1665860, baseEnd_1665860] using wordTrace_append hprefix tailTrace_1665860
  have hstable : (prefixWord ++ tailWord_1665860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665860).length < 2 ^ (prefixWord ++ tailWord_1665860).sum := by decide
  have hdescent : baseEnd_1665860 < baseStart_1665860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665913 : List Nat := [1, 2, 1, 3, 2, 4, 8]
def baseStart_1665913 : Nat := 118140960795 + 1665913 * 2 ^ 59
def prefixEnd_1665913 : Nat := 4983230072969 + 3 ^ 40 * 1665913 * 2
def baseEnd_1665913 : Nat := 42242671485118313156845

theorem tailTrace_1665913 : CollatzResearch.WordTrace tailWord_1665913 prefixEnd_1665913 42242671485118313156845 := by
  unfold tailWord_1665913
  simp only [CollatzResearch.WordTrace]
  refine ⟨60760838813689191134090393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40507225875792794089393595 60760838813689191134090393)
  ·
    refine ⟨45570629110266893350567795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60760838813689191134090393 45570629110266893350567795)
    ·
      refine ⟨68355943665400340025851693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45570629110266893350567795 68355943665400340025851693)
      ·
        refine ⟨25633478874525127509694385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68355943665400340025851693 25633478874525127509694385)
        ·
          refine ⟨19225109155893845632270789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25633478874525127509694385 19225109155893845632270789)
          ·
            refine ⟨3604707966730096056050773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19225109155893845632270789 3604707966730096056050773)
            ·
              refine ⟨42242671485118313156845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3604707966730096056050773 42242671485118313156845)
              ·
                rfl

theorem cell21_1665913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 8].length) (baseStart_1665913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665913 prefixEnd_1665913 := by exact prefixLift 1665913
  have htrace : WordTrace (prefixWord ++ tailWord_1665913) baseStart_1665913 baseEnd_1665913 := by
    simpa [prefixWord, tailWord_1665913, baseEnd_1665913] using wordTrace_append hprefix tailTrace_1665913
  have hstable : (prefixWord ++ tailWord_1665913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665913).length < 2 ^ (prefixWord ++ tailWord_1665913).sum := by decide
  have hdescent : baseEnd_1665913 < baseStart_1665913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665978 : List Nat := [3, 1, 1, 1, 2, 1, 7, 2, 3]
def baseStart_1665978 : Nat := 118140960795 + 1665978 * 2 ^ 59
def prefixEnd_1665978 : Nat := 4983230072969 + 3 ^ 40 * 1665978 * 2
def baseEnd_1665978 : Nat := 380198877251639149828139

theorem tailTrace_1665978 : CollatzResearch.WordTrace tailWord_1665978 prefixEnd_1665978 380198877251639149828139 := by
  unfold tailWord_1665978
  simp only [CollatzResearch.WordTrace]
  refine ⟨15190802389613426808801647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40508806372302471490137725 15190802389613426808801647)
  ·
    refine ⟨22786203584420140213202471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15190802389613426808801647 22786203584420140213202471)
    ·
      refine ⟨34179305376630210319803707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22786203584420140213202471 34179305376630210319803707)
      ·
        refine ⟨51268958064945315479705561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34179305376630210319803707 51268958064945315479705561)
        ·
          refine ⟨38451718548708986609779171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51268958064945315479705561 38451718548708986609779171)
          ·
            refine ⟨57677577823063479914668757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38451718548708986609779171 57677577823063479914668757)
            ·
              refine ⟨1351818230228050310500049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 57677577823063479914668757 1351818230228050310500049)
              ·
                refine ⟨1013863672671037732875037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1351818230228050310500049 1013863672671037732875037)
                ·
                  refine ⟨380198877251639149828139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013863672671037732875037 380198877251639149828139)
                  ·
                    rfl

theorem cell21_1665978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_1665978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665978 prefixEnd_1665978 := by exact prefixLift 1665978
  have htrace : WordTrace (prefixWord ++ tailWord_1665978) baseStart_1665978 baseEnd_1665978 := by
    simpa [prefixWord, tailWord_1665978, baseEnd_1665978] using wordTrace_append hprefix tailTrace_1665978
  have hstable : (prefixWord ++ tailWord_1665978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665978).length < 2 ^ (prefixWord ++ tailWord_1665978).sum := by decide
  have hdescent : baseEnd_1665978 < baseStart_1665978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665992 : List Nat := [2, 1, 3, 1, 5, 1, 1, 3, 4]
def baseStart_1665992 : Nat := 118140960795 + 1665992 * 2 ^ 59
def prefixEnd_1665992 : Nat := 4983230072969 + 3 ^ 40 * 1665992 * 2
def baseEnd_1665992 : Nat := 380202072242378236594777

theorem tailTrace_1665992 : CollatzResearch.WordTrace tailWord_1665992 prefixEnd_1665992 380202072242378236594777 := by
  unfold tailWord_1665992
  simp only [CollatzResearch.WordTrace]
  refine ⟨30381860090201493813108115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40509146786935325084144153 30381860090201493813108115)
  ·
    refine ⟨45572790135302240719662173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30381860090201493813108115 45572790135302240719662173)
    ·
      refine ⟨17089796300738340269873315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45572790135302240719662173 17089796300738340269873315)
      ·
        refine ⟨25634694451107510404809973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17089796300738340269873315 25634694451107510404809973)
        ·
          refine ⟨2403252604791329100450935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25634694451107510404809973 2403252604791329100450935)
          ·
            refine ⟨3604878907186993650676403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2403252604791329100450935 3604878907186993650676403)
            ·
              refine ⟨5407318360780490476014605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604878907186993650676403 5407318360780490476014605)
              ·
                refine ⟨2027744385292683928505477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5407318360780490476014605 2027744385292683928505477)
                ·
                  refine ⟨380202072242378236594777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2027744385292683928505477 380202072242378236594777)
                  ·
                    rfl

theorem cell21_1665992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_1665992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1665992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1665992 prefixEnd_1665992 := by exact prefixLift 1665992
  have htrace : WordTrace (prefixWord ++ tailWord_1665992) baseStart_1665992 baseEnd_1665992 := by
    simpa [prefixWord, tailWord_1665992, baseEnd_1665992] using wordTrace_append hprefix tailTrace_1665992
  have hstable : (prefixWord ++ tailWord_1665992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665992).length < 2 ^ (prefixWord ++ tailWord_1665992).sum := by decide
  have hdescent : baseEnd_1665992 < baseStart_1665992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666096 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 5]
def baseStart_1666096 : Nat := 118140960795 + 1666096 * 2 ^ 59
def prefixEnd_1666096 : Nat := 4983230072969 + 3 ^ 40 * 1666096 * 2
def baseEnd_1666096 : Nat := 380225806459297166861231

theorem tailTrace_1666096 : CollatzResearch.WordTrace tailWord_1666096 prefixEnd_1666096 380225806459297166861231 := by
  unfold tailWord_1666096
  simp only [CollatzResearch.WordTrace]
  refine ⟨30383756686013106694001071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40511675581350808925334761 30383756686013106694001071)
  ·
    refine ⟨45575635029019660041001607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30383756686013106694001071 45575635029019660041001607)
    ·
      refine ⟨68363452543529490061502411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45575635029019660041001607 68363452543529490061502411)
      ·
        refine ⟨102545178815294235092253617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68363452543529490061502411 102545178815294235092253617)
        ·
          refine ⟨76908884111470676319190213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102545178815294235092253617 76908884111470676319190213)
          ·
            refine ⟨14420415770900751809848165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76908884111470676319190213 14420415770900751809848165)
            ·
              refine ⟨2703827957043890964346531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14420415770900751809848165 2703827957043890964346531)
              ·
                refine ⟨4055741935565836446519797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2703827957043890964346531 4055741935565836446519797)
                ·
                  refine ⟨380225806459297166861231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4055741935565836446519797 380225806459297166861231)
                  ·
                    rfl

theorem cell21_1666096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_1666096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666096 prefixEnd_1666096 := by exact prefixLift 1666096
  have htrace : WordTrace (prefixWord ++ tailWord_1666096) baseStart_1666096 baseEnd_1666096 := by
    simpa [prefixWord, tailWord_1666096, baseEnd_1666096] using wordTrace_append hprefix tailTrace_1666096
  have hstable : (prefixWord ++ tailWord_1666096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666096).length < 2 ^ (prefixWord ++ tailWord_1666096).sum := by decide
  have hdescent : baseEnd_1666096 < baseStart_1666096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666130 : List Nat := [3, 2, 2, 1, 3, 1, 3, 3, 3]
def baseStart_1666130 : Nat := 118140960795 + 1666130 * 2 ^ 59
def prefixEnd_1666130 : Nat := 4983230072969 + 3 ^ 40 * 1666130 * 2
def baseEnd_1666130 : Nat := 380233565722520663294495

theorem tailTrace_1666130 : CollatzResearch.WordTrace tailWord_1666130 prefixEnd_1666130 380233565722520663294495 := by
  unfold tailWord_1666130
  simp only [CollatzResearch.WordTrace]
  refine ⟨15192188363475759298684961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40512502302602024796493229 15192188363475759298684961)
  ·
    refine ⟨11394141272606819474013721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15192188363475759298684961 11394141272606819474013721)
    ·
      refine ⟨8545605954455114605510291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11394141272606819474013721 8545605954455114605510291)
      ·
        refine ⟨12818408931682671908265437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8545605954455114605510291 12818408931682671908265437)
        ·
          refine ⟨4806903349381001965599539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12818408931682671908265437 4806903349381001965599539)
          ·
            refine ⟨7210355024071502948399309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4806903349381001965599539 7210355024071502948399309)
            ·
              refine ⟨2703883134026813605649741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7210355024071502948399309 2703883134026813605649741)
              ·
                refine ⟨1013956175260055102118653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2703883134026813605649741 1013956175260055102118653)
                ·
                  refine ⟨380233565722520663294495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013956175260055102118653 380233565722520663294495)
                  ·
                    rfl

theorem cell21_1666130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_1666130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666130 prefixEnd_1666130 := by exact prefixLift 1666130
  have htrace : WordTrace (prefixWord ++ tailWord_1666130) baseStart_1666130 baseEnd_1666130 := by
    simpa [prefixWord, tailWord_1666130, baseEnd_1666130] using wordTrace_append hprefix tailTrace_1666130
  have hstable : (prefixWord ++ tailWord_1666130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666130).length < 2 ^ (prefixWord ++ tailWord_1666130).sum := by decide
  have hdescent : baseEnd_1666130 < baseStart_1666130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666158 : List Nat := [4, 1, 2, 2, 1, 3, 2, 6]
def baseStart_1666158 : Nat := 118140960795 + 1666158 * 2 ^ 59
def prefixEnd_1666158 : Nat := 4983230072969 + 3 ^ 40 * 1666158 * 2
def baseEnd_1666158 : Nat := 126746651901332945609257

theorem tailTrace_1666158 : CollatzResearch.WordTrace tailWord_1666158 prefixEnd_1666158 126746651901332945609257 := by
  unfold tailWord_1666158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7596221837225199747094891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40513183131867731984506085 7596221837225199747094891)
  ·
    refine ⟨11394332755837799620642337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7596221837225199747094891 11394332755837799620642337)
    ·
      refine ⟨8545749566878349715481753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11394332755837799620642337 8545749566878349715481753)
      ·
        refine ⟨6409312175158762286611315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8545749566878349715481753 6409312175158762286611315)
        ·
          refine ⟨9613968262738143429916973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6409312175158762286611315 9613968262738143429916973)
          ·
            refine ⟨3605238098526803786218865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9613968262738143429916973 3605238098526803786218865)
            ·
              refine ⟨2703928573895102839664149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3605238098526803786218865 2703928573895102839664149)
              ·
                refine ⟨126746651901332945609257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2703928573895102839664149 126746651901332945609257)
                ·
                  rfl

theorem cell21_1666158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_1666158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666158 prefixEnd_1666158 := by exact prefixLift 1666158
  have htrace : WordTrace (prefixWord ++ tailWord_1666158) baseStart_1666158 baseEnd_1666158 := by
    simpa [prefixWord, tailWord_1666158, baseEnd_1666158] using wordTrace_append hprefix tailTrace_1666158
  have hstable : (prefixWord ++ tailWord_1666158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666158).length < 2 ^ (prefixWord ++ tailWord_1666158).sum := by decide
  have hdescent : baseEnd_1666158 < baseStart_1666158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666352 : List Nat := [2, 1, 1, 1, 2, 2, 3, 9]
def baseStart_1666352 : Nat := 118140960795 + 1666352 * 2 ^ 59
def prefixEnd_1666352 : Nat := 4983230072969 + 3 ^ 40 * 1666352 * 2
def baseEnd_1666352 : Nat := 126761409715699203531347

theorem tailTrace_1666352 : CollatzResearch.WordTrace tailWord_1666352 prefixEnd_1666352 126761409715699203531347 := by
  unfold tailWord_1666352
  simp only [CollatzResearch.WordTrace]
  refine ⟨30388425229549384554660655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40517900306065846072880873 30388425229549384554660655)
  ·
    refine ⟨45582637844324076831990983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30388425229549384554660655 45582637844324076831990983)
    ·
      refine ⟨68373956766486115247986475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45582637844324076831990983 68373956766486115247986475)
      ·
        refine ⟨102560935149729172871979713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68373956766486115247986475 102560935149729172871979713)
        ·
          refine ⟨76920701362296879653984785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102560935149729172871979713 76920701362296879653984785)
          ·
            refine ⟨57690526021722659740488589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76920701362296879653984785 57690526021722659740488589)
            ·
              refine ⟨21633947258145997402683221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57690526021722659740488589 21633947258145997402683221)
              ·
                refine ⟨126761409715699203531347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21633947258145997402683221 126761409715699203531347)
                ·
                  rfl

theorem cell21_1666352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 9].length) (baseStart_1666352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666352 prefixEnd_1666352 := by exact prefixLift 1666352
  have htrace : WordTrace (prefixWord ++ tailWord_1666352) baseStart_1666352 baseEnd_1666352 := by
    simpa [prefixWord, tailWord_1666352, baseEnd_1666352] using wordTrace_append hprefix tailTrace_1666352
  have hstable : (prefixWord ++ tailWord_1666352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666352).length < 2 ^ (prefixWord ++ tailWord_1666352).sum := by decide
  have hdescent : baseEnd_1666352 < baseStart_1666352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666369 : List Nat := [1, 2, 5, 2, 1, 10]
def baseStart_1666369 : Nat := 118140960795 + 1666369 * 2 ^ 59
def prefixEnd_1666369 : Nat := 4983230072969 + 3 ^ 40 * 1666369 * 2
def baseEnd_1666369 : Nat := 14084744769581828104099

theorem tailTrace_1666369 : CollatzResearch.WordTrace tailWord_1666369 prefixEnd_1666369 14084744769581828104099 := by
  unfold tailWord_1666369
  simp only [CollatzResearch.WordTrace]
  refine ⟨60777470500037181012690161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40518313666691454008460107 60777470500037181012690161)
  ·
    refine ⟨45583102875027885759517621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60777470500037181012690161 45583102875027885759517621)
    ·
      refine ⟨4273415894533864289954777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45583102875027885759517621 4273415894533864289954777)
      ·
        refine ⟨3205061920900398217466083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4273415894533864289954777 3205061920900398217466083)
        ·
          refine ⟨4807592881350597326199125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3205061920900398217466083 4807592881350597326199125)
          ·
            refine ⟨14084744769581828104099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4807592881350597326199125 14084744769581828104099)
            ·
              rfl

theorem cell21_1666369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 10].length) (baseStart_1666369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666369 prefixEnd_1666369 := by exact prefixLift 1666369
  have htrace : WordTrace (prefixWord ++ tailWord_1666369) baseStart_1666369 baseEnd_1666369 := by
    simpa [prefixWord, tailWord_1666369, baseEnd_1666369] using wordTrace_append hprefix tailTrace_1666369
  have hstable : (prefixWord ++ tailWord_1666369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666369).length < 2 ^ (prefixWord ++ tailWord_1666369).sum := by decide
  have hdescent : baseEnd_1666369 < baseStart_1666369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666372 : List Nat := [2, 3, 4, 1, 1, 1, 1, 4, 4]
def baseStart_1666372 : Nat := 118140960795 + 1666372 * 2 ^ 59
def prefixEnd_1666372 : Nat := 4983230072969 + 3 ^ 40 * 1666372 * 2
def baseEnd_1666372 : Nat := 380288793419582020260667

theorem tailTrace_1666372 : CollatzResearch.WordTrace tailWord_1666372 prefixEnd_1666372 380288793419582020260667 := by
  unfold tailWord_1666372
  simp only [CollatzResearch.WordTrace]
  refine ⟨30388789959513156262524685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40518386612684208350032913 30388789959513156262524685)
  ·
    refine ⟨11395796234817433598446757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30388789959513156262524685 11395796234817433598446757)
    ·
      refine ⟨2136711794028268799708767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11395796234817433598446757 2136711794028268799708767)
      ·
        refine ⟨3205067691042403199563151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2136711794028268799708767 3205067691042403199563151)
        ·
          refine ⟨4807601536563604799344727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3205067691042403199563151 4807601536563604799344727)
          ·
            refine ⟨7211402304845407199017091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4807601536563604799344727 7211402304845407199017091)
            ·
              refine ⟨10817103457268110798525637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7211402304845407199017091 10817103457268110798525637)
              ·
                refine ⟨2028206898237770774723557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10817103457268110798525637 2028206898237770774723557)
                ·
                  refine ⟨380288793419582020260667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2028206898237770774723557 380288793419582020260667)
                  ·
                    rfl

theorem cell21_1666372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_1666372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666372 prefixEnd_1666372 := by exact prefixLift 1666372
  have htrace : WordTrace (prefixWord ++ tailWord_1666372) baseStart_1666372 baseEnd_1666372 := by
    simpa [prefixWord, tailWord_1666372, baseEnd_1666372] using wordTrace_append hprefix tailTrace_1666372
  have hstable : (prefixWord ++ tailWord_1666372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666372).length < 2 ^ (prefixWord ++ tailWord_1666372).sum := by decide
  have hdescent : baseEnd_1666372 < baseStart_1666372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666400 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 5]
def baseStart_1666400 : Nat := 118140960795 + 1666400 * 2 ^ 59
def prefixEnd_1666400 : Nat := 4983230072969 + 3 ^ 40 * 1666400 * 2
def baseEnd_1666400 : Nat := 380295183401060193793943

theorem tailTrace_1666400 : CollatzResearch.WordTrace tailWord_1666400 prefixEnd_1666400 380295183401060193793943 := by
  unfold tailWord_1666400
  simp only [CollatzResearch.WordTrace]
  refine ⟨30389300581462436653534327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40519067441949915538045769 30389300581462436653534327)
  ·
    refine ⟨45583950872193654980301491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30389300581462436653534327 45583950872193654980301491)
    ·
      refine ⟨68375926308290482470452237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45583950872193654980301491 68375926308290482470452237)
      ·
        refine ⟨25640972365608930926419589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68375926308290482470452237 25640972365608930926419589)
        ·
          refine ⟨4807682318551674548703673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25640972365608930926419589 4807682318551674548703673)
          ·
            refine ⟨3605761738913755911527755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4807682318551674548703673 3605761738913755911527755)
            ·
              refine ⟨5408642608370633867291633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3605761738913755911527755 5408642608370633867291633)
              ·
                refine ⟨4056481956277975400468725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5408642608370633867291633 4056481956277975400468725)
                ·
                  refine ⟨380295183401060193793943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4056481956277975400468725 380295183401060193793943)
                  ·
                    rfl

theorem cell21_1666400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_1666400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666400 prefixEnd_1666400 := by exact prefixLift 1666400
  have htrace : WordTrace (prefixWord ++ tailWord_1666400) baseStart_1666400 baseEnd_1666400 := by
    simpa [prefixWord, tailWord_1666400, baseEnd_1666400] using wordTrace_append hprefix tailTrace_1666400
  have hstable : (prefixWord ++ tailWord_1666400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666400).length < 2 ^ (prefixWord ++ tailWord_1666400).sum := by decide
  have hdescent : baseEnd_1666400 < baseStart_1666400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666428 : List Nat := [2, 2, 2, 1, 1, 1, 12]
def baseStart_1666428 : Nat := 118140960795 + 1666428 * 2 ^ 59
def prefixEnd_1666428 : Nat := 4983230072969 + 3 ^ 40 * 1666428 * 2
def baseEnd_1666428 : Nat := 42255730375837596369691

theorem tailTrace_1666428 : CollatzResearch.WordTrace tailWord_1666428 prefixEnd_1666428 42255730375837596369691 := by
  unfold tailWord_1666428
  simp only [CollatzResearch.WordTrace]
  refine ⟨30389811203411717044543969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40519748271215622726058625 30389811203411717044543969)
  ·
    refine ⟨22792358402558787783407977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30389811203411717044543969 22792358402558787783407977)
    ·
      refine ⟨17094268801919090837555983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22792358402558787783407977 17094268801919090837555983)
      ·
        refine ⟨25641403202878636256333975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17094268801919090837555983 25641403202878636256333975)
        ·
          refine ⟨38462104804317954384500963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25641403202878636256333975 38462104804317954384500963)
          ·
            refine ⟨57693157206476931576751445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38462104804317954384500963 57693157206476931576751445)
            ·
              refine ⟨42255730375837596369691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 57693157206476931576751445 42255730375837596369691)
              ·
                rfl

theorem cell21_1666428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 12].length) (baseStart_1666428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666428 prefixEnd_1666428 := by exact prefixLift 1666428
  have htrace : WordTrace (prefixWord ++ tailWord_1666428) baseStart_1666428 baseEnd_1666428 := by
    simpa [prefixWord, tailWord_1666428, baseEnd_1666428] using wordTrace_append hprefix tailTrace_1666428
  have hstable : (prefixWord ++ tailWord_1666428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666428).length < 2 ^ (prefixWord ++ tailWord_1666428).sum := by decide
  have hdescent : baseEnd_1666428 < baseStart_1666428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666434 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1666434 : Nat := 118140960795 + 1666434 * 2 ^ 59
def prefixEnd_1666434 : Nat := 4983230072969 + 3 ^ 40 * 1666434 * 2
def baseEnd_1666434 : Nat := 380302942664283690227207

theorem tailTrace_1666434 : CollatzResearch.WordTrace tailWord_1666434 prefixEnd_1666434 380302942664283690227207 := by
  unfold tailWord_1666434
  simp only [CollatzResearch.WordTrace]
  refine ⟨15194960311200424278451589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40519894163201131409204237 15194960311200424278451589)
  ·
    refine ⟨2849055058350079552209673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15194960311200424278451589 2849055058350079552209673)
    ·
      refine ⟨2136791293762559664157255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2849055058350079552209673 2136791293762559664157255)
      ·
        refine ⟨3205186940643839496235883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2136791293762559664157255 3205186940643839496235883)
        ·
          refine ⟨4807780410965759244353825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3205186940643839496235883 4807780410965759244353825)
          ·
            refine ⟨3605835308224319433265369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4807780410965759244353825 3605835308224319433265369)
            ·
              refine ⟨2704376481168239574949027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3605835308224319433265369 2704376481168239574949027)
              ·
                refine ⟨4056564721752359362423541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2704376481168239574949027 4056564721752359362423541)
                ·
                  refine ⟨380302942664283690227207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4056564721752359362423541 380302942664283690227207)
                  ·
                    rfl

theorem cell21_1666434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1666434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666434 prefixEnd_1666434 := by exact prefixLift 1666434
  have htrace : WordTrace (prefixWord ++ tailWord_1666434) baseStart_1666434 baseEnd_1666434 := by
    simpa [prefixWord, tailWord_1666434, baseEnd_1666434] using wordTrace_append hprefix tailTrace_1666434
  have hstable : (prefixWord ++ tailWord_1666434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666434).length < 2 ^ (prefixWord ++ tailWord_1666434).sum := by decide
  have hdescent : baseEnd_1666434 < baseStart_1666434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666507 : List Nat := [1, 1, 1, 1, 3, 3, 6, 1, 4]
def baseStart_1666507 : Nat := 118140960795 + 1666507 * 2 ^ 59
def prefixEnd_1666507 : Nat := 4983230072969 + 3 ^ 40 * 1666507 * 2
def baseEnd_1666507 : Nat := 380319602258851785510391

theorem tailTrace_1666507 : CollatzResearch.WordTrace tailWord_1666507 prefixEnd_1666507 380319602258851785510391 := by
  unfold tailWord_1666507
  simp only [CollatzResearch.WordTrace]
  refine ⟨60782503773537230581213775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40521669182358153720809183 60782503773537230581213775)
  ·
    refine ⟨91173755660305845871820663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60782503773537230581213775 91173755660305845871820663)
    ·
      refine ⟨136760633490458768807730995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91173755660305845871820663 136760633490458768807730995)
      ·
        refine ⟨205140950235688153211596493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136760633490458768807730995 205140950235688153211596493)
        ·
          refine ⟨76927856338383057454348685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205140950235688153211596493 76927856338383057454348685)
          ·
            refine ⟨28847946126893646545380757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76927856338383057454348685 28847946126893646545380757)
            ·
              refine ⟨1352247474698139681814723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28847946126893646545380757 1352247474698139681814723)
              ·
                refine ⟨2028371212047209522722085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1352247474698139681814723 2028371212047209522722085)
                ·
                  refine ⟨380319602258851785510391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2028371212047209522722085 380319602258851785510391)
                  ·
                    rfl

theorem cell21_1666507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 4].length) (baseStart_1666507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666507 prefixEnd_1666507 := by exact prefixLift 1666507
  have htrace : WordTrace (prefixWord ++ tailWord_1666507) baseStart_1666507 baseEnd_1666507 := by
    simpa [prefixWord, tailWord_1666507, baseEnd_1666507] using wordTrace_append hprefix tailTrace_1666507
  have hstable : (prefixWord ++ tailWord_1666507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666507).length < 2 ^ (prefixWord ++ tailWord_1666507).sum := by decide
  have hdescent : baseEnd_1666507 < baseStart_1666507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666611 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 5]
def baseStart_1666611 : Nat := 118140960795 + 1666611 * 2 ^ 59
def prefixEnd_1666611 : Nat := 4983230072969 + 3 ^ 40 * 1666611 * 2
def baseEnd_1666611 : Nat := 380343336475770715776845

theorem tailTrace_1666611 : CollatzResearch.WordTrace tailWord_1666611 prefixEnd_1666611 380343336475770715776845 := by
  unfold tailWord_1666611
  simp only [CollatzResearch.WordTrace]
  refine ⟨60786296965160456342999687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40524197976773637561999791 60786296965160456342999687)
  ·
    refine ⟨91179445447740684514499531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60786296965160456342999687 91179445447740684514499531)
    ·
      refine ⟨136769168171611026771749297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91179445447740684514499531 136769168171611026771749297)
      ·
        refine ⟨102576876128708270078811973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136769168171611026771749297 102576876128708270078811973)
        ·
          refine ⟨19233164274132800639777245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102576876128708270078811973 19233164274132800639777245)
          ·
            refine ⟨7212436602799800239916467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19233164274132800639777245 7212436602799800239916467)
            ·
              refine ⟨10818654904199700359874701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7212436602799800239916467 10818654904199700359874701)
              ·
                refine ⟨4056995589074887634953013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10818654904199700359874701 4056995589074887634953013)
                ·
                  refine ⟨380343336475770715776845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4056995589074887634953013 380343336475770715776845)
                  ·
                    rfl

theorem cell21_1666611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 5].length) (baseStart_1666611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666611 prefixEnd_1666611 := by exact prefixLift 1666611
  have htrace : WordTrace (prefixWord ++ tailWord_1666611) baseStart_1666611 baseEnd_1666611 := by
    simpa [prefixWord, tailWord_1666611, baseEnd_1666611] using wordTrace_append hprefix tailTrace_1666611
  have hstable : (prefixWord ++ tailWord_1666611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666611).length < 2 ^ (prefixWord ++ tailWord_1666611).sum := by decide
  have hdescent : baseEnd_1666611 < baseStart_1666611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666631 : List Nat := [1, 1, 4, 1, 6, 1, 2, 5]
def baseStart_1666631 : Nat := 118140960795 + 1666631 * 2 ^ 59
def prefixEnd_1666631 : Nat := 4983230072969 + 3 ^ 40 * 1666631 * 2
def baseEnd_1666631 : Nat := 126782633582751708481157

theorem tailTrace_1666631 : CollatzResearch.WordTrace tailWord_1666631 prefixEnd_1666631 126782633582751708481157 := by
  unfold tailWord_1666631
  simp only [CollatzResearch.WordTrace]
  refine ⟨60787026425087999758727747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40524684283391999839151831 60787026425087999758727747)
  ·
    refine ⟨91180539637631999638091621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60787026425087999758727747 91180539637631999638091621)
    ·
      refine ⟨17096351182055999932142179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91180539637631999638091621 17096351182055999932142179)
      ·
        refine ⟨25644526773083999898213269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17096351182055999932142179 25644526773083999898213269)
        ·
          refine ⟨1202087192488312495228747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25644526773083999898213269 1202087192488312495228747)
          ·
            refine ⟨1803130788732468742843121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202087192488312495228747 1803130788732468742843121)
            ·
              refine ⟨1352348091549351557132341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1803130788732468742843121 1352348091549351557132341)
              ·
                refine ⟨126782633582751708481157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1352348091549351557132341 126782633582751708481157)
                ·
                  rfl

theorem cell21_1666631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 5].length) (baseStart_1666631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666631 prefixEnd_1666631 := by exact prefixLift 1666631
  have htrace : WordTrace (prefixWord ++ tailWord_1666631) baseStart_1666631 baseEnd_1666631 := by
    simpa [prefixWord, tailWord_1666631, baseEnd_1666631] using wordTrace_append hprefix tailTrace_1666631
  have hstable : (prefixWord ++ tailWord_1666631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666631).length < 2 ^ (prefixWord ++ tailWord_1666631).sum := by decide
  have hdescent : baseEnd_1666631 < baseStart_1666631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666642 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 6]
def baseStart_1666642 : Nat := 118140960795 + 1666642 * 2 ^ 59
def prefixEnd_1666642 : Nat := 4983230072969 + 3 ^ 40 * 1666642 * 2
def baseEnd_1666642 : Nat := 380350411098121550760115

theorem tailTrace_1666642 : CollatzResearch.WordTrace tailWord_1666642 prefixEnd_1666642 380350411098121550760115 := by
  unfold tailWord_1666642
  simp only [CollatzResearch.WordTrace]
  refine ⟨15196856907012037159344545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40524951752032099091585453 15196856907012037159344545)
  ·
    refine ⟨11397642680259027869508409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15196856907012037159344545 11397642680259027869508409)
    ·
      refine ⟨8548232010194270902131307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11397642680259027869508409 8548232010194270902131307)
      ·
        refine ⟨12822348015291406353196961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8548232010194270902131307 12822348015291406353196961)
        ·
          refine ⟨9616761011468554764897721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12822348015291406353196961 9616761011468554764897721)
          ·
            refine ⟨7212570758601416073673291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9616761011468554764897721 7212570758601416073673291)
            ·
              refine ⟨10818856137902124110509937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7212570758601416073673291 10818856137902124110509937)
              ·
                refine ⟨8114142103426593082882453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10818856137902124110509937 8114142103426593082882453)
                ·
                  refine ⟨380350411098121550760115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8114142103426593082882453 380350411098121550760115)
                  ·
                    rfl

theorem cell21_1666642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_1666642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666642 prefixEnd_1666642 := by exact prefixLift 1666642
  have htrace : WordTrace (prefixWord ++ tailWord_1666642) baseStart_1666642 baseEnd_1666642 := by
    simpa [prefixWord, tailWord_1666642, baseEnd_1666642] using wordTrace_append hprefix tailTrace_1666642
  have hstable : (prefixWord ++ tailWord_1666642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666642).length < 2 ^ (prefixWord ++ tailWord_1666642).sum := by decide
  have hdescent : baseEnd_1666642 < baseStart_1666642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666721 : List Nat := [1, 2, 3, 3, 2, 2, 1, 4, 3]
def baseStart_1666721 : Nat := 118140960795 + 1666721 * 2 ^ 59
def prefixEnd_1666721 : Nat := 4983230072969 + 3 ^ 40 * 1666721 * 2
def baseEnd_1666721 : Nat := 380368439974434968943287

theorem tailTrace_1666721 : CollatzResearch.WordTrace tailWord_1666721 prefixEnd_1666721 380368439974434968943287 := by
  unfold tailWord_1666721
  simp only [CollatzResearch.WordTrace]
  refine ⟨60790308994761945129504017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40526872663174630086336011 60790308994761945129504017)
  ·
    refine ⟨45592731746071458847128013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60790308994761945129504017 45592731746071458847128013)
    ·
      refine ⟨17097274404776797067673005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45592731746071458847128013 17097274404776797067673005)
      ·
        refine ⟨6411477901791298900377377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17097274404776797067673005 6411477901791298900377377)
        ·
          refine ⟨4808608426343474175283033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6411477901791298900377377 4808608426343474175283033)
          ·
            refine ⟨3606456319757605631462275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4808608426343474175283033 3606456319757605631462275)
            ·
              refine ⟨5409684479636408447193413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3606456319757605631462275 5409684479636408447193413)
              ·
                refine ⟨1014315839931826583848765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5409684479636408447193413 1014315839931826583848765)
                ·
                  refine ⟨380368439974434968943287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1014315839931826583848765 380368439974434968943287)
                  ·
                    rfl

theorem cell21_1666721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 3].length) (baseStart_1666721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666721 prefixEnd_1666721 := by exact prefixLift 1666721
  have htrace : WordTrace (prefixWord ++ tailWord_1666721) baseStart_1666721 baseEnd_1666721 := by
    simpa [prefixWord, tailWord_1666721, baseEnd_1666721] using wordTrace_append hprefix tailTrace_1666721
  have hstable : (prefixWord ++ tailWord_1666721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666721).length < 2 ^ (prefixWord ++ tailWord_1666721).sum := by decide
  have hdescent : baseEnd_1666721 < baseStart_1666721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666749 : List Nat := [1, 4, 1, 2, 1, 2, 5, 5]
def baseStart_1666749 : Nat := 118140960795 + 1666749 * 2 ^ 59
def prefixEnd_1666749 : Nat := 4983230072969 + 3 ^ 40 * 1666749 * 2
def baseEnd_1666749 : Nat := 126791609985304380825521

theorem tailTrace_1666749 : CollatzResearch.WordTrace tailWord_1666749 prefixEnd_1666749 126791609985304380825521 := by
  unfold tailWord_1666749
  simp only [CollatzResearch.WordTrace]
  refine ⟨60791330238660505911523301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40527553492440337274348867 60791330238660505911523301)
  ·
    refine ⟨11398374419748844858410619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60791330238660505911523301 11398374419748844858410619)
    ·
      refine ⟨17097561629623267287615929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11398374419748844858410619 17097561629623267287615929)
      ·
        refine ⟨12823171222217450465711947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17097561629623267287615929 12823171222217450465711947)
        ·
          refine ⟨19234756833326175698567921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12823171222217450465711947 19234756833326175698567921)
          ·
            refine ⟨14426067624994631773925941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19234756833326175698567921 14426067624994631773925941)
            ·
              refine ⟨1352443839843246728805557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14426067624994631773925941 1352443839843246728805557)
              ·
                refine ⟨126791609985304380825521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1352443839843246728805557 126791609985304380825521)
                ·
                  rfl

theorem cell21_1666749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 5].length) (baseStart_1666749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666749 prefixEnd_1666749 := by exact prefixLift 1666749
  have htrace : WordTrace (prefixWord ++ tailWord_1666749) baseStart_1666749 baseEnd_1666749 := by
    simpa [prefixWord, tailWord_1666749, baseEnd_1666749] using wordTrace_append hprefix tailTrace_1666749
  have hstable : (prefixWord ++ tailWord_1666749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666749).length < 2 ^ (prefixWord ++ tailWord_1666749).sum := by decide
  have hdescent : baseEnd_1666749 < baseStart_1666749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666794 : List Nat := [3, 1, 3, 1, 1, 1, 2, 5, 4]
def baseStart_1666794 : Nat := 118140960795 + 1666794 * 2 ^ 59
def prefixEnd_1666794 : Nat := 4983230072969 + 3 ^ 40 * 1666794 * 2
def baseEnd_1666794 : Nat := 380385099569003064226471

theorem tailTrace_1666794 : CollatzResearch.WordTrace tailWord_1666794 prefixEnd_1666794 380385099569003064226471 := by
  unfold tailWord_1666794
  simp only [CollatzResearch.WordTrace]
  refine ⟨15198242880874369649227859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40528647682331652397940957 15198242880874369649227859)
  ·
    refine ⟨22797364321311554473841789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15198242880874369649227859 22797364321311554473841789)
    ·
      refine ⟨8549011620491832927690671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22797364321311554473841789 8549011620491832927690671)
      ·
        refine ⟨12823517430737749391536007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8549011620491832927690671 12823517430737749391536007)
        ·
          refine ⟨19235276146106624087304011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12823517430737749391536007 19235276146106624087304011)
          ·
            refine ⟨28852914219159936130956017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19235276146106624087304011 28852914219159936130956017)
            ·
              refine ⟨21639685664369952098217013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28852914219159936130956017 21639685664369952098217013)
              ·
                refine ⟨2028720531034683009207845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21639685664369952098217013 2028720531034683009207845)
                ·
                  refine ⟨380385099569003064226471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2028720531034683009207845 380385099569003064226471)
                  ·
                    rfl

theorem cell21_1666794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_1666794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666794 prefixEnd_1666794 := by exact prefixLift 1666794
  have htrace : WordTrace (prefixWord ++ tailWord_1666794) baseStart_1666794 baseEnd_1666794 := by
    simpa [prefixWord, tailWord_1666794, baseEnd_1666794] using wordTrace_append hprefix tailTrace_1666794
  have hstable : (prefixWord ++ tailWord_1666794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666794).length < 2 ^ (prefixWord ++ tailWord_1666794).sum := by decide
  have hdescent : baseEnd_1666794 < baseStart_1666794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666884 : List Nat := [2, 3, 4, 12]
def baseStart_1666884 : Nat := 118140960795 + 1666884 * 2 ^ 59
def prefixEnd_1666884 : Nat := 4983230072969 + 3 ^ 40 * 1666884 * 2
def baseEnd_1666884 : Nat := 1565455303683880278709

theorem tailTrace_1666884 : CollatzResearch.WordTrace tailWord_1666884 prefixEnd_1666884 1565455303683880278709 := by
  unfold tailWord_1666884
  simp only [CollatzResearch.WordTrace]
  refine ⟨30398127046585711983843853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40530836062114282645125137 30398127046585711983843853)
  ·
    refine ⟨11399297642469641993941445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30398127046585711983843853 11399297642469641993941445)
    ·
      refine ⟨2137368307963057873864021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11399297642469641993941445 2137368307963057873864021)
      ·
        refine ⟨1565455303683880278709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2137368307963057873864021 1565455303683880278709)
        ·
          rfl

theorem cell21_1666884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 12].length) (baseStart_1666884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666884 prefixEnd_1666884 := by exact prefixLift 1666884
  have htrace : WordTrace (prefixWord ++ tailWord_1666884) baseStart_1666884 baseEnd_1666884 := by
    simpa [prefixWord, tailWord_1666884, baseEnd_1666884] using wordTrace_append hprefix tailTrace_1666884
  have hstable : (prefixWord ++ tailWord_1666884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666884).length < 2 ^ (prefixWord ++ tailWord_1666884).sum := by decide
  have hdescent : baseEnd_1666884 < baseStart_1666884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666901 : List Nat := [1, 3, 2, 2, 2, 4, 1, 6]
def baseStart_1666901 : Nat := 118140960795 + 1666901 * 2 ^ 59
def prefixEnd_1666901 : Nat := 4983230072969 + 3 ^ 40 * 1666901 * 2
def baseEnd_1666901 : Nat := 126803172808931551980973

theorem tailTrace_1666901 : CollatzResearch.WordTrace tailWord_1666901 prefixEnd_1666901 126803172808931551980973 := by
  unfold tailWord_1666901
  simp only [CollatzResearch.WordTrace]
  refine ⟨60796874134109835871056557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40531249422739890580704371 60796874134109835871056557)
  ·
    refine ⟨22798827800291188451646209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60796874134109835871056557 22798827800291188451646209)
    ·
      refine ⟨17099120850218391338734657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22798827800291188451646209 17099120850218391338734657)
      ·
        refine ⟨12824340637663793504050993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17099120850218391338734657 12824340637663793504050993)
        ·
          refine ⟨9618255478247845128038245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12824340637663793504050993 9618255478247845128038245)
          ·
            refine ⟨1803422902171470961507171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9618255478247845128038245 1803422902171470961507171)
            ·
              refine ⟨2705134353257206442260757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803422902171470961507171 2705134353257206442260757)
              ·
                refine ⟨126803172808931551980973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2705134353257206442260757 126803172808931551980973)
                ·
                  rfl

theorem cell21_1666901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 6].length) (baseStart_1666901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666901 prefixEnd_1666901 := by exact prefixLift 1666901
  have htrace : WordTrace (prefixWord ++ tailWord_1666901) baseStart_1666901 baseEnd_1666901 := by
    simpa [prefixWord, tailWord_1666901, baseEnd_1666901] using wordTrace_append hprefix tailTrace_1666901
  have hstable : (prefixWord ++ tailWord_1666901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666901).length < 2 ^ (prefixWord ++ tailWord_1666901).sum := by decide
  have hdescent : baseEnd_1666901 < baseStart_1666901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666929 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 6]
def baseStart_1666929 : Nat := 118140960795 + 1666929 * 2 ^ 59
def prefixEnd_1666929 : Nat := 4983230072969 + 3 ^ 40 * 1666929 * 2
def baseEnd_1666929 : Nat := 380415908408272829476195

theorem tailTrace_1666929 : CollatzResearch.WordTrace tailWord_1666929 prefixEnd_1666929 380415908408272829476195 := by
  unfold tailWord_1666929
  simp only [CollatzResearch.WordTrace]
  refine ⟨60797895378008396653075841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40531930252005597768717227 60797895378008396653075841)
  ·
    refine ⟨45598421533506297489806881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60797895378008396653075841 45598421533506297489806881)
    ·
      refine ⟨34198816150129723117355161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45598421533506297489806881 34198816150129723117355161)
      ·
        refine ⟨25649112112597292338016371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34198816150129723117355161 25649112112597292338016371)
        ·
          refine ⟨38473668168895938507024557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25649112112597292338016371 38473668168895938507024557)
          ·
            refine ⟨14427625563335976940134209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38473668168895938507024557 14427625563335976940134209)
            ·
              refine ⟨10820719172501982705100657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14427625563335976940134209 10820719172501982705100657)
              ·
                refine ⟨8115539379376487028825493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10820719172501982705100657 8115539379376487028825493)
                ·
                  refine ⟨380415908408272829476195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8115539379376487028825493 380415908408272829476195)
                  ·
                    rfl

theorem cell21_1666929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_1666929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666929 prefixEnd_1666929 := by exact prefixLift 1666929
  have htrace : WordTrace (prefixWord ++ tailWord_1666929) baseStart_1666929 baseEnd_1666929 := by
    simpa [prefixWord, tailWord_1666929, baseEnd_1666929] using wordTrace_append hprefix tailTrace_1666929
  have hstable : (prefixWord ++ tailWord_1666929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666929).length < 2 ^ (prefixWord ++ tailWord_1666929).sum := by decide
  have hdescent : baseEnd_1666929 < baseStart_1666929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666977 : List Nat := [1, 2, 3, 4, 2, 1, 1, 7]
def baseStart_1666977 : Nat := 118140960795 + 1666977 * 2 ^ 59
def prefixEnd_1666977 : Nat := 4983230072969 + 3 ^ 40 * 1666977 * 2
def baseEnd_1666977 : Nat := 126808954220745137558699

theorem tailTrace_1666977 : CollatzResearch.WordTrace tailWord_1666977 prefixEnd_1666977 126808954220745137558699 := by
  unfold tailWord_1666977
  simp only [CollatzResearch.WordTrace]
  refine ⟨60799646081834500850823185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40533097387889667233882123 60799646081834500850823185)
  ·
    refine ⟨45599734561375875638117389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60799646081834500850823185 45599734561375875638117389)
    ·
      refine ⟨17099900460515953364294021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45599734561375875638117389 17099900460515953364294021)
      ·
        refine ⟨3206231336346741255805129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17099900460515953364294021 3206231336346741255805129)
        ·
          refine ⟨2404673502260055941853847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3206231336346741255805129 2404673502260055941853847)
          ·
            refine ⟨3607010253390083912780771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2404673502260055941853847 3607010253390083912780771)
            ·
              refine ⟨5410515380085125869171157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3607010253390083912780771 5410515380085125869171157)
              ·
                refine ⟨126808954220745137558699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5410515380085125869171157 126808954220745137558699)
                ·
                  rfl

theorem cell21_1666977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 7].length) (baseStart_1666977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1666977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1666977 prefixEnd_1666977 := by exact prefixLift 1666977
  have htrace : WordTrace (prefixWord ++ tailWord_1666977) baseStart_1666977 baseEnd_1666977 := by
    simpa [prefixWord, tailWord_1666977, baseEnd_1666977] using wordTrace_append hprefix tailTrace_1666977
  have hstable : (prefixWord ++ tailWord_1666977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666977).length < 2 ^ (prefixWord ++ tailWord_1666977).sum := by decide
  have hdescent : baseEnd_1666977 < baseStart_1666977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667022 : List Nat := [4, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_1667022 : Nat := 118140960795 + 1667022 * 2 ^ 59
def prefixEnd_1667022 : Nat := 4983230072969 + 3 ^ 40 * 1667022 * 2
def baseEnd_1667022 : Nat := 380437132275325334426005

theorem tailTrace_1667022 : CollatzResearch.WordTrace tailWord_1667022 prefixEnd_1667022 380437132275325334426005 := by
  unfold tailWord_1667022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7600160920833934192026415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40534191577780982357474213 7600160920833934192026415)
  ·
    refine ⟨11400241381250901288039623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7600160920833934192026415 11400241381250901288039623)
    ·
      refine ⟨17100362071876351932059435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11400241381250901288039623 17100362071876351932059435)
      ·
        refine ⟨25650543107814527898089153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17100362071876351932059435 25650543107814527898089153)
        ·
          refine ⟨19237907330860895923566865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25650543107814527898089153 19237907330860895923566865)
          ·
            refine ⟨14428430498145671942675149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19237907330860895923566865 14428430498145671942675149)
            ·
              refine ⟨5410661436804626978503181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14428430498145671942675149 5410661436804626978503181)
              ·
                refine ⟨2028998038801735116938693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5410661436804626978503181 2028998038801735116938693)
                ·
                  refine ⟨380437132275325334426005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2028998038801735116938693 380437132275325334426005)
                  ·
                    rfl

theorem cell21_1667022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_1667022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667022 prefixEnd_1667022 := by exact prefixLift 1667022
  have htrace : WordTrace (prefixWord ++ tailWord_1667022) baseStart_1667022 baseEnd_1667022 := by
    simpa [prefixWord, tailWord_1667022, baseEnd_1667022] using wordTrace_append hprefix tailTrace_1667022
  have hstable : (prefixWord ++ tailWord_1667022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667022).length < 2 ^ (prefixWord ++ tailWord_1667022).sum := by decide
  have hdescent : baseEnd_1667022 < baseStart_1667022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667053 : List Nat := [1, 5, 1, 4, 1, 9]
def baseStart_1667053 : Nat := 118140960795 + 1667053 * 2 ^ 59
def prefixEnd_1667053 : Nat := 4983230072969 + 3 ^ 40 * 1667053 * 2
def baseEnd_1667053 : Nat := 14090526181395413681825

theorem tailTrace_1667053 : CollatzResearch.WordTrace tailWord_1667053 prefixEnd_1667053 14090526181395413681825 := by
  unfold tailWord_1667053
  simp only [CollatzResearch.WordTrace]
  refine ⟨60802418029559165830589813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40534945353039443887059875 60802418029559165830589813)
  ·
    refine ⟨5700226690271171796617795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60802418029559165830589813 5700226690271171796617795)
    ·
      refine ⟨8550340035406757694926693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5700226690271171796617795 8550340035406757694926693)
      ·
        refine ⟨1603188756638767067798755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8550340035406757694926693 1603188756638767067798755)
        ·
          refine ⟨2404783134958150601698133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1603188756638767067798755 2404783134958150601698133)
          ·
            refine ⟨14090526181395413681825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2404783134958150601698133 14090526181395413681825)
            ·
              rfl

theorem cell21_1667053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 9].length) (baseStart_1667053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667053 prefixEnd_1667053 := by exact prefixLift 1667053
  have htrace : WordTrace (prefixWord ++ tailWord_1667053) baseStart_1667053 baseEnd_1667053 := by
    simpa [prefixWord, tailWord_1667053, baseEnd_1667053] using wordTrace_append hprefix tailTrace_1667053
  have hstable : (prefixWord ++ tailWord_1667053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667053).length < 2 ^ (prefixWord ++ tailWord_1667053).sum := by decide
  have hdescent : baseEnd_1667053 < baseStart_1667053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667070 : List Nat := [4, 2, 2, 2, 1, 3, 1, 6]
def baseStart_1667070 : Nat := 118140960795 + 1667070 * 2 ^ 59
def prefixEnd_1667070 : Nat := 4983230072969 + 3 ^ 40 * 1667070 * 2
def baseEnd_1667070 : Nat := 126816028843095972541969

theorem tailTrace_1667070 : CollatzResearch.WordTrace tailWord_1667070 prefixEnd_1667070 126816028843095972541969 := by
  unfold tailWord_1667070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7600379758812197216744833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40535358713665051822639109 7600379758812197216744833)
  ·
    refine ⟨5700284819109147912558625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7600379758812197216744833 5700284819109147912558625)
    ·
      refine ⟨4275213614331860934418969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5700284819109147912558625 4275213614331860934418969)
      ·
        refine ⟨3206410210748895700814227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4275213614331860934418969 3206410210748895700814227)
        ·
          refine ⟨4809615316123343551221341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3206410210748895700814227 4809615316123343551221341)
          ·
            refine ⟨1803605743546253831708003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4809615316123343551221341 1803605743546253831708003)
            ·
              refine ⟨2705408615319380747562005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803605743546253831708003 2705408615319380747562005)
              ·
                refine ⟨126816028843095972541969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2705408615319380747562005 126816028843095972541969)
                ·
                  rfl

theorem cell21_1667070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_1667070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667070 prefixEnd_1667070 := by exact prefixLift 1667070
  have htrace : WordTrace (prefixWord ++ tailWord_1667070) baseStart_1667070 baseEnd_1667070 := by
    simpa [prefixWord, tailWord_1667070, baseEnd_1667070] using wordTrace_append hprefix tailTrace_1667070
  have hstable : (prefixWord ++ tailWord_1667070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667070).length < 2 ^ (prefixWord ++ tailWord_1667070).sum := by decide
  have hdescent : baseEnd_1667070 < baseStart_1667070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667101 : List Nat := [1, 4, 2, 2, 2, 2, 2, 3, 3]
def baseStart_1667101 : Nat := 118140960795 + 1667101 * 2 ^ 59
def prefixEnd_1667101 : Nat := 4983230072969 + 3 ^ 40 * 1667101 * 2
def baseEnd_1667101 : Nat := 380455161151638752609177

theorem tailTrace_1667101 : CollatzResearch.WordTrace tailWord_1667101 prefixEnd_1667101 380455161151638752609177 := by
  unfold tailWord_1667101
  simp only [CollatzResearch.WordTrace]
  refine ⟨60804168733385270028337157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40536112488923513352224771 60804168733385270028337157)
  ·
    refine ⟨11400781637509738130313217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60804168733385270028337157 11400781637509738130313217)
    ·
      refine ⟨8550586228132303597734913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11400781637509738130313217 8550586228132303597734913)
      ·
        refine ⟨6412939671099227698301185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8550586228132303597734913 6412939671099227698301185)
        ·
          refine ⟨4809704753324420773725889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6412939671099227698301185 4809704753324420773725889)
          ·
            refine ⟨3607278564993315580294417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4809704753324420773725889 3607278564993315580294417)
            ·
              refine ⟨2705458923744986685220813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3607278564993315580294417 2705458923744986685220813)
              ·
                refine ⟨1014547096404370006957805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2705458923744986685220813 1014547096404370006957805)
                ·
                  refine ⟨380455161151638752609177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1014547096404370006957805 380455161151638752609177)
                  ·
                    rfl

theorem cell21_1667101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_1667101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667101 prefixEnd_1667101 := by exact prefixLift 1667101
  have htrace : WordTrace (prefixWord ++ tailWord_1667101) baseStart_1667101 baseEnd_1667101 := by
    simpa [prefixWord, tailWord_1667101, baseEnd_1667101] using wordTrace_append hprefix tailTrace_1667101
  have hstable : (prefixWord ++ tailWord_1667101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667101).length < 2 ^ (prefixWord ++ tailWord_1667101).sum := by decide
  have hdescent : baseEnd_1667101 < baseStart_1667101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667157 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 6]
def baseStart_1667157 : Nat := 118140960795 + 1667157 * 2 ^ 59
def prefixEnd_1667157 : Nat := 4983230072969 + 3 ^ 40 * 1667157 * 2
def baseEnd_1667157 : Nat := 380467941114595099675729

theorem tailTrace_1667157 : CollatzResearch.WordTrace tailWord_1667157 prefixEnd_1667157 380467941114595099675729 := by
  unfold tailWord_1667157
  simp only [CollatzResearch.WordTrace]
  refine ⟨60806211221182391592375725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40537474147454927728250483 60806211221182391592375725)
  ·
    refine ⟨22802329207943396847140897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60806211221182391592375725 22802329207943396847140897)
    ·
      refine ⟨17101746905957547635355673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22802329207943396847140897 17101746905957547635355673)
      ·
        refine ⟨12826310179468160726516755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17101746905957547635355673 12826310179468160726516755)
        ·
          refine ⟨19239465269202241089775133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12826310179468160726516755 19239465269202241089775133)
          ·
            refine ⟨7214799475950840408665675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19239465269202241089775133 7214799475950840408665675)
            ·
              refine ⟨10822199213926260612998513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7214799475950840408665675 10822199213926260612998513)
              ·
                refine ⟨8116649410444695459748885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10822199213926260612998513 8116649410444695459748885)
                ·
                  refine ⟨380467941114595099675729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8116649410444695459748885 380467941114595099675729)
                  ·
                    rfl

theorem cell21_1667157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_1667157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667157 prefixEnd_1667157 := by exact prefixLift 1667157
  have htrace : WordTrace (prefixWord ++ tailWord_1667157) baseStart_1667157 baseEnd_1667157 := by
    simpa [prefixWord, tailWord_1667157, baseEnd_1667157] using wordTrace_append hprefix tailTrace_1667157
  have hstable : (prefixWord ++ tailWord_1667157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667157).length < 2 ^ (prefixWord ++ tailWord_1667157).sum := by decide
  have hdescent : baseEnd_1667157 < baseStart_1667157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667160 : List Nat := [2, 1, 2, 2, 1, 4, 3, 3, 3]
def baseStart_1667160 : Nat := 118140960795 + 1667160 * 2 ^ 59
def prefixEnd_1667160 : Nat := 4983230072969 + 3 ^ 40 * 1667160 * 2
def baseEnd_1667160 : Nat := 380468625755467761125723

theorem tailTrace_1667160 : CollatzResearch.WordTrace tailWord_1667160 prefixEnd_1667160 380468625755467761125723 := by
  unfold tailWord_1667160
  simp only [CollatzResearch.WordTrace]
  refine ⟨30403160320085761552367467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40537547093447682069823289 30403160320085761552367467)
  ·
    refine ⟨45604740480128642328551201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30403160320085761552367467 45604740480128642328551201)
    ·
      refine ⟨34203555360096481746413401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45604740480128642328551201 34203555360096481746413401)
      ·
        refine ⟨25652666520072361309810051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34203555360096481746413401 25652666520072361309810051)
        ·
          refine ⟨38478999780108541964715077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25652666520072361309810051 38478999780108541964715077)
          ·
            refine ⟨7214812458770351618384077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38478999780108541964715077 7214812458770351618384077)
            ·
              refine ⟨2705554672038881856894029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7214812458770351618384077 2705554672038881856894029)
              ·
                refine ⟨1014583002014580696335261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2705554672038881856894029 1014583002014580696335261)
                ·
                  refine ⟨380468625755467761125723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1014583002014580696335261 380468625755467761125723)
                  ·
                    rfl

theorem cell21_1667160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 3].length) (baseStart_1667160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667160 prefixEnd_1667160 := by exact prefixLift 1667160
  have htrace : WordTrace (prefixWord ++ tailWord_1667160) baseStart_1667160 baseEnd_1667160 := by
    simpa [prefixWord, tailWord_1667160, baseEnd_1667160] using wordTrace_append hprefix tailTrace_1667160
  have hstable : (prefixWord ++ tailWord_1667160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667160).length < 2 ^ (prefixWord ++ tailWord_1667160).sum := by decide
  have hdescent : baseEnd_1667160 < baseStart_1667160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667171 : List Nat := [1, 1, 1, 5, 1, 1, 11]
def baseStart_1667171 : Nat := 118140960795 + 1667171 * 2 ^ 59
def prefixEnd_1667171 : Nat := 4983230072969 + 3 ^ 40 * 1667171 * 2
def baseEnd_1667171 : Nat := 42274570678370465160263

theorem tailTrace_1667171 : CollatzResearch.WordTrace tailWord_1667171 prefixEnd_1667171 42274570678370465160263 := by
  unfold tailWord_1667171
  simp only [CollatzResearch.WordTrace]
  refine ⟨60806721843131671983385367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40537814562087781322256911 60806721843131671983385367)
  ·
    refine ⟨91210082764697507975078051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60806721843131671983385367 91210082764697507975078051)
    ·
      refine ⟨136815124147046261962617077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91210082764697507975078051 136815124147046261962617077)
      ·
        refine ⟨12826417888785587058995351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136815124147046261962617077 12826417888785587058995351)
        ·
          refine ⟨19239626833178380588493027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12826417888785587058995351 19239626833178380588493027)
          ·
            refine ⟨28859440249767570882739541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19239626833178380588493027 28859440249767570882739541)
            ·
              refine ⟨42274570678370465160263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28859440249767570882739541 42274570678370465160263)
              ·
                rfl

theorem cell21_1667171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 11].length) (baseStart_1667171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667171 prefixEnd_1667171 := by exact prefixLift 1667171
  have htrace : WordTrace (prefixWord ++ tailWord_1667171) baseStart_1667171 baseEnd_1667171 := by
    simpa [prefixWord, tailWord_1667171, baseEnd_1667171] using wordTrace_append hprefix tailTrace_1667171
  have hstable : (prefixWord ++ tailWord_1667171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667171).length < 2 ^ (prefixWord ++ tailWord_1667171).sum := by decide
  have hdescent : baseEnd_1667171 < baseStart_1667171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667191 : List Nat := [1, 1, 3, 1, 1, 7, 2, 1, 4]
def baseStart_1667191 : Nat := 118140960795 + 1667191 * 2 ^ 59
def prefixEnd_1667191 : Nat := 4983230072969 + 3 ^ 40 * 1667191 * 2
def baseEnd_1667191 : Nat := 380475700377818596108993

theorem tailTrace_1667191 : CollatzResearch.WordTrace tailWord_1667191 prefixEnd_1667191 380475700377818596108993 := by
  unfold tailWord_1667191
  simp only [CollatzResearch.WordTrace]
  refine ⟨60807451303059215399113427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40538300868706143599408951 60807451303059215399113427)
  ·
    refine ⟨91211176954588823098670141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60807451303059215399113427 91211176954588823098670141)
    ·
      refine ⟨34204191357970808662001303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91211176954588823098670141 34204191357970808662001303)
      ·
        refine ⟨51306287036956212993001955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34204191357970808662001303 51306287036956212993001955)
        ·
          refine ⟨76959430555434319489502933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51306287036956212993001955 76959430555434319489502933)
          ·
            refine ⟨1803736653642991863035225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 76959430555434319489502933 1803736653642991863035225)
            ·
              refine ⟨1352802490232243897276419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1803736653642991863035225 1352802490232243897276419)
              ·
                refine ⟨2029203735348365845914629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1352802490232243897276419 2029203735348365845914629)
                ·
                  refine ⟨380475700377818596108993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2029203735348365845914629 380475700377818596108993)
                  ·
                    rfl

theorem cell21_1667191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 4].length) (baseStart_1667191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667191 prefixEnd_1667191 := by exact prefixLift 1667191
  have htrace : WordTrace (prefixWord ++ tailWord_1667191) baseStart_1667191 baseEnd_1667191 := by
    simpa [prefixWord, tailWord_1667191, baseEnd_1667191] using wordTrace_append hprefix tailTrace_1667191
  have hstable : (prefixWord ++ tailWord_1667191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667191).length < 2 ^ (prefixWord ++ tailWord_1667191).sum := by decide
  have hdescent : baseEnd_1667191 < baseStart_1667191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667219 : List Nat := [1, 1, 1, 2, 1, 2, 3, 7, 3]
def baseStart_1667219 : Nat := 118140960795 + 1667219 * 2 ^ 59
def prefixEnd_1667219 : Nat := 4983230072969 + 3 ^ 40 * 1667219 * 2
def baseEnd_1667219 : Nat := 380482090359296769642269

theorem tailTrace_1667219 : CollatzResearch.WordTrace tailWord_1667219 prefixEnd_1667219 380482090359296769642269 := by
  unfold tailWord_1667219
  simp only [CollatzResearch.WordTrace]
  refine ⟨60808472546957776181132711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40538981697971850787421807 60808472546957776181132711)
  ·
    refine ⟨91212708820436664271699067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60808472546957776181132711 91212708820436664271699067)
    ·
      refine ⟨136819063230654996407548601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91212708820436664271699067 136819063230654996407548601)
      ·
        refine ⟨102614297422991247305661451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136819063230654996407548601 102614297422991247305661451)
        ·
          refine ⟨153921446134486870958492177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102614297422991247305661451 153921446134486870958492177)
          ·
            refine ⟨115441084600865153218869133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153921446134486870958492177 115441084600865153218869133)
            ·
              refine ⟨43290406725324432457075925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115441084600865153218869133 43290406725324432457075925)
              ·
                refine ⟨1014618907624791385712717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43290406725324432457075925 1014618907624791385712717)
                ·
                  refine ⟨380482090359296769642269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1014618907624791385712717 380482090359296769642269)
                  ·
                    rfl

theorem cell21_1667219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 3].length) (baseStart_1667219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667219 prefixEnd_1667219 := by exact prefixLift 1667219
  have htrace : WordTrace (prefixWord ++ tailWord_1667219) baseStart_1667219 baseEnd_1667219 := by
    simpa [prefixWord, tailWord_1667219, baseEnd_1667219] using wordTrace_append hprefix tailTrace_1667219
  have hstable : (prefixWord ++ tailWord_1667219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667219).length < 2 ^ (prefixWord ++ tailWord_1667219).sum := by decide
  have hdescent : baseEnd_1667219 < baseStart_1667219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667357 : List Nat := [1, 4, 2, 3, 2, 1, 2, 6]
def baseStart_1667357 : Nat := 118140960795 + 1667357 * 2 ^ 59
def prefixEnd_1667357 : Nat := 4983230072969 + 3 ^ 40 * 1667357 * 2
def baseEnd_1667357 : Nat := 126837861279813065447329

theorem tailTrace_1667357 : CollatzResearch.WordTrace tailWord_1667357 prefixEnd_1667357 126837861279813065447329 := by
  unfold tailWord_1667357
  simp only [CollatzResearch.WordTrace]
  refine ⟨60813505820457825749656325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40542337213638550499770883 60813505820457825749656325)
  ·
    refine ⟨11402532341335842328060561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60813505820457825749656325 11402532341335842328060561)
    ·
      refine ⟨8551899256001881746045421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11402532341335842328060561 8551899256001881746045421)
      ·
        refine ⟨3206962221000705654767033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8551899256001881746045421 3206962221000705654767033)
        ·
          refine ⟨2405221665750529241075275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3206962221000705654767033 2405221665750529241075275)
          ·
            refine ⟨3607832498625793861612913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405221665750529241075275 3607832498625793861612913)
            ·
              refine ⟨2705874373969345396209685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3607832498625793861612913 2705874373969345396209685)
              ·
                refine ⟨126837861279813065447329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2705874373969345396209685 126837861279813065447329)
                ·
                  rfl

theorem cell21_1667357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 6].length) (baseStart_1667357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667357 prefixEnd_1667357 := by exact prefixLift 1667357
  have htrace : WordTrace (prefixWord ++ tailWord_1667357) baseStart_1667357 baseEnd_1667357 := by
    simpa [prefixWord, tailWord_1667357, baseEnd_1667357] using wordTrace_append hprefix tailTrace_1667357
  have hstable : (prefixWord ++ tailWord_1667357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667357).length < 2 ^ (prefixWord ++ tailWord_1667357).sum := by decide
  have hdescent : baseEnd_1667357 < baseStart_1667357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667492 : List Nat := [2, 3, 1, 2, 1, 1, 6, 5]
def baseStart_1667492 : Nat := 118140960795 + 1667492 * 2 ^ 59
def prefixEnd_1667492 : Nat := 4983230072969 + 3 ^ 40 * 1667492 * 2
def baseEnd_1667492 : Nat := 126848130892902987197237

theorem tailTrace_1667492 : CollatzResearch.WordTrace tailWord_1667492 prefixEnd_1667492 126848130892902987197237 := by
  unfold tailWord_1667492
  simp only [CollatzResearch.WordTrace]
  refine ⟨30409214837484371902910365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40545619783312495870547153 30409214837484371902910365)
  ·
    refine ⟨11403455564056639463591387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30409214837484371902910365 11403455564056639463591387)
    ·
      refine ⟨17105183346084959195387081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11403455564056639463591387 17105183346084959195387081)
      ·
        refine ⟨12828887509563719396540311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17105183346084959195387081 12828887509563719396540311)
        ·
          refine ⟨19243331264345579094810467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12828887509563719396540311 19243331264345579094810467)
          ·
            refine ⟨28864996896518368642215701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19243331264345579094810467 28864996896518368642215701)
            ·
              refine ⟨1353046729524298530103861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28864996896518368642215701 1353046729524298530103861)
              ·
                refine ⟨126848130892902987197237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1353046729524298530103861 126848130892902987197237)
                ·
                  rfl

theorem cell21_1667492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 5].length) (baseStart_1667492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667492 prefixEnd_1667492 := by exact prefixLift 1667492
  have htrace : WordTrace (prefixWord ++ tailWord_1667492) baseStart_1667492 baseEnd_1667492 := by
    simpa [prefixWord, tailWord_1667492, baseEnd_1667492] using wordTrace_append hprefix tailTrace_1667492
  have hstable : (prefixWord ++ tailWord_1667492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667492).length < 2 ^ (prefixWord ++ tailWord_1667492).sum := by decide
  have hdescent : baseEnd_1667492 < baseStart_1667492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667509 : List Nat := [1, 3, 3, 2, 4, 1, 7]
def baseStart_1667509 : Nat := 118140960795 + 1667509 * 2 ^ 59
def prefixEnd_1667509 : Nat := 4983230072969 + 3 ^ 40 * 1667509 * 2
def baseEnd_1667509 : Nat := 42283141367813412200927

theorem tailTrace_1667509 : CollatzResearch.WordTrace tailWord_1667509 prefixEnd_1667509 42283141367813412200927 := by
  unfold tailWord_1667509
  simp only [CollatzResearch.WordTrace]
  refine ⟨60819049715907155709189581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40546033143938103806126387 60819049715907155709189581)
  ·
    refine ⟨22807143643465183390946093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60819049715907155709189581 22807143643465183390946093)
    ·
      refine ⟨8552678866299443771604785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22807143643465183390946093 8552678866299443771604785)
      ·
        refine ⟨6414509149724582828703589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8552678866299443771604785 6414509149724582828703589)
        ·
          refine ⟨1202720465573359280381923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6414509149724582828703589 1202720465573359280381923)
          ·
            refine ⟨1804080698360038920572885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202720465573359280381923 1804080698360038920572885)
            ·
              refine ⟨42283141367813412200927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1804080698360038920572885 42283141367813412200927)
              ·
                rfl

theorem cell21_1667509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 7].length) (baseStart_1667509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667509 prefixEnd_1667509 := by exact prefixLift 1667509
  have htrace : WordTrace (prefixWord ++ tailWord_1667509) baseStart_1667509 baseEnd_1667509 := by
    simpa [prefixWord, tailWord_1667509, baseEnd_1667509] using wordTrace_append hprefix tailTrace_1667509
  have hstable : (prefixWord ++ tailWord_1667509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667509).length < 2 ^ (prefixWord ++ tailWord_1667509).sum := by decide
  have hdescent : baseEnd_1667509 < baseStart_1667509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667551 : List Nat := [1, 1, 2, 3, 3, 2, 2, 7]
def baseStart_1667551 : Nat := 118140960795 + 1667551 * 2 ^ 59
def prefixEnd_1667551 : Nat := 4983230072969 + 3 ^ 40 * 1667551 * 2
def baseEnd_1667551 : Nat := 126852619094179323369419

theorem tailTrace_1667551 : CollatzResearch.WordTrace tailWord_1667551 prefixEnd_1667551 126852619094179323369419 := by
  unfold tailWord_1667551
  simp only [CollatzResearch.WordTrace]
  refine ⟨60820581581754996882218507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40547054387836664588145671 60820581581754996882218507)
  ·
    refine ⟨91230872372632495323327761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60820581581754996882218507 91230872372632495323327761)
    ·
      refine ⟨68423154279474371492495821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91230872372632495323327761 68423154279474371492495821)
      ·
        refine ⟨25658682854802889309685933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68423154279474371492495821 25658682854802889309685933)
        ·
          refine ⟨9622006070551083491132225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25658682854802889309685933 9622006070551083491132225)
          ·
            refine ⟨7216504552913312618349169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9622006070551083491132225 7216504552913312618349169)
            ·
              refine ⟨5412378414684984463761877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7216504552913312618349169 5412378414684984463761877)
              ·
                refine ⟨126852619094179323369419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5412378414684984463761877 126852619094179323369419)
                ·
                  rfl

theorem cell21_1667551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 7].length) (baseStart_1667551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667551 prefixEnd_1667551 := by exact prefixLift 1667551
  have htrace : WordTrace (prefixWord ++ tailWord_1667551) baseStart_1667551 baseEnd_1667551 := by
    simpa [prefixWord, tailWord_1667551, baseEnd_1667551] using wordTrace_append hprefix tailTrace_1667551
  have hstable : (prefixWord ++ tailWord_1667551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667551).length < 2 ^ (prefixWord ++ tailWord_1667551).sum := by decide
  have hdescent : baseEnd_1667551 < baseStart_1667551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667630 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_1667630 : Nat := 118140960795 + 1667630 * 2 ^ 59
def prefixEnd_1667630 : Nat := 4983230072969 + 3 ^ 40 * 1667630 * 2
def baseEnd_1667630 : Nat := 380575886158851388291429

theorem tailTrace_1667630 : CollatzResearch.WordTrace tailWord_1667630 prefixEnd_1667630 380575886158851388291429 := by
  unfold tailWord_1667630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7602932868558599171793043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40548975298979195582896229 7602932868558599171793043)
  ·
    refine ⟨11404399302837898757689565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7602932868558599171793043 11404399302837898757689565)
    ·
      refine ⟨4276649738564212034133587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11404399302837898757689565 4276649738564212034133587)
      ·
        refine ⟨6414974607846318051200381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4276649738564212034133587 6414974607846318051200381)
        ·
          refine ⟨2405615477942369269200143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6414974607846318051200381 2405615477942369269200143)
          ·
            refine ⟨3608423216913553903800215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405615477942369269200143 3608423216913553903800215)
            ·
              refine ⟨5412634825370330855700323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3608423216913553903800215 5412634825370330855700323)
              ·
                refine ⟨8118952238055496283550485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5412634825370330855700323 8118952238055496283550485)
                ·
                  refine ⟨380575886158851388291429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8118952238055496283550485 380575886158851388291429)
                  ·
                    rfl

theorem cell21_1667630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_1667630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667630 prefixEnd_1667630 := by exact prefixLift 1667630
  have htrace : WordTrace (prefixWord ++ tailWord_1667630) baseStart_1667630 baseEnd_1667630 := by
    simpa [prefixWord, tailWord_1667630, baseEnd_1667630] using wordTrace_append hprefix tailTrace_1667630
  have hstable : (prefixWord ++ tailWord_1667630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667630).length < 2 ^ (prefixWord ++ tailWord_1667630).sum := by decide
  have hdescent : baseEnd_1667630 < baseStart_1667630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667658 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 5]
def baseStart_1667658 : Nat := 118140960795 + 1667658 * 2 ^ 59
def prefixEnd_1667658 : Nat := 4983230072969 + 3 ^ 40 * 1667658 * 2
def baseEnd_1667658 : Nat := 380582276140329561824705

theorem tailTrace_1667658 : CollatzResearch.WordTrace tailWord_1667658 prefixEnd_1667658 380582276140329561824705 := by
  unfold tailWord_1667658
  simp only [CollatzResearch.WordTrace]
  refine ⟨15206121048091838539090907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40549656128244902770909085 15206121048091838539090907)
  ·
    refine ⟨22809181572137757808636361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15206121048091838539090907 22809181572137757808636361)
    ·
      refine ⟨17106886179103318356477271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22809181572137757808636361 17106886179103318356477271)
      ·
        refine ⟨25660329268654977534715907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17106886179103318356477271 25660329268654977534715907)
        ·
          refine ⟨38490493902982466302073861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25660329268654977534715907 38490493902982466302073861)
          ·
            refine ⟨7216967606809212431638849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38490493902982466302073861 7216967606809212431638849)
            ·
              refine ⟨5412725705106909323729137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7216967606809212431638849 5412725705106909323729137)
              ·
                refine ⟨4059544278830181992796853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5412725705106909323729137 4059544278830181992796853)
                ·
                  refine ⟨380582276140329561824705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4059544278830181992796853 380582276140329561824705)
                  ·
                    rfl

theorem cell21_1667658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_1667658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667658 prefixEnd_1667658 := by exact prefixLift 1667658
  have htrace : WordTrace (prefixWord ++ tailWord_1667658) baseStart_1667658 baseEnd_1667658 := by
    simpa [prefixWord, tailWord_1667658, baseEnd_1667658] using wordTrace_append hprefix tailTrace_1667658
  have hstable : (prefixWord ++ tailWord_1667658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667658).length < 2 ^ (prefixWord ++ tailWord_1667658).sum := by decide
  have hdescent : baseEnd_1667658 < baseStart_1667658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667661 : List Nat := [1, 6, 1, 1, 2, 1, 4, 5]
def baseStart_1667661 : Nat := 118140960795 + 1667661 * 2 ^ 59
def prefixEnd_1667661 : Nat := 4983230072969 + 3 ^ 40 * 1667661 * 2
def baseEnd_1667661 : Nat := 126860986927067407758233

theorem tailTrace_1667661 : CollatzResearch.WordTrace tailWord_1667661 prefixEnd_1667661 126860986927067407758233 := by
  unfold tailWord_1667661
  simp only [CollatzResearch.WordTrace]
  refine ⟨60824593611356485668722837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40549729074237657112481891 60824593611356485668722837)
  ·
    refine ⟨2851152825532335265721383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60824593611356485668722837 2851152825532335265721383)
    ·
      refine ⟨4276729238298502898582075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2851152825532335265721383 4276729238298502898582075)
      ·
        refine ⟨6415093857447754347873113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4276729238298502898582075 6415093857447754347873113)
        ·
          refine ⟨4811320393085815760904835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6415093857447754347873113 4811320393085815760904835)
          ·
            refine ⟨7216980589628723641357253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4811320393085815760904835 7216980589628723641357253)
            ·
              refine ⟨1353183860555385682754485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7216980589628723641357253 1353183860555385682754485)
              ·
                refine ⟨126860986927067407758233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1353183860555385682754485 126860986927067407758233)
                ·
                  rfl

theorem cell21_1667661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 5].length) (baseStart_1667661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667661 prefixEnd_1667661 := by exact prefixLift 1667661
  have htrace : WordTrace (prefixWord ++ tailWord_1667661) baseStart_1667661 baseEnd_1667661 := by
    simpa [prefixWord, tailWord_1667661, baseEnd_1667661] using wordTrace_append hprefix tailTrace_1667661
  have hstable : (prefixWord ++ tailWord_1667661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667661).length < 2 ^ (prefixWord ++ tailWord_1667661).sum := by decide
  have hdescent : baseEnd_1667661 < baseStart_1667661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667672 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 6]
def baseStart_1667672 : Nat := 118140960795 + 1667672 * 2 ^ 59
def prefixEnd_1667672 : Nat := 4983230072969 + 3 ^ 40 * 1667672 * 2
def baseEnd_1667672 : Nat := 380585471131068648591343

theorem tailTrace_1667672 : CollatzResearch.WordTrace tailWord_1667672 prefixEnd_1667672 380585471131068648591343 := by
  unfold tailWord_1667672
  simp only [CollatzResearch.WordTrace]
  refine ⟨30412497407158317273686635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40549996542877756364915513 30412497407158317273686635)
  ·
    refine ⟨45618746110737475910529953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30412497407158317273686635 45618746110737475910529953)
    ·
      refine ⟨34214059583053106932897465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45618746110737475910529953 34214059583053106932897465)
      ·
        refine ⟨25660544687289830199673099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34214059583053106932897465 25660544687289830199673099)
        ·
          refine ⟨38490817030934745299509649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25660544687289830199673099 38490817030934745299509649)
          ·
            refine ⟨28868112773201058974632237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38490817030934745299509649 28868112773201058974632237)
            ·
              refine ⟨10825542289950397115487089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28868112773201058974632237 10825542289950397115487089)
              ·
                refine ⟨8119156717462797836615317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10825542289950397115487089 8119156717462797836615317)
                ·
                  refine ⟨380585471131068648591343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8119156717462797836615317 380585471131068648591343)
                  ·
                    rfl

theorem cell21_1667672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_1667672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667672 prefixEnd_1667672 := by exact prefixLift 1667672
  have htrace : WordTrace (prefixWord ++ tailWord_1667672) baseStart_1667672 baseEnd_1667672 := by
    simpa [prefixWord, tailWord_1667672, baseEnd_1667672] using wordTrace_append hprefix tailTrace_1667672
  have hstable : (prefixWord ++ tailWord_1667672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667672).length < 2 ^ (prefixWord ++ tailWord_1667672).sum := by decide
  have hdescent : baseEnd_1667672 < baseStart_1667672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667754 : List Nat := [3, 1, 5, 2, 1, 2, 1, 6]
def baseStart_1667754 : Nat := 118140960795 + 1667754 * 2 ^ 59
def prefixEnd_1667754 : Nat := 4983230072969 + 3 ^ 40 * 1667754 * 2
def baseEnd_1667754 : Nat := 126868061549418242741503

theorem tailTrace_1667754 : CollatzResearch.WordTrace tailWord_1667754 prefixEnd_1667754 126868061549418242741503 := by
  unfold tailWord_1667754
  simp only [CollatzResearch.WordTrace]
  refine ⟨15206996400004890637964579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40551990400013041701238877 15206996400004890637964579)
  ·
    refine ⟨22810494600007335956946869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15206996400004890637964579 22810494600007335956946869)
    ·
      refine ⟨2138483868750687745963769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22810494600007335956946869 2138483868750687745963769)
      ·
        refine ⟨1603862901563015809472827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2138483868750687745963769 1603862901563015809472827)
        ·
          refine ⟨2405794352344523714209241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1603862901563015809472827 2405794352344523714209241)
          ·
            refine ⟨1804345764258392785656931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2405794352344523714209241 1804345764258392785656931)
            ·
              refine ⟨2706518646387589178485397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804345764258392785656931 2706518646387589178485397)
              ·
                refine ⟨126868061549418242741503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2706518646387589178485397 126868061549418242741503)
                ·
                  rfl

theorem cell21_1667754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_1667754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667754 prefixEnd_1667754 := by exact prefixLift 1667754
  have htrace : WordTrace (prefixWord ++ tailWord_1667754) baseStart_1667754 baseEnd_1667754 := by
    simpa [prefixWord, tailWord_1667754, baseEnd_1667754] using wordTrace_append hprefix tailTrace_1667754
  have hstable : (prefixWord ++ tailWord_1667754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667754).length < 2 ^ (prefixWord ++ tailWord_1667754).sum := by decide
  have hdescent : baseEnd_1667754 < baseStart_1667754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667793 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 7]
def baseStart_1667793 : Nat := 118140960795 + 1667793 * 2 ^ 59
def prefixEnd_1667793 : Nat := 4983230072969 + 3 ^ 40 * 1667793 * 2
def baseEnd_1667793 : Nat := 380613084979599327074429

theorem tailTrace_1667793 : CollatzResearch.WordTrace tailWord_1667793 prefixEnd_1667793 380613084979599327074429 := by
  unfold tailWord_1667793
  simp only [CollatzResearch.WordTrace]
  refine ⟨60829408046878272212528033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40552938697918848141685355 60829408046878272212528033)
  ·
    refine ⟨45622056035158704159396025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60829408046878272212528033 45622056035158704159396025)
    ·
      refine ⟨34216542026369028119547019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45622056035158704159396025 34216542026369028119547019)
      ·
        refine ⟨51324813039553542179320529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34216542026369028119547019 51324813039553542179320529)
        ·
          refine ⟨38493609779665156634490397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51324813039553542179320529 38493609779665156634490397)
          ·
            refine ⟨14435103667374433737933899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38493609779665156634490397 14435103667374433737933899)
            ·
              refine ⟨21652655501061650606900849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14435103667374433737933899 21652655501061650606900849)
              ·
                refine ⟨16239491625796237955175637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21652655501061650606900849 16239491625796237955175637)
                ·
                  refine ⟨380613084979599327074429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16239491625796237955175637 380613084979599327074429)
                  ·
                    rfl

theorem cell21_1667793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_1667793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667793 prefixEnd_1667793 := by exact prefixLift 1667793
  have htrace : WordTrace (prefixWord ++ tailWord_1667793) baseStart_1667793 baseEnd_1667793 := by
    simpa [prefixWord, tailWord_1667793, baseEnd_1667793] using wordTrace_append hprefix tailTrace_1667793
  have hstable : (prefixWord ++ tailWord_1667793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667793).length < 2 ^ (prefixWord ++ tailWord_1667793).sum := by decide
  have hdescent : baseEnd_1667793 < baseStart_1667793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667796 : List Nat := [2, 4, 1, 3, 2, 1, 8]
def baseStart_1667796 : Nat := 118140960795 + 1667796 * 2 ^ 59
def prefixEnd_1667796 : Nat := 4983230072969 + 3 ^ 40 * 1667796 * 2
def baseEnd_1667796 : Nat := 42290418846719109836047

theorem tailTrace_1667796 : CollatzResearch.WordTrace tailWord_1667796 prefixEnd_1667796 42290418846719109836047 := by
  unfold tailWord_1667796
  simp only [CollatzResearch.WordTrace]
  refine ⟨30414758732933701862443621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40553011643911602483258161 30414758732933701862443621)
  ·
    refine ⟨5702767262425069099208179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30414758732933701862443621 5702767262425069099208179)
    ·
      refine ⟨8554150893637603648812269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5702767262425069099208179 8554150893637603648812269)
      ·
        refine ⟨3207806585114101368304601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8554150893637603648812269 3207806585114101368304601)
        ·
          refine ⟨2405854938835576026228451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3207806585114101368304601 2405854938835576026228451)
          ·
            refine ⟨3608782408253364039342677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405854938835576026228451 3608782408253364039342677)
            ·
              refine ⟨42290418846719109836047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3608782408253364039342677 42290418846719109836047)
              ·
                rfl

theorem cell21_1667796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 8].length) (baseStart_1667796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1667796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1667796 prefixEnd_1667796 := by exact prefixLift 1667796
  have htrace : WordTrace (prefixWord ++ tailWord_1667796) baseStart_1667796 baseEnd_1667796 := by
    simpa [prefixWord, tailWord_1667796, baseEnd_1667796] using wordTrace_append hprefix tailTrace_1667796
  have hstable : (prefixWord ++ tailWord_1667796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667796).length < 2 ^ (prefixWord ++ tailWord_1667796).sum := by decide
  have hdescent : baseEnd_1667796 < baseStart_1667796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668086 : List Nat := [5, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_1668086 : Nat := 118140960795 + 1668086 * 2 ^ 59
def prefixEnd_1668086 : Nat := 4983230072969 + 3 ^ 40 * 1668086 * 2
def baseEnd_1668086 : Nat := 380679951571495928690497

theorem tailTrace_1668086 : CollatzResearch.WordTrace tailWord_1668086 prefixEnd_1668086 380679951571495928690497 := by
  unfold tailWord_1668086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3802505914676048953309007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40560063089877855501962741 3802505914676048953309007)
  ·
    refine ⟨5703758872014073429963511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3802505914676048953309007 5703758872014073429963511)
    ·
      refine ⟨8555638308021110144945267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5703758872014073429963511 8555638308021110144945267)
      ·
        refine ⟨12833457462031665217417901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8555638308021110144945267 12833457462031665217417901)
        ·
          refine ⟨4812546548261874456531713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12833457462031665217417901 4812546548261874456531713)
          ·
            refine ⟨3609409911196405842398785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4812546548261874456531713 3609409911196405842398785)
            ·
              refine ⟨2707057433397304381799089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3609409911196405842398785 2707057433397304381799089)
              ·
                refine ⟨2030293075047978286349317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2707057433397304381799089 2030293075047978286349317)
                ·
                  refine ⟨380679951571495928690497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2030293075047978286349317 380679951571495928690497)
                  ·
                    rfl

theorem cell21_1668086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_1668086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668086 prefixEnd_1668086 := by exact prefixLift 1668086
  have htrace : WordTrace (prefixWord ++ tailWord_1668086) baseStart_1668086 baseEnd_1668086 := by
    simpa [prefixWord, tailWord_1668086, baseEnd_1668086] using wordTrace_append hprefix tailTrace_1668086
  have hstable : (prefixWord ++ tailWord_1668086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668086).length < 2 ^ (prefixWord ++ tailWord_1668086).sum := by decide
  have hdescent : baseEnd_1668086 < baseStart_1668086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668131 : List Nat := [1, 1, 1, 4, 3, 3, 2, 3, 3]
def baseStart_1668131 : Nat := 118140960795 + 1668131 * 2 ^ 59
def prefixEnd_1668131 : Nat := 4983230072969 + 3 ^ 40 * 1668131 * 2
def baseEnd_1668131 : Nat := 380690221184585850440405

theorem tailTrace_1668131 : CollatzResearch.WordTrace tailWord_1668131 prefixEnd_1668131 380690221184585850440405 := by
  unfold tailWord_1668131
  simp only [CollatzResearch.WordTrace]
  refine ⟨60841735919653755938332247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40561157279769170625554831 60841735919653755938332247)
  ·
    refine ⟨91262603879480633907498371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60841735919653755938332247 91262603879480633907498371)
    ·
      refine ⟨136893905819220950861247557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91262603879480633907498371 136893905819220950861247557)
      ·
        refine ⟨25667607341103928286483917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136893905819220950861247557 25667607341103928286483917)
        ·
          refine ⟨9625352752913973107431469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25667607341103928286483917 9625352752913973107431469)
          ·
            refine ⟨3609507282342739915286801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9625352752913973107431469 3609507282342739915286801)
            ·
              refine ⟨2707130461757054936465101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3609507282342739915286801 2707130461757054936465101)
              ·
                refine ⟨1015173923158895601174413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2707130461757054936465101 1015173923158895601174413)
                ·
                  refine ⟨380690221184585850440405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015173923158895601174413 380690221184585850440405)
                  ·
                    rfl

theorem cell21_1668131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 3].length) (baseStart_1668131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668131 prefixEnd_1668131 := by exact prefixLift 1668131
  have htrace : WordTrace (prefixWord ++ tailWord_1668131) baseStart_1668131 baseEnd_1668131 := by
    simpa [prefixWord, tailWord_1668131, baseEnd_1668131] using wordTrace_append hprefix tailTrace_1668131
  have hstable : (prefixWord ++ tailWord_1668131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668131).length < 2 ^ (prefixWord ++ tailWord_1668131).sum := by decide
  have hdescent : baseEnd_1668131 < baseStart_1668131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668148 : List Nat := [2, 5, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1668148 : Nat := 118140960795 + 1668148 * 2 ^ 59
def prefixEnd_1668148 : Nat := 4983230072969 + 3 ^ 40 * 1668148 * 2
def baseEnd_1668148 : Nat := 380694100816197598657037

theorem tailTrace_1668148 : CollatzResearch.WordTrace tailWord_1668148 prefixEnd_1668148 380694100816197598657037 := by
  unfold tailWord_1668148
  simp only [CollatzResearch.WordTrace]
  refine ⟨30421177980296083920850549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40561570640394778561134065 30421177980296083920850549)
  ·
    refine ⟨2851985435652757867579739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30421177980296083920850549 2851985435652757867579739)
    ·
      refine ⟨4277978153479136801369609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2851985435652757867579739 4277978153479136801369609)
      ·
        refine ⟨3208483615109352601027207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4277978153479136801369609 3208483615109352601027207)
        ·
          refine ⟨4812725422664028901540811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3208483615109352601027207 4812725422664028901540811)
          ·
            refine ⟨7219088133996043352311217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4812725422664028901540811 7219088133996043352311217)
            ·
              refine ⟨5414316100497032514233413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7219088133996043352311217 5414316100497032514233413)
              ·
                refine ⟨1015184268843193596418765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5414316100497032514233413 1015184268843193596418765)
                ·
                  refine ⟨380694100816197598657037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015184268843193596418765 380694100816197598657037)
                  ·
                    rfl

theorem cell21_1668148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1668148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668148 prefixEnd_1668148 := by exact prefixLift 1668148
  have htrace : WordTrace (prefixWord ++ tailWord_1668148) baseStart_1668148 baseEnd_1668148 := by
    simpa [prefixWord, tailWord_1668148, baseEnd_1668148] using wordTrace_append hprefix tailTrace_1668148
  have hstable : (prefixWord ++ tailWord_1668148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668148).length < 2 ^ (prefixWord ++ tailWord_1668148).sum := by decide
  have hdescent : baseEnd_1668148 < baseStart_1668148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668182 : List Nat := [5, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1668182 : Nat := 118140960795 + 1668182 * 2 ^ 59
def prefixEnd_1668182 : Nat := 4983230072969 + 3 ^ 40 * 1668182 * 2
def baseEnd_1668182 : Nat := 380701860079421095090301

theorem tailTrace_1668182 : CollatzResearch.WordTrace tailWord_1668182 prefixEnd_1668182 380701860079421095090301 := by
  unfold tailWord_1668182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3802724752654311978027425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40562397361645994432292533 3802724752654311978027425)
  ·
    refine ⟨2852043564490733983520569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3802724752654311978027425 2852043564490733983520569)
    ·
      refine ⟨2139032673368050487640427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2852043564490733983520569 2139032673368050487640427)
      ·
        refine ⟨3208549010052075731460641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2139032673368050487640427 3208549010052075731460641)
        ·
          refine ⟨2406411757539056798595481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3208549010052075731460641 2406411757539056798595481)
          ·
            refine ⟨1804808818154292598946611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2406411757539056798595481 1804808818154292598946611)
            ·
              refine ⟨2707213227231438898419917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804808818154292598946611 2707213227231438898419917)
              ·
                refine ⟨1015204960211789586907469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2707213227231438898419917 1015204960211789586907469)
                ·
                  refine ⟨380701860079421095090301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015204960211789586907469 380701860079421095090301)
                  ·
                    rfl

theorem cell21_1668182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1668182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668182 prefixEnd_1668182 := by exact prefixLift 1668182
  have htrace : WordTrace (prefixWord ++ tailWord_1668182) baseStart_1668182 baseEnd_1668182 := by
    simpa [prefixWord, tailWord_1668182, baseEnd_1668182] using wordTrace_append hprefix tailTrace_1668182
  have hstable : (prefixWord ++ tailWord_1668182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668182).length < 2 ^ (prefixWord ++ tailWord_1668182).sum := by decide
  have hdescent : baseEnd_1668182 < baseStart_1668182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668204 : List Nat := [2, 2, 1, 1, 3, 2, 2, 4, 4]
def baseStart_1668204 : Nat := 118140960795 + 1668204 * 2 ^ 59
def prefixEnd_1668204 : Nat := 4983230072969 + 3 ^ 40 * 1668204 * 2
def baseEnd_1668204 : Nat := 380706880779153945723589

theorem tailTrace_1668204 : CollatzResearch.WordTrace tailWord_1668204 prefixEnd_1668204 380706880779153945723589 := by
  unfold tailWord_1668204
  simp only [CollatzResearch.WordTrace]
  refine ⟨30422199224194644702869833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40562932298926192937159777 30422199224194644702869833)
  ·
    refine ⟨22816649418145983527152375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30422199224194644702869833 22816649418145983527152375)
    ·
      refine ⟨34224974127218975290728563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22816649418145983527152375 34224974127218975290728563)
      ·
        refine ⟨51337461190828462936092845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34224974127218975290728563 51337461190828462936092845)
        ·
          refine ⟨19251547946560673601034817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51337461190828462936092845 19251547946560673601034817)
          ·
            refine ⟨14438660959920505200776113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19251547946560673601034817 14438660959920505200776113)
            ·
              refine ⟨10828995719940378900582085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14438660959920505200776113 10828995719940378900582085)
              ·
                refine ⟨2030436697488821043859141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10828995719940378900582085 2030436697488821043859141)
                ·
                  refine ⟨380706880779153945723589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2030436697488821043859141 380706880779153945723589)
                  ·
                    rfl

theorem cell21_1668204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_1668204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668204 prefixEnd_1668204 := by exact prefixLift 1668204
  have htrace : WordTrace (prefixWord ++ tailWord_1668204) baseStart_1668204 baseEnd_1668204 := by
    simpa [prefixWord, tailWord_1668204, baseEnd_1668204] using wordTrace_append hprefix tailTrace_1668204
  have hstable : (prefixWord ++ tailWord_1668204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668204).length < 2 ^ (prefixWord ++ tailWord_1668204).sum := by decide
  have hdescent : baseEnd_1668204 < baseStart_1668204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668207 : List Nat := [1, 1, 2, 1, 3, 3, 5, 2, 3]
def baseStart_1668207 : Nat := 118140960795 + 1668207 * 2 ^ 59
def prefixEnd_1668207 : Nat := 4983230072969 + 3 ^ 40 * 1668207 * 2
def baseEnd_1668207 : Nat := 380707565420026607173583

theorem tailTrace_1668207 : CollatzResearch.WordTrace tailWord_1668207 prefixEnd_1668207 380707565420026607173583 := by
  unfold tailWord_1668207
  simp only [CollatzResearch.WordTrace]
  refine ⟨60844507867378420918098875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40563005244918947278732583 60844507867378420918098875)
  ·
    refine ⟨91266761801067631377148313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60844507867378420918098875 91266761801067631377148313)
    ·
      refine ⟨68450071350800723532861235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91266761801067631377148313 68450071350800723532861235)
      ·
        refine ⟨102675107026201085299291853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68450071350800723532861235 102675107026201085299291853)
        ·
          refine ⟨38503165134825406987234445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102675107026201085299291853 38503165134825406987234445)
          ·
            refine ⟨14438686925559527620212917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38503165134825406987234445 14438686925559527620212917)
            ·
              refine ⟨1353626899271205714394961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14438686925559527620212917 1353626899271205714394961)
              ·
                refine ⟨1015220174453404285796221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1353626899271205714394961 1015220174453404285796221)
                ·
                  refine ⟨380707565420026607173583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015220174453404285796221 380707565420026607173583)
                  ·
                    rfl

theorem cell21_1668207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 3].length) (baseStart_1668207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668207 prefixEnd_1668207 := by exact prefixLift 1668207
  have htrace : WordTrace (prefixWord ++ tailWord_1668207) baseStart_1668207 baseEnd_1668207 := by
    simpa [prefixWord, tailWord_1668207, baseEnd_1668207] using wordTrace_append hprefix tailTrace_1668207
  have hstable : (prefixWord ++ tailWord_1668207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668207).length < 2 ^ (prefixWord ++ tailWord_1668207).sum := by decide
  have hdescent : baseEnd_1668207 < baseStart_1668207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668258 : List Nat := [3, 3, 1, 3, 3, 1, 2, 2, 3]
def baseStart_1668258 : Nat := 118140960795 + 1668258 * 2 ^ 59
def prefixEnd_1668258 : Nat := 4983230072969 + 3 ^ 40 * 1668258 * 2
def baseEnd_1668258 : Nat := 380719204314861851823479

theorem tailTrace_1668258 : CollatzResearch.WordTrace tailWord_1668258 prefixEnd_1668258 380719204314861851823479 := by
  unfold tailWord_1668258
  simp only [CollatzResearch.WordTrace]
  refine ⟨15211591997548414157051357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40564245326795771085470285 15211591997548414157051357)
  ·
    refine ⟨5704346999080655308894259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15211591997548414157051357 5704346999080655308894259)
    ·
      refine ⟨8556520498620982963341389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5704346999080655308894259 8556520498620982963341389)
      ·
        refine ⟨3208695186982868611253021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8556520498620982963341389 3208695186982868611253021)
        ·
          refine ⟨1203260695118575729219883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3208695186982868611253021 1203260695118575729219883)
          ·
            refine ⟨1804891042677863593829825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203260695118575729219883 1804891042677863593829825)
            ·
              refine ⟨1353668282008397695372369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1804891042677863593829825 1353668282008397695372369)
              ·
                refine ⟨1015251211506298271529277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1353668282008397695372369 1015251211506298271529277)
                ·
                  refine ⟨380719204314861851823479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015251211506298271529277 380719204314861851823479)
                  ·
                    rfl

theorem cell21_1668258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_1668258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668258 prefixEnd_1668258 := by exact prefixLift 1668258
  have htrace : WordTrace (prefixWord ++ tailWord_1668258) baseStart_1668258 baseEnd_1668258 := by
    simpa [prefixWord, tailWord_1668258, baseEnd_1668258] using wordTrace_append hprefix tailTrace_1668258
  have hstable : (prefixWord ++ tailWord_1668258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668258).length < 2 ^ (prefixWord ++ tailWord_1668258).sum := by decide
  have hdescent : baseEnd_1668258 < baseStart_1668258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668269 : List Nat := [1, 5, 2, 1, 4, 1, 1, 6]
def baseStart_1668269 : Nat := 118140960795 + 1668269 * 2 ^ 59
def prefixEnd_1668269 : Nat := 4983230072969 + 3 ^ 40 * 1668269 * 2
def baseEnd_1668269 : Nat := 126907238221576092380041

theorem tailTrace_1668269 : CollatzResearch.WordTrace tailWord_1668269 prefixEnd_1668269 126907238221576092380041 := by
  unfold tailWord_1668269
  simp only [CollatzResearch.WordTrace]
  refine ⟨60846769193153805506855861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40564512795435870337903907 60846769193153805506855861)
  ·
    refine ⟨5704384611858169266267737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60846769193153805506855861 5704384611858169266267737)
    ·
      refine ⟨4278288458893626949700803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5704384611858169266267737 4278288458893626949700803)
      ·
        refine ⟨6417432688340440424551205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4278288458893626949700803 6417432688340440424551205)
        ·
          refine ⟨1203268629063832579603351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6417432688340440424551205 1203268629063832579603351)
          ·
            refine ⟨1804902943595748869405027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203268629063832579603351 1804902943595748869405027)
            ·
              refine ⟨2707354415393623304107541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804902943595748869405027 2707354415393623304107541)
              ·
                refine ⟨126907238221576092380041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2707354415393623304107541 126907238221576092380041)
                ·
                  rfl

theorem cell21_1668269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 6].length) (baseStart_1668269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668269 prefixEnd_1668269 := by exact prefixLift 1668269
  have htrace : WordTrace (prefixWord ++ tailWord_1668269) baseStart_1668269 baseEnd_1668269 := by
    simpa [prefixWord, tailWord_1668269, baseEnd_1668269] using wordTrace_append hprefix tailTrace_1668269
  have hstable : (prefixWord ++ tailWord_1668269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668269).length < 2 ^ (prefixWord ++ tailWord_1668269).sum := by decide
  have hdescent : baseEnd_1668269 < baseStart_1668269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668356 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 6]
def baseStart_1668356 : Nat := 118140960795 + 1668356 * 2 ^ 59
def prefixEnd_1668356 : Nat := 4983230072969 + 3 ^ 40 * 1668356 * 2
def baseEnd_1668356 : Nat := 380741569250035459189945

theorem tailTrace_1668356 : CollatzResearch.WordTrace tailWord_1668356 prefixEnd_1668356 380741569250035459189945 := by
  unfold tailWord_1668356
  simp only [CollatzResearch.WordTrace]
  refine ⟨30424971171919309682636461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40566628229225746243515281 30424971171919309682636461)
  ·
    refine ⟨11409364189469741130988673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30424971171919309682636461 11409364189469741130988673)
    ·
      refine ⟨8557023142102305848241505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11409364189469741130988673 8557023142102305848241505)
      ·
        refine ⟨6417767356576729386181129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8557023142102305848241505 6417767356576729386181129)
        ·
          refine ⟨4813325517432547039635847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6417767356576729386181129 4813325517432547039635847)
          ·
            refine ⟨7219988276148820559453771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4813325517432547039635847 7219988276148820559453771)
            ·
              refine ⟨10829982414223230839180657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7219988276148820559453771 10829982414223230839180657)
              ·
                refine ⟨8122486810667423129385493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10829982414223230839180657 8122486810667423129385493)
                ·
                  refine ⟨380741569250035459189945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8122486810667423129385493 380741569250035459189945)
                  ·
                    rfl

theorem cell21_1668356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_1668356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668356 prefixEnd_1668356 := by exact prefixLift 1668356
  have htrace : WordTrace (prefixWord ++ tailWord_1668356) baseStart_1668356 baseEnd_1668356 := by
    simpa [prefixWord, tailWord_1668356, baseEnd_1668356] using wordTrace_append hprefix tailTrace_1668356
  have hstable : (prefixWord ++ tailWord_1668356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668356).length < 2 ^ (prefixWord ++ tailWord_1668356).sum := by decide
  have hdescent : baseEnd_1668356 < baseStart_1668356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668432 : List Nat := [2, 1, 1, 1, 1, 5, 4, 2, 4]
def baseStart_1668432 : Nat := 118140960795 + 1668432 * 2 ^ 59
def prefixEnd_1668432 : Nat := 4983230072969 + 3 ^ 40 * 1668432 * 2
def baseEnd_1668432 : Nat := 380758913485476215923123

theorem tailTrace_1668432 : CollatzResearch.WordTrace tailWord_1668432 prefixEnd_1668432 380758913485476215923123 := by
  unfold tailWord_1668432
  simp only [CollatzResearch.WordTrace]
  refine ⟨30426357145781642172519775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40568476194375522896693033 30426357145781642172519775)
  ·
    refine ⟨45639535718672463258779663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30426357145781642172519775 45639535718672463258779663)
    ·
      refine ⟨68459303578008694888169495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45639535718672463258779663 68459303578008694888169495)
      ·
        refine ⟨102688955367013042332254243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68459303578008694888169495 102688955367013042332254243)
        ·
          refine ⟨154033433050519563498381365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102688955367013042332254243 154033433050519563498381365)
          ·
            refine ⟨14440634348486209077973253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154033433050519563498381365 14440634348486209077973253)
            ·
              refine ⟨2707618940341164202119985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14440634348486209077973253 2707618940341164202119985)
              ·
                refine ⟨2030714205255873151589989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2707618940341164202119985 2030714205255873151589989)
                ·
                  refine ⟨380758913485476215923123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2030714205255873151589989 380758913485476215923123)
                  ·
                    rfl

theorem cell21_1668432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_1668432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668432 prefixEnd_1668432 := by exact prefixLift 1668432
  have htrace : WordTrace (prefixWord ++ tailWord_1668432) baseStart_1668432 baseEnd_1668432 := by
    simpa [prefixWord, tailWord_1668432, baseEnd_1668432] using wordTrace_append hprefix tailTrace_1668432
  have hstable : (prefixWord ++ tailWord_1668432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668432).length < 2 ^ (prefixWord ++ tailWord_1668432).sum := by decide
  have hdescent : baseEnd_1668432 < baseStart_1668432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668491 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 6]
def baseStart_1668491 : Nat := 118140960795 + 1668491 * 2 ^ 59
def prefixEnd_1668491 : Nat := 4983230072969 + 3 ^ 40 * 1668491 * 2
def baseEnd_1668491 : Nat := 380772378089305224439669

theorem tailTrace_1668491 : CollatzResearch.WordTrace tailWord_1668491 prefixEnd_1668491 380772378089305224439669 := by
  unfold tailWord_1668491
  simp only [CollatzResearch.WordTrace]
  refine ⟨60854866198349537421437327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40569910798899691614291551 60854866198349537421437327)
  ·
    refine ⟨91282299297524306132155991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60854866198349537421437327 91282299297524306132155991)
    ·
      refine ⟨136923448946286459198233987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91282299297524306132155991 136923448946286459198233987)
      ·
        refine ⟨205385173419429688797350981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136923448946286459198233987 205385173419429688797350981)
        ·
          refine ⟨38509720016143066649503309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205385173419429688797350981 38509720016143066649503309)
          ·
            refine ⟨14441145006053649993563741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38509720016143066649503309 14441145006053649993563741)
            ·
              refine ⟨5415429377270118747586403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14441145006053649993563741 5415429377270118747586403)
              ·
                refine ⟨8123144065905178121379605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5415429377270118747586403 8123144065905178121379605)
                ·
                  refine ⟨380772378089305224439669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8123144065905178121379605 380772378089305224439669)
                  ·
                    rfl

theorem cell21_1668491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 6].length) (baseStart_1668491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668491 prefixEnd_1668491 := by exact prefixLift 1668491
  have htrace : WordTrace (prefixWord ++ tailWord_1668491) baseStart_1668491 baseEnd_1668491 := by
    simpa [prefixWord, tailWord_1668491, baseEnd_1668491] using wordTrace_append hprefix tailTrace_1668491
  have hstable : (prefixWord ++ tailWord_1668491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668491).length < 2 ^ (prefixWord ++ tailWord_1668491).sum := by decide
  have hdescent : baseEnd_1668491 < baseStart_1668491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668536 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 7]
def baseStart_1668536 : Nat := 118140960795 + 1668536 * 2 ^ 59
def prefixEnd_1668536 : Nat := 4983230072969 + 3 ^ 40 * 1668536 * 2
def baseEnd_1668536 : Nat := 380782647702395146189577

theorem tailTrace_1668536 : CollatzResearch.WordTrace tailWord_1668536 prefixEnd_1668536 380782647702395146189577 := by
  unfold tailWord_1668536
  simp only [CollatzResearch.WordTrace]
  refine ⟨30428253741593255053412731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40571004988791006737883641 30428253741593255053412731)
  ·
    refine ⟨45642380612389882580119097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30428253741593255053412731 45642380612389882580119097)
    ·
      refine ⟨34231785459292411935089323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45642380612389882580119097 34231785459292411935089323)
      ·
        refine ⟨51347678188938617902633985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34231785459292411935089323 51347678188938617902633985)
        ·
          refine ⟨38510758641703963426975489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51347678188938617902633985 38510758641703963426975489)
          ·
            refine ⟨28883068981277972570231617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38510758641703963426975489 28883068981277972570231617)
            ·
              refine ⟨21662301735958479427673713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28883068981277972570231617 21662301735958479427673713)
              ·
                refine ⟨16246726301968859570755285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21662301735958479427673713 16246726301968859570755285)
                ·
                  refine ⟨380782647702395146189577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16246726301968859570755285 380782647702395146189577)
                  ·
                    rfl

theorem cell21_1668536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_1668536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668536 prefixEnd_1668536 := by exact prefixLift 1668536
  have htrace : WordTrace (prefixWord ++ tailWord_1668536) baseStart_1668536 baseEnd_1668536 := by
    simpa [prefixWord, tailWord_1668536, baseEnd_1668536] using wordTrace_append hprefix tailTrace_1668536
  have hstable : (prefixWord ++ tailWord_1668536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668536).length < 2 ^ (prefixWord ++ tailWord_1668536).sum := by decide
  have hdescent : baseEnd_1668536 < baseStart_1668536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668598 : List Nat := [5, 1, 1, 1, 2, 11]
def baseStart_1668598 : Nat := 118140960795 + 1668598 * 2 ^ 59
def prefixEnd_1668598 : Nat := 4983230072969 + 3 ^ 40 * 1668598 * 2
def baseEnd_1668598 : Nat := 14103585072114696894671

theorem tailTrace_1668598 : CollatzResearch.WordTrace tailWord_1668598 prefixEnd_1668598 14103585072114696894671 := by
  unfold tailWord_1668598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3803673050560118418473903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40572512539307929797054965 3803673050560118418473903)
  ·
    refine ⟨5705509575840177627710855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3803673050560118418473903 5705509575840177627710855)
    ·
      refine ⟨8558264363760266441566283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5705509575840177627710855 8558264363760266441566283)
      ·
        refine ⟨12837396545640399662349425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8558264363760266441566283 12837396545640399662349425)
        ·
          refine ⟨9628047409230299746762069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12837396545640399662349425 9628047409230299746762069)
          ·
            refine ⟨14103585072114696894671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9628047409230299746762069 14103585072114696894671)
            ·
              rfl

theorem cell21_1668598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 11].length) (baseStart_1668598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668598 prefixEnd_1668598 := by exact prefixLift 1668598
  have htrace : WordTrace (prefixWord ++ tailWord_1668598) baseStart_1668598 baseEnd_1668598 := by
    simpa [prefixWord, tailWord_1668598, baseEnd_1668598] using wordTrace_append hprefix tailTrace_1668598
  have hstable : (prefixWord ++ tailWord_1668598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668598).length < 2 ^ (prefixWord ++ tailWord_1668598).sum := by decide
  have hdescent : baseEnd_1668598 < baseStart_1668598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668615 : List Nat := [1, 1, 4, 3, 2, 3, 1, 6]
def baseStart_1668615 : Nat := 118140960795 + 1668615 * 2 ^ 59
def prefixEnd_1668615 : Nat := 4983230072969 + 3 ^ 40 * 1668615 * 2
def baseEnd_1668615 : Nat := 126933558859569521457583

theorem tailTrace_1668615 : CollatzResearch.WordTrace tailWord_1668615 prefixEnd_1668615 126933558859569521457583 := by
  unfold tailWord_1668615
  simp only [CollatzResearch.WordTrace]
  refine ⟨60859388849900306598951299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40572925899933537732634199 60859388849900306598951299)
  ·
    refine ⟨91289083274850459898426949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60859388849900306598951299 91289083274850459898426949)
    ·
      refine ⟨17116703114034461230955053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91289083274850459898426949 17116703114034461230955053)
      ·
        refine ⟨6418763667762922961608145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17116703114034461230955053 6418763667762922961608145)
        ·
          refine ⟨4814072750822192221206109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6418763667762922961608145 4814072750822192221206109)
          ·
            refine ⟨1805277281558322082952291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4814072750822192221206109 1805277281558322082952291)
            ·
              refine ⟨2707915922337483124428437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1805277281558322082952291 2707915922337483124428437)
              ·
                refine ⟨126933558859569521457583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2707915922337483124428437 126933558859569521457583)
                ·
                  rfl

theorem cell21_1668615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 6].length) (baseStart_1668615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668615 prefixEnd_1668615 := by exact prefixLift 1668615
  have htrace : WordTrace (prefixWord ++ tailWord_1668615) baseStart_1668615 baseEnd_1668615 := by
    simpa [prefixWord, tailWord_1668615, baseEnd_1668615] using wordTrace_append hprefix tailTrace_1668615
  have hstable : (prefixWord ++ tailWord_1668615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668615).length < 2 ^ (prefixWord ++ tailWord_1668615).sum := by decide
  have hdescent : baseEnd_1668615 < baseStart_1668615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668629 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 5]
def baseStart_1668629 : Nat := 118140960795 + 1668629 * 2 ^ 59
def prefixEnd_1668629 : Nat := 4983230072969 + 3 ^ 40 * 1668629 * 2
def baseEnd_1668629 : Nat := 380803871569447651139387

theorem tailTrace_1668629 : CollatzResearch.WordTrace tailWord_1668629 prefixEnd_1668629 380803871569447651139387 := by
  unfold tailWord_1668629
  simp only [CollatzResearch.WordTrace]
  refine ⟨60859899471849586989960941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40573266314566391326640627 60859899471849586989960941)
  ·
    refine ⟨22822462301943595121235353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60859899471849586989960941 22822462301943595121235353)
    ·
      refine ⟨17116846726457696340926515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22822462301943595121235353 17116846726457696340926515)
      ·
        refine ⟨25675270089686544511389773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17116846726457696340926515 25675270089686544511389773)
        ·
          refine ⟨9628226283632454191771165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25675270089686544511389773 9628226283632454191771165)
          ·
            refine ⟨3610584856362170321914187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9628226283632454191771165 3610584856362170321914187)
            ·
              refine ⟨5415877284543255482871281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3610584856362170321914187 5415877284543255482871281)
              ·
                refine ⟨4061907963407441612153461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5415877284543255482871281 4061907963407441612153461)
                ·
                  refine ⟨380803871569447651139387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4061907963407441612153461 380803871569447651139387)
                  ·
                    rfl

theorem cell21_1668629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_1668629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668629 prefixEnd_1668629 := by exact prefixLift 1668629
  have htrace : WordTrace (prefixWord ++ tailWord_1668629) baseStart_1668629 baseEnd_1668629 := by
    simpa [prefixWord, tailWord_1668629, baseEnd_1668629] using wordTrace_append hprefix tailTrace_1668629
  have hstable : (prefixWord ++ tailWord_1668629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668629).length < 2 ^ (prefixWord ++ tailWord_1668629).sum := by decide
  have hdescent : baseEnd_1668629 < baseStart_1668629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668638 : List Nat := [4, 3, 3, 1, 1, 1, 2, 3, 3]
def baseStart_1668638 : Nat := 118140960795 + 1668638 * 2 ^ 59
def prefixEnd_1668638 : Nat := 4983230072969 + 3 ^ 40 * 1668638 * 2
def baseEnd_1668638 : Nat := 380805925492065635489369

theorem tailTrace_1668638 : CollatzResearch.WordTrace tailWord_1668638 prefixEnd_1668638 380805925492065635489369 := by
  unfold tailWord_1668638
  simp only [CollatzResearch.WordTrace]
  refine ⟨7607528466102122690879821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40573485152544654351359045 7607528466102122690879821)
  ·
    refine ⟨2852823174788296009079933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7607528466102122690879821 2852823174788296009079933)
    ·
      refine ⟨1069808690545611003404975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2852823174788296009079933 1069808690545611003404975)
      ·
        refine ⟨1604713035818416505107463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1069808690545611003404975 1604713035818416505107463)
        ·
          refine ⟨2407069553727624757661195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1604713035818416505107463 2407069553727624757661195)
          ·
            refine ⟨3610604330591437136491793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407069553727624757661195 3610604330591437136491793)
            ·
              refine ⟨2707953247943577852368845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3610604330591437136491793 2707953247943577852368845)
              ·
                refine ⟨1015482467978841694638317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2707953247943577852368845 1015482467978841694638317)
                ·
                  refine ⟨380805925492065635489369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015482467978841694638317 380805925492065635489369)
                  ·
                    rfl

theorem cell21_1668638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_1668638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668638 prefixEnd_1668638 := by exact prefixLift 1668638
  have htrace : WordTrace (prefixWord ++ tailWord_1668638) baseStart_1668638 baseEnd_1668638 := by
    simpa [prefixWord, tailWord_1668638, baseEnd_1668638] using wordTrace_append hprefix tailTrace_1668638
  have hstable : (prefixWord ++ tailWord_1668638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668638).length < 2 ^ (prefixWord ++ tailWord_1668638).sum := by decide
  have hdescent : baseEnd_1668638 < baseStart_1668638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668688 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 5]
def baseStart_1668688 : Nat := 118140960795 + 1668688 * 2 ^ 59
def prefixEnd_1668688 : Nat := 4983230072969 + 3 ^ 40 * 1668688 * 2
def baseEnd_1668688 : Nat := 380817336173276659655933

theorem tailTrace_1668688 : CollatzResearch.WordTrace tailWord_1668688 prefixEnd_1668688 380817336173276659655933 := by
  unfold tailWord_1668688
  simp only [CollatzResearch.WordTrace]
  refine ⟨30431025689317920033179359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40574700919090560044239145 30431025689317920033179359)
  ·
    refine ⟨45646538533976880049769039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30431025689317920033179359 45646538533976880049769039)
    ·
      refine ⟨68469807800965320074653559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45646538533976880049769039 68469807800965320074653559)
      ·
        refine ⟨102704711701447980111980339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68469807800965320074653559 102704711701447980111980339)
        ·
          refine ⟨154057067552171970167970509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102704711701447980111980339 154057067552171970167970509)
          ·
            refine ⟨57771400332064488812988941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154057067552171970167970509 57771400332064488812988941)
            ·
              refine ⟨21664275124524183304870853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57771400332064488812988941 21664275124524183304870853)
              ·
                refine ⟨4062051585848284369663285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21664275124524183304870853 4062051585848284369663285)
                ·
                  refine ⟨380817336173276659655933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4062051585848284369663285 380817336173276659655933)
                  ·
                    rfl

theorem cell21_1668688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_1668688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668688 prefixEnd_1668688 := by exact prefixLift 1668688
  have htrace : WordTrace (prefixWord ++ tailWord_1668688) baseStart_1668688 baseEnd_1668688 := by
    simpa [prefixWord, tailWord_1668688, baseEnd_1668688] using wordTrace_append hprefix tailTrace_1668688
  have hstable : (prefixWord ++ tailWord_1668688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668688).length < 2 ^ (prefixWord ++ tailWord_1668688).sum := by decide
  have hdescent : baseEnd_1668688 < baseStart_1668688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668719 : List Nat := [1, 1, 2, 1, 3, 2, 1, 6, 4]
def baseStart_1668719 : Nat := 118140960795 + 1668719 * 2 ^ 59
def prefixEnd_1668719 : Nat := 4983230072969 + 3 ^ 40 * 1668719 * 2
def baseEnd_1668719 : Nat := 380824410795627494639203

theorem tailTrace_1668719 : CollatzResearch.WordTrace tailWord_1668719 prefixEnd_1668719 380824410795627494639203 := by
  unfold tailWord_1668719
  simp only [CollatzResearch.WordTrace]
  refine ⟨60863182041523532360737211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40575454694349021573824807 60863182041523532360737211)
  ·
    refine ⟨91294773062285298541105817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60863182041523532360737211 91294773062285298541105817)
    ·
      refine ⟨68471079796713973905829363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91294773062285298541105817 68471079796713973905829363)
      ·
        refine ⟨102706619695070960858744045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68471079796713973905829363 102706619695070960858744045)
        ·
          refine ⟨38514982385651610322029017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102706619695070960858744045 38514982385651610322029017)
          ·
            refine ⟨28886236789238707741521763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38514982385651610322029017 28886236789238707741521763)
            ·
              refine ⟨43329355183858061612282645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28886236789238707741521763 43329355183858061612282645)
              ·
                refine ⟨2031063524243346638075749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43329355183858061612282645 2031063524243346638075749)
                ·
                  refine ⟨380824410795627494639203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2031063524243346638075749 380824410795627494639203)
                  ·
                    rfl

theorem cell21_1668719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 4].length) (baseStart_1668719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668719 prefixEnd_1668719 := by exact prefixLift 1668719
  have htrace : WordTrace (prefixWord ++ tailWord_1668719) baseStart_1668719 baseEnd_1668719 := by
    simpa [prefixWord, tailWord_1668719, baseEnd_1668719] using wordTrace_append hprefix tailTrace_1668719
  have hstable : (prefixWord ++ tailWord_1668719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668719).length < 2 ^ (prefixWord ++ tailWord_1668719).sum := by decide
  have hdescent : baseEnd_1668719 < baseStart_1668719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668722 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 5]
def baseStart_1668722 : Nat := 118140960795 + 1668722 * 2 ^ 59
def prefixEnd_1668722 : Nat := 4983230072969 + 3 ^ 40 * 1668722 * 2
def baseEnd_1668722 : Nat := 380825095436500156089197

theorem tailTrace_1668722 : CollatzResearch.WordTrace tailWord_1668722 prefixEnd_1668722 380825095436500156089197 := by
  unfold tailWord_1668722
  simp only [CollatzResearch.WordTrace]
  refine ⟨15215822865128165968274105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40575527640341775915397613 15215822865128165968274105)
  ·
    refine ⟨11411867148846124476205579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15215822865128165968274105 11411867148846124476205579)
    ·
      refine ⟨17117800723269186714308369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11411867148846124476205579 17117800723269186714308369)
      ·
        refine ⟨12838350542451890035731277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17117800723269186714308369 12838350542451890035731277)
        ·
          refine ⟨4814381453419458763399229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12838350542451890035731277 4814381453419458763399229)
          ·
            refine ⟨1805393045032297036274711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4814381453419458763399229 1805393045032297036274711)
            ·
              refine ⟨2708089567548445554412067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1805393045032297036274711 2708089567548445554412067)
              ·
                refine ⟨4062134351322668331618101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2708089567548445554412067 4062134351322668331618101)
                ·
                  refine ⟨380825095436500156089197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4062134351322668331618101 380825095436500156089197)
                  ·
                    rfl

theorem cell21_1668722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_1668722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668722 prefixEnd_1668722 := by exact prefixLift 1668722
  have htrace : WordTrace (prefixWord ++ tailWord_1668722) baseStart_1668722 baseEnd_1668722 := by
    simpa [prefixWord, tailWord_1668722, baseEnd_1668722] using wordTrace_append hprefix tailTrace_1668722
  have hstable : (prefixWord ++ tailWord_1668722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668722).length < 2 ^ (prefixWord ++ tailWord_1668722).sum := by decide
  have hdescent : baseEnd_1668722 < baseStart_1668722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668750 : List Nat := [4, 1, 1, 3, 1, 2, 2, 7]
def baseStart_1668750 : Nat := 118140960795 + 1668750 * 2 ^ 59
def prefixEnd_1668750 : Nat := 4983230072969 + 3 ^ 40 * 1668750 * 2
def baseEnd_1668750 : Nat := 126943828472659443207491

theorem tailTrace_1668750 : CollatzResearch.WordTrace tailWord_1668750 prefixEnd_1668750 126943828472659443207491 := by
  unfold tailWord_1668750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7608039088051403081889463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40576208469607483103410469 7608039088051403081889463)
  ·
    refine ⟨11412058632077104622834195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7608039088051403081889463 11412058632077104622834195)
    ·
      refine ⟨17118087948115656934251293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11412058632077104622834195 17118087948115656934251293)
      ·
        refine ⟨6419282980543371350344235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17118087948115656934251293 6419282980543371350344235)
        ·
          refine ⟨9628924470815057025516353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6419282980543371350344235 9628924470815057025516353)
          ·
            refine ⟨7221693353111292769137265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9628924470815057025516353 7221693353111292769137265)
            ·
              refine ⟨5416270014833469576852949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7221693353111292769137265 5416270014833469576852949)
              ·
                refine ⟨126943828472659443207491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5416270014833469576852949 126943828472659443207491)
                ·
                  rfl

theorem cell21_1668750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_1668750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668750 prefixEnd_1668750 := by exact prefixLift 1668750
  have htrace : WordTrace (prefixWord ++ tailWord_1668750) baseStart_1668750 baseEnd_1668750 := by
    simpa [prefixWord, tailWord_1668750, baseEnd_1668750] using wordTrace_append hprefix tailTrace_1668750
  have hstable : (prefixWord ++ tailWord_1668750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668750).length < 2 ^ (prefixWord ++ tailWord_1668750).sum := by decide
  have hdescent : baseEnd_1668750 < baseStart_1668750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668767 : List Nat := [1, 1, 2, 7, 2, 8]
def baseStart_1668767 : Nat := 118140960795 + 1668767 * 2 ^ 59
def prefixEnd_1668767 : Nat := 4983230072969 + 3 ^ 40 * 1668767 * 2
def baseEnd_1668767 : Nat := 14105013520355188068115

theorem tailTrace_1668767 : CollatzResearch.WordTrace tailWord_1668767 prefixEnd_1668767 14105013520355188068115 := by
  unfold tailWord_1668767
  simp only [CollatzResearch.WordTrace]
  refine ⟨60864932745349636558484555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40576621830233091038989703 60864932745349636558484555)
  ·
    refine ⟨91297399118024454837726833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60864932745349636558484555 91297399118024454837726833)
    ·
      refine ⟨68473049338518341128295125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91297399118024454837726833 68473049338518341128295125)
      ·
        refine ⟨1604837093871523620194417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 68473049338518341128295125 1604837093871523620194417)
        ·
          refine ⟨1203627820403642715145813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1604837093871523620194417 1203627820403642715145813)
          ·
            refine ⟨14105013520355188068115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1203627820403642715145813 14105013520355188068115)
            ·
              rfl

theorem cell21_1668767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 8].length) (baseStart_1668767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668767 prefixEnd_1668767 := by exact prefixLift 1668767
  have htrace : WordTrace (prefixWord ++ tailWord_1668767) baseStart_1668767 baseEnd_1668767 := by
    simpa [prefixWord, tailWord_1668767, baseEnd_1668767] using wordTrace_append hprefix tailTrace_1668767
  have hstable : (prefixWord ++ tailWord_1668767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668767).length < 2 ^ (prefixWord ++ tailWord_1668767).sum := by decide
  have hdescent : baseEnd_1668767 < baseStart_1668767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668770 : List Nat := [3, 3, 1, 4, 1, 1, 2, 2, 4]
def baseStart_1668770 : Nat := 118140960795 + 1668770 * 2 ^ 59
def prefixEnd_1668770 : Nat := 4983230072969 + 3 ^ 40 * 1668770 * 2
def baseEnd_1668770 : Nat := 380836049690462739289099

theorem tailTrace_1668770 : CollatzResearch.WordTrace tailWord_1668770 prefixEnd_1668770 380836049690462739289099 := by
  unfold tailWord_1668770
  simp only [CollatzResearch.WordTrace]
  refine ⟨15216260541084692017710941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40576694776225845380562509 15216260541084692017710941)
  ·
    refine ⟨5706097702906759506641603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15216260541084692017710941 5706097702906759506641603)
    ·
      refine ⟨8559146554360139259962405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5706097702906759506641603 8559146554360139259962405)
      ·
        refine ⟨1604839978942526111242951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8559146554360139259962405 1604839978942526111242951)
        ·
          refine ⟨2407259968413789166864427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1604839978942526111242951 2407259968413789166864427)
          ·
            refine ⟨3610889952620683750296641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407259968413789166864427 3610889952620683750296641)
            ·
              refine ⟨2708167464465512812722481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3610889952620683750296641 2708167464465512812722481)
              ·
                refine ⟨2031125598349134609541861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2708167464465512812722481 2031125598349134609541861)
                ·
                  refine ⟨380836049690462739289099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2031125598349134609541861 380836049690462739289099)
                  ·
                    rfl

theorem cell21_1668770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_1668770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668770 prefixEnd_1668770 := by exact prefixLift 1668770
  have htrace : WordTrace (prefixWord ++ tailWord_1668770) baseStart_1668770 baseEnd_1668770 := by
    simpa [prefixWord, tailWord_1668770, baseEnd_1668770] using wordTrace_append hprefix tailTrace_1668770
  have hstable : (prefixWord ++ tailWord_1668770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668770).length < 2 ^ (prefixWord ++ tailWord_1668770).sum := by decide
  have hdescent : baseEnd_1668770 < baseStart_1668770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668781 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 5]
def baseStart_1668781 : Nat := 118140960795 + 1668781 * 2 ^ 59
def prefixEnd_1668781 : Nat := 4983230072969 + 3 ^ 40 * 1668781 * 2
def baseEnd_1668781 : Nat := 380838560040329164605743

theorem tailTrace_1668781 : CollatzResearch.WordTrace tailWord_1668781 prefixEnd_1668781 380838560040329164605743 := by
  unfold tailWord_1668781
  simp only [CollatzResearch.WordTrace]
  refine ⟨60865443367298916949494197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40576962244865944632996131 60865443367298916949494197)
  ·
    refine ⟨5706135315684273464015081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60865443367298916949494197 5706135315684273464015081)
    ·
      refine ⟨4279601486763205098011311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5706135315684273464015081 4279601486763205098011311)
      ·
        refine ⟨6419402230144807647016967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4279601486763205098011311 6419402230144807647016967)
        ·
          refine ⟨9629103345217211470525451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6419402230144807647016967 9629103345217211470525451)
          ·
            refine ⟨14443655017825817205788177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9629103345217211470525451 14443655017825817205788177)
            ·
              refine ⟨10832741263369362904341133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14443655017825817205788177 10832741263369362904341133)
              ·
                refine ⟨4062277973763511089127925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10832741263369362904341133 4062277973763511089127925)
                ·
                  refine ⟨380838560040329164605743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4062277973763511089127925 380838560040329164605743)
                  ·
                    rfl

theorem cell21_1668781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_1668781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668781 prefixEnd_1668781 := by exact prefixLift 1668781
  have htrace : WordTrace (prefixWord ++ tailWord_1668781) baseStart_1668781 baseEnd_1668781 := by
    simpa [prefixWord, tailWord_1668781, baseEnd_1668781] using wordTrace_append hprefix tailTrace_1668781
  have hstable : (prefixWord ++ tailWord_1668781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668781).length < 2 ^ (prefixWord ++ tailWord_1668781).sum := by decide
  have hdescent : baseEnd_1668781 < baseStart_1668781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668829 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 6]
def baseStart_1668829 : Nat := 118140960795 + 1668829 * 2 ^ 59
def prefixEnd_1668829 : Nat := 4983230072969 + 3 ^ 40 * 1668829 * 2
def baseEnd_1668829 : Nat := 380849514294291747805645

theorem tailTrace_1668829 : CollatzResearch.WordTrace tailWord_1668829 prefixEnd_1668829 380849514294291747805645 := by
  unfold tailWord_1668829
  simp only [CollatzResearch.WordTrace]
  refine ⟨60867194071125021147241541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40578129380750014098161027 60867194071125021147241541)
  ·
    refine ⟨11412598888335941465107789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60867194071125021147241541 11412598888335941465107789)
    ·
      refine ⟨4279724583125978049415421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11412598888335941465107789 4279724583125978049415421)
      ·
        refine ⟨1604896718672241768530783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4279724583125978049415421 1604896718672241768530783)
        ·
          refine ⟨2407345078008362652796175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1604896718672241768530783 2407345078008362652796175)
          ·
            refine ⟨3611017617012543979194263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407345078008362652796175 3611017617012543979194263)
            ·
              refine ⟨5416526425518815968791395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3611017617012543979194263 5416526425518815968791395)
              ·
                refine ⟨8124789638278223953187093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5416526425518815968791395 8124789638278223953187093)
                ·
                  refine ⟨380849514294291747805645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8124789638278223953187093 380849514294291747805645)
                  ·
                    rfl

theorem cell21_1668829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_1668829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668829 prefixEnd_1668829 := by exact prefixLift 1668829
  have htrace : WordTrace (prefixWord ++ tailWord_1668829) baseStart_1668829 baseEnd_1668829 := by
    simpa [prefixWord, tailWord_1668829, baseEnd_1668829] using wordTrace_append hprefix tailTrace_1668829
  have hstable : (prefixWord ++ tailWord_1668829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668829).length < 2 ^ (prefixWord ++ tailWord_1668829).sum := by decide
  have hdescent : baseEnd_1668829 < baseStart_1668829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668874 : List Nat := [3, 1, 2, 2, 1, 3, 3, 3, 3]
def baseStart_1668874 : Nat := 118140960795 + 1668874 * 2 ^ 59
def prefixEnd_1668874 : Nat := 4983230072969 + 3 ^ 40 * 1668874 * 2
def baseEnd_1668874 : Nat := 380859783907381669555553

theorem tailTrace_1668874 : CollatzResearch.WordTrace tailWord_1668874 prefixEnd_1668874 380859783907381669555553 := by
  unfold tailWord_1668874
  simp only [CollatzResearch.WordTrace]
  refine ⟨15217208838990498458157419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40579223570641329221753117 15217208838990498458157419)
  ·
    refine ⟨22825813258485747687236129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15217208838990498458157419 22825813258485747687236129)
    ·
      refine ⟨17119359943864310765427097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22825813258485747687236129 17119359943864310765427097)
      ·
        refine ⟨12839519957898233074070323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17119359943864310765427097 12839519957898233074070323)
        ·
          refine ⟨19259279936847349611105485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12839519957898233074070323 19259279936847349611105485)
          ·
            refine ⟨7222229976317756104164557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19259279936847349611105485 7222229976317756104164557)
            ·
              refine ⟨2708336241119158539061709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7222229976317756104164557 2708336241119158539061709)
              ·
                refine ⟨1015626090419684452148141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2708336241119158539061709 1015626090419684452148141)
                ·
                  refine ⟨380859783907381669555553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015626090419684452148141 380859783907381669555553)
                  ·
                    rfl

theorem cell21_1668874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_1668874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668874 prefixEnd_1668874 := by exact prefixLift 1668874
  have htrace : WordTrace (prefixWord ++ tailWord_1668874) baseStart_1668874 baseEnd_1668874 := by
    simpa [prefixWord, tailWord_1668874, baseEnd_1668874] using wordTrace_append hprefix tailTrace_1668874
  have hstable : (prefixWord ++ tailWord_1668874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668874).length < 2 ^ (prefixWord ++ tailWord_1668874).sum := by decide
  have hdescent : baseEnd_1668874 < baseStart_1668874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668885 : List Nat := [1, 3, 2, 1, 2, 3, 9]
def baseStart_1668885 : Nat := 118140960795 + 1668885 * 2 ^ 59
def prefixEnd_1668885 : Nat := 4983230072969 + 3 ^ 40 * 1668885 * 2
def baseEnd_1668885 : Nat := 42318032695249788319133

theorem tailTrace_1668885 : CollatzResearch.WordTrace tailWord_1668885 prefixEnd_1668885 42318032695249788319133 := by
  unfold tailWord_1668885
  simp only [CollatzResearch.WordTrace]
  refine ⟨60869236558922142711280109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40579491039281428474186739 60869236558922142711280109)
  ·
    refine ⟨22825963709595803516730041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60869236558922142711280109 22825963709595803516730041)
    ·
      refine ⟨17119472782196852637547531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22825963709595803516730041 17119472782196852637547531)
      ·
        refine ⟨25679209173295278956321297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17119472782196852637547531 25679209173295278956321297)
        ·
          refine ⟨19259406879971459217240973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25679209173295278956321297 19259406879971459217240973)
          ·
            refine ⟨7222277579989297206465365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19259406879971459217240973 7222277579989297206465365)
            ·
              refine ⟨42318032695249788319133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7222277579989297206465365 42318032695249788319133)
              ·
                rfl

theorem cell21_1668885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 9].length) (baseStart_1668885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668885 prefixEnd_1668885 := by exact prefixLift 1668885
  have htrace : WordTrace (prefixWord ++ tailWord_1668885) baseStart_1668885 baseEnd_1668885 := by
    simpa [prefixWord, tailWord_1668885, baseEnd_1668885] using wordTrace_append hprefix tailTrace_1668885
  have hstable : (prefixWord ++ tailWord_1668885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668885).length < 2 ^ (prefixWord ++ tailWord_1668885).sum := by decide
  have hdescent : baseEnd_1668885 < baseStart_1668885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668933 : List Nat := [1, 3, 1, 1, 1, 2, 4, 5, 3]
def baseStart_1668933 : Nat := 118140960795 + 1668933 * 2 ^ 59
def prefixEnd_1668933 : Nat := 4983230072969 + 3 ^ 40 * 1668933 * 2
def baseEnd_1668933 : Nat := 380873248511210678072099

theorem tailTrace_1668933 : CollatzResearch.WordTrace tailWord_1668933 prefixEnd_1668933 380873248511210678072099 := by
  unfold tailWord_1668933
  simp only [CollatzResearch.WordTrace]
  refine ⟨60870987262748246909027453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40580658175165497939351635 60870987262748246909027453)
  ·
    refine ⟨22826620223530592590885295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60870987262748246909027453 22826620223530592590885295)
    ·
      refine ⟨34239930335295888886327943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22826620223530592590885295 34239930335295888886327943)
      ·
        refine ⟨51359895502943833329491915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34239930335295888886327943 51359895502943833329491915)
        ·
          refine ⟨77039843254415749994237873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51359895502943833329491915 77039843254415749994237873)
          ·
            refine ⟨57779882440811812495678405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77039843254415749994237873 57779882440811812495678405)
            ·
              refine ⟨10833727957652214842939701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57779882440811812495678405 10833727957652214842939701)
              ·
                refine ⟨1015661996029895141525597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10833727957652214842939701 1015661996029895141525597)
                ·
                  refine ⟨380873248511210678072099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015661996029895141525597 380873248511210678072099)
                  ·
                    rfl

theorem cell21_1668933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_1668933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1668933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1668933 prefixEnd_1668933 := by exact prefixLift 1668933
  have htrace : WordTrace (prefixWord ++ tailWord_1668933) baseStart_1668933 baseEnd_1668933 := by
    simpa [prefixWord, tailWord_1668933, baseEnd_1668933] using wordTrace_append hprefix tailTrace_1668933
  have hstable : (prefixWord ++ tailWord_1668933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668933).length < 2 ^ (prefixWord ++ tailWord_1668933).sum := by decide
  have hdescent : baseEnd_1668933 < baseStart_1668933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669009 : List Nat := [1, 2, 2, 1, 1, 1, 6, 4, 3]
def baseStart_1669009 : Nat := 118140960795 + 1669009 * 2 ^ 59
def prefixEnd_1669009 : Nat := 4983230072969 + 3 ^ 40 * 1669009 * 2
def baseEnd_1669009 : Nat := 380890592746651434805277

theorem tailTrace_1669009 : CollatzResearch.WordTrace tailWord_1669009 prefixEnd_1669009 380890592746651434805277 := by
  unfold tailWord_1669009
  simp only [CollatzResearch.WordTrace]
  refine ⟨60873759210472911888794081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40582506140315274592529387 60873759210472911888794081)
  ·
    refine ⟨45655319407854683916595561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60873759210472911888794081 45655319407854683916595561)
    ·
      refine ⟨34241489555891012937446671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45655319407854683916595561 34241489555891012937446671)
      ·
        refine ⟨51362234333836519406170007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34241489555891012937446671 51362234333836519406170007)
        ·
          refine ⟨77043351500754779109255011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51362234333836519406170007 77043351500754779109255011)
          ·
            refine ⟨115565027251132168663882517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77043351500754779109255011 115565027251132168663882517)
            ·
              refine ⟨5417110652396820406119493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115565027251132168663882517 5417110652396820406119493)
              ·
                refine ⟨1015708247324403826147405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5417110652396820406119493 1015708247324403826147405)
                ·
                  refine ⟨380890592746651434805277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015708247324403826147405 380890592746651434805277)
                  ·
                    rfl

theorem cell21_1669009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 3].length) (baseStart_1669009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669009 prefixEnd_1669009 := by exact prefixLift 1669009
  have htrace : WordTrace (prefixWord ++ tailWord_1669009) baseStart_1669009 baseEnd_1669009 := by
    simpa [prefixWord, tailWord_1669009, baseEnd_1669009] using wordTrace_append hprefix tailTrace_1669009
  have hstable : (prefixWord ++ tailWord_1669009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669009).length < 2 ^ (prefixWord ++ tailWord_1669009).sum := by decide
  have hdescent : baseEnd_1669009 < baseStart_1669009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669051 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 9]
def baseStart_1669051 : Nat := 118140960795 + 1669051 * 2 ^ 59
def prefixEnd_1669051 : Nat := 4983230072969 + 3 ^ 40 * 1669051 * 2
def baseEnd_1669051 : Nat := 380900177718868695105191

theorem tailTrace_1669051 : CollatzResearch.WordTrace tailWord_1669051 prefixEnd_1669051 380900177718868695105191 := by
  unfold tailWord_1669051
  simp only [CollatzResearch.WordTrace]
  refine ⟨60875291076320753061823007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40583527384213835374548671 60875291076320753061823007)
  ·
    refine ⟨91312936614481129592734511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60875291076320753061823007 91312936614481129592734511)
    ·
      refine ⟨136969404921721694389101767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91312936614481129592734511 136969404921721694389101767)
      ·
        refine ⟨205454107382582541583652651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136969404921721694389101767 205454107382582541583652651)
        ·
          refine ⟨308181161073873812375478977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205454107382582541583652651 308181161073873812375478977)
          ·
            refine ⟨231135870805405359281609233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308181161073873812375478977 231135870805405359281609233)
            ·
              refine ⟨173351903104054019461206925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231135870805405359281609233 173351903104054019461206925)
              ·
                refine ⟨65006963664020257297952597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173351903104054019461206925 65006963664020257297952597)
                ·
                  refine ⟨380900177718868695105191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65006963664020257297952597 380900177718868695105191)
                  ·
                    rfl

theorem cell21_1669051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 9].length) (baseStart_1669051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669051 prefixEnd_1669051 := by exact prefixLift 1669051
  have htrace : WordTrace (prefixWord ++ tailWord_1669051) baseStart_1669051 baseEnd_1669051 := by
    simpa [prefixWord, tailWord_1669051, baseEnd_1669051] using wordTrace_append hprefix tailTrace_1669051
  have hstable : (prefixWord ++ tailWord_1669051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669051).length < 2 ^ (prefixWord ++ tailWord_1669051).sum := by decide
  have hdescent : baseEnd_1669051 < baseStart_1669051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669054 : List Nat := [4, 2, 1, 1, 1, 5, 7]
def baseStart_1669054 : Nat := 118140960795 + 1669054 * 2 ^ 59
def prefixEnd_1669054 : Nat := 4983230072969 + 3 ^ 40 * 1669054 * 2
def baseEnd_1669054 : Nat := 42322318039971261839465

theorem tailTrace_1669054 : CollatzResearch.WordTrace tailWord_1669054 prefixEnd_1669054 42322318039971261839465 := by
  unfold tailWord_1669054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7609425061913735571772777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40583600330206589716121477 7609425061913735571772777)
  ·
    refine ⟨5707068796435301678829583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7609425061913735571772777 5707068796435301678829583)
    ·
      refine ⟨8560603194652952518244375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5707068796435301678829583 8560603194652952518244375)
      ·
        refine ⟨12840904791979428777366563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8560603194652952518244375 12840904791979428777366563)
        ·
          refine ⟨19261357187969143166049845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12840904791979428777366563 19261357187969143166049845)
          ·
            refine ⟨1805752236372107171817173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19261357187969143166049845 1805752236372107171817173)
            ·
              refine ⟨42322318039971261839465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1805752236372107171817173 42322318039971261839465)
              ·
                rfl

theorem cell21_1669054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 7].length) (baseStart_1669054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669054 prefixEnd_1669054 := by exact prefixLift 1669054
  have htrace : WordTrace (prefixWord ++ tailWord_1669054) baseStart_1669054 baseEnd_1669054 := by
    simpa [prefixWord, tailWord_1669054, baseEnd_1669054] using wordTrace_append hprefix tailTrace_1669054
  have hstable : (prefixWord ++ tailWord_1669054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669054).length < 2 ^ (prefixWord ++ tailWord_1669054).sum := by decide
  have hdescent : baseEnd_1669054 < baseStart_1669054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669074 : List Nat := [3, 2, 2, 3, 2, 2, 2, 1, 4]
def baseStart_1669074 : Nat := 118140960795 + 1669074 * 2 ^ 59
def prefixEnd_1669074 : Nat := 4983230072969 + 3 ^ 40 * 1669074 * 2
def baseEnd_1669074 : Nat := 380905426632225766221811

theorem tailTrace_1669074 : CollatzResearch.WordTrace tailWord_1669074 prefixEnd_1669074 380905426632225766221811 := by
  unfold tailWord_1669074
  simp only [CollatzResearch.WordTrace]
  refine ⟨15219032488809356997477569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40584086636824951993273517 15219032488809356997477569)
  ·
    refine ⟨11414274366607017748108177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15219032488809356997477569 11414274366607017748108177)
    ·
      refine ⟨8560705774955263311081133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11414274366607017748108177 8560705774955263311081133)
      ·
        refine ⟨3210264665608223741655425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8560705774955263311081133 3210264665608223741655425)
        ·
          refine ⟨2407698499206167806241569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3210264665608223741655425 2407698499206167806241569)
          ·
            refine ⟨1805773874404625854681177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2407698499206167806241569 1805773874404625854681177)
            ·
              refine ⟨1354330405803469391010883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1805773874404625854681177 1354330405803469391010883)
              ·
                refine ⟨2031495608705204086516325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354330405803469391010883 2031495608705204086516325)
                ·
                  refine ⟨380905426632225766221811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2031495608705204086516325 380905426632225766221811)
                  ·
                    rfl

theorem cell21_1669074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_1669074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669074 prefixEnd_1669074 := by exact prefixLift 1669074
  have htrace : WordTrace (prefixWord ++ tailWord_1669074) baseStart_1669074 baseEnd_1669074 := by
    simpa [prefixWord, tailWord_1669074, baseEnd_1669074] using wordTrace_append hprefix tailTrace_1669074
  have hstable : (prefixWord ++ tailWord_1669074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669074).length < 2 ^ (prefixWord ++ tailWord_1669074).sum := by decide
  have hdescent : baseEnd_1669074 < baseStart_1669074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669144 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 5]
def baseStart_1669144 : Nat := 118140960795 + 1669144 * 2 ^ 59
def prefixEnd_1669144 : Nat := 4983230072969 + 3 ^ 40 * 1669144 * 2
def baseEnd_1669144 : Nat := 380921401585921200055001

theorem tailTrace_1669144 : CollatzResearch.WordTrace tailWord_1669144 prefixEnd_1669144 380921401585921200055001 := by
  unfold tailWord_1669144
  simp only [CollatzResearch.WordTrace]
  refine ⟨30439341532491914972479243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40585788709989219963305657 30439341532491914972479243)
  ·
    refine ⟨45659012298737872458718865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30439341532491914972479243 45659012298737872458718865)
    ·
      refine ⟨34244259224053404344039149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45659012298737872458718865 34244259224053404344039149)
      ·
        refine ⟨12841597209020026629014681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34244259224053404344039149 12841597209020026629014681)
        ·
          refine ⟨9631197906765019971761011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12841597209020026629014681 9631197906765019971761011)
          ·
            refine ⟨14446796860147529957641517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9631197906765019971761011 14446796860147529957641517)
            ·
              refine ⟨5417548822555323734115569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14446796860147529957641517 5417548822555323734115569)
              ·
                refine ⟨4063161616916492800586677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5417548822555323734115569 4063161616916492800586677)
                ·
                  refine ⟨380921401585921200055001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4063161616916492800586677 380921401585921200055001)
                  ·
                    rfl

theorem cell21_1669144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_1669144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669144 prefixEnd_1669144 := by exact prefixLift 1669144
  have htrace : WordTrace (prefixWord ++ tailWord_1669144) baseStart_1669144 baseEnd_1669144 := by
    simpa [prefixWord, tailWord_1669144, baseEnd_1669144] using wordTrace_append hprefix tailTrace_1669144
  have hstable : (prefixWord ++ tailWord_1669144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669144).length < 2 ^ (prefixWord ++ tailWord_1669144).sum := by decide
  have hdescent : baseEnd_1669144 < baseStart_1669144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669175 : List Nat := [1, 1, 3, 1, 2, 2, 5, 2, 4]
def baseStart_1669175 : Nat := 118140960795 + 1669175 * 2 ^ 59
def prefixEnd_1669175 : Nat := 4983230072969 + 3 ^ 40 * 1669175 * 2
def baseEnd_1669175 : Nat := 380928476208272035038271

theorem tailTrace_1669175 : CollatzResearch.WordTrace tailWord_1669175 prefixEnd_1669175 380928476208272035038271 := by
  unfold tailWord_1669175
  simp only [CollatzResearch.WordTrace]
  refine ⟨60879813727871522239336979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40586542485247681492891319 60879813727871522239336979)
  ·
    refine ⟨91319720591807283359005469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60879813727871522239336979 91319720591807283359005469)
    ·
      refine ⟨34244895221927731259627051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91319720591807283359005469 34244895221927731259627051)
      ·
        refine ⟨51367342832891596889440577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34244895221927731259627051 51367342832891596889440577)
        ·
          refine ⟨38525507124668697667080433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51367342832891596889440577 38525507124668697667080433)
          ·
            refine ⟨28894130343501523250310325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38525507124668697667080433 28894130343501523250310325)
            ·
              refine ⟨2708824719703267804716593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28894130343501523250310325 2708824719703267804716593)
              ·
                refine ⟨2031618539777450853537445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2708824719703267804716593 2031618539777450853537445)
                ·
                  refine ⟨380928476208272035038271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2031618539777450853537445 380928476208272035038271)
                  ·
                    rfl

theorem cell21_1669175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 4].length) (baseStart_1669175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669175 prefixEnd_1669175 := by exact prefixLift 1669175
  have htrace : WordTrace (prefixWord ++ tailWord_1669175) baseStart_1669175 baseEnd_1669175 := by
    simpa [prefixWord, tailWord_1669175, baseEnd_1669175] using wordTrace_append hprefix tailTrace_1669175
  have hstable : (prefixWord ++ tailWord_1669175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669175).length < 2 ^ (prefixWord ++ tailWord_1669175).sum := by decide
  have hdescent : baseEnd_1669175 < baseStart_1669175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669251 : List Nat := [1, 1, 1, 3, 3, 4, 1, 3, 4]
def baseStart_1669251 : Nat := 118140960795 + 1669251 * 2 ^ 59
def prefixEnd_1669251 : Nat := 4983230072969 + 3 ^ 40 * 1669251 * 2
def baseEnd_1669251 : Nat := 380945820443712791771449

theorem tailTrace_1669251 : CollatzResearch.WordTrace tailWord_1669251 prefixEnd_1669251 380945820443712791771449 := by
  unfold tailWord_1669251
  simp only [CollatzResearch.WordTrace]
  refine ⟨60882585675596187219103607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40588390450397458146069071 60882585675596187219103607)
  ·
    refine ⟨91323878513394280828655411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60882585675596187219103607 91323878513394280828655411)
    ·
      refine ⟨136985817770091421242983117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91323878513394280828655411 136985817770091421242983117)
      ·
        refine ⟨51369681663784282966118669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136985817770091421242983117 51369681663784282966118669)
        ·
          refine ⟨19263630623919106112294501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51369681663784282966118669 19263630623919106112294501)
          ·
            refine ⟨3611930741984832396055219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19263630623919106112294501 3611930741984832396055219)
            ·
              refine ⟨5417896112977248594082829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3611930741984832396055219 5417896112977248594082829)
              ·
                refine ⟨2031711042366468222781061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5417896112977248594082829 2031711042366468222781061)
                ·
                  refine ⟨380945820443712791771449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2031711042366468222781061 380945820443712791771449)
                  ·
                    rfl

theorem cell21_1669251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 4].length) (baseStart_1669251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669251 prefixEnd_1669251 := by exact prefixLift 1669251
  have htrace : WordTrace (prefixWord ++ tailWord_1669251) baseStart_1669251 baseEnd_1669251 := by
    simpa [prefixWord, tailWord_1669251, baseEnd_1669251] using wordTrace_append hprefix tailTrace_1669251
  have hstable : (prefixWord ++ tailWord_1669251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669251).length < 2 ^ (prefixWord ++ tailWord_1669251).sum := by decide
  have hdescent : baseEnd_1669251 < baseStart_1669251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669330 : List Nat := [3, 2, 2, 2, 1, 3, 2, 3, 3]
def baseStart_1669330 : Nat := 118140960795 + 1669330 * 2 ^ 59
def prefixEnd_1669330 : Nat := 4983230072969 + 3 ^ 40 * 1669330 * 2
def baseEnd_1669330 : Nat := 380963849320026209954621

theorem tailTrace_1669330 : CollatzResearch.WordTrace tailWord_1669330 prefixEnd_1669330 380963849320026209954621 := by
  unfold tailWord_1669330
  simp only [CollatzResearch.WordTrace]
  refine ⟨15221366760577495927807361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40590311361539989140819629 15221366760577495927807361)
  ·
    refine ⟨11416025070433121945855521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15221366760577495927807361 11416025070433121945855521)
    ·
      refine ⟨8562018802824841459391641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11416025070433121945855521 8562018802824841459391641)
      ·
        refine ⟨6421514102118631094543731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8562018802824841459391641 6421514102118631094543731)
        ·
          refine ⟨9632271153177946641815597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6421514102118631094543731 9632271153177946641815597)
          ·
            refine ⟨3612101682441729990680849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9632271153177946641815597 3612101682441729990680849)
            ·
              refine ⟨2709076261831297493010637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3612101682441729990680849 2709076261831297493010637)
              ·
                refine ⟨1015903598186736559878989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2709076261831297493010637 1015903598186736559878989)
                ·
                  refine ⟨380963849320026209954621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015903598186736559878989 380963849320026209954621)
                  ·
                    rfl

theorem cell21_1669330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_1669330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669330 prefixEnd_1669330 := by exact prefixLift 1669330
  have htrace : WordTrace (prefixWord ++ tailWord_1669330) baseStart_1669330 baseEnd_1669330 := by
    simpa [prefixWord, tailWord_1669330, baseEnd_1669330] using wordTrace_append hprefix tailTrace_1669330
  have hstable : (prefixWord ++ tailWord_1669330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669330).length < 2 ^ (prefixWord ++ tailWord_1669330).sum := by decide
  have hdescent : baseEnd_1669330 < baseStart_1669330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669372 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 5]
def baseStart_1669372 : Nat := 118140960795 + 1669372 * 2 ^ 59
def prefixEnd_1669372 : Nat := 4983230072969 + 3 ^ 40 * 1669372 * 2
def baseEnd_1669372 : Nat := 380973434292243470254535

theorem tailTrace_1669372 : CollatzResearch.WordTrace tailWord_1669372 prefixEnd_1669372 380973434292243470254535 := by
  unfold tailWord_1669372
  simp only [CollatzResearch.WordTrace]
  refine ⟨30443499454078912442129185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40591332605438549922838913 30443499454078912442129185)
  ·
    refine ⟨22832624590559184331596889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30443499454078912442129185 22832624590559184331596889)
    ·
      refine ⟨17124468442919388248697667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22832624590559184331596889 17124468442919388248697667)
      ·
        refine ⟨25686702664379082373046501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17124468442919388248697667 25686702664379082373046501)
        ·
          refine ⟨4816256749571077944946219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25686702664379082373046501 4816256749571077944946219)
          ·
            refine ⟨7224385124356616917419329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4816256749571077944946219 7224385124356616917419329)
            ·
              refine ⟨5418288843267462688064497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7224385124356616917419329 5418288843267462688064497)
              ·
                refine ⟨4063716632450597016048373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5418288843267462688064497 4063716632450597016048373)
                ·
                  refine ⟨380973434292243470254535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4063716632450597016048373 380973434292243470254535)
                  ·
                    rfl

theorem cell21_1669372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_1669372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669372 prefixEnd_1669372 := by exact prefixLift 1669372
  have htrace : WordTrace (prefixWord ++ tailWord_1669372) baseStart_1669372 baseEnd_1669372 := by
    simpa [prefixWord, tailWord_1669372, baseEnd_1669372] using wordTrace_append hprefix tailTrace_1669372
  have hstable : (prefixWord ++ tailWord_1669372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669372).length < 2 ^ (prefixWord ++ tailWord_1669372).sum := by decide
  have hdescent : baseEnd_1669372 < baseStart_1669372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669386 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 6]
def baseStart_1669386 : Nat := 118140960795 + 1669386 * 2 ^ 59
def prefixEnd_1669386 : Nat := 4983230072969 + 3 ^ 40 * 1669386 * 2
def baseEnd_1669386 : Nat := 380976629282982557021173

theorem tailTrace_1669386 : CollatzResearch.WordTrace tailWord_1669386 prefixEnd_1669386 380976629282982557021173 := by
  unfold tailWord_1669386
  simp only [CollatzResearch.WordTrace]
  refine ⟨15221877382526776318817003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40591673020071403516845341 15221877382526776318817003)
  ·
    refine ⟨22832816073790164478225505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15221877382526776318817003 22832816073790164478225505)
    ·
      refine ⟨17124612055342623358669129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22832816073790164478225505 17124612055342623358669129)
      ·
        refine ⟨12843459041506967519001847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17124612055342623358669129 12843459041506967519001847)
        ·
          refine ⟨19265188562260451278502771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12843459041506967519001847 19265188562260451278502771)
          ·
            refine ⟨28897782843390676917754157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19265188562260451278502771 28897782843390676917754157)
            ·
              refine ⟨10836668566271503844157809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28897782843390676917754157 10836668566271503844157809)
              ·
                refine ⟨8127501424703627883118357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10836668566271503844157809 8127501424703627883118357)
                ·
                  refine ⟨380976629282982557021173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8127501424703627883118357 380976629282982557021173)
                  ·
                    rfl

theorem cell21_1669386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_1669386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669386 prefixEnd_1669386 := by exact prefixLift 1669386
  have htrace : WordTrace (prefixWord ++ tailWord_1669386) baseStart_1669386 baseEnd_1669386 := by
    simpa [prefixWord, tailWord_1669386, baseEnd_1669386] using wordTrace_append hprefix tailTrace_1669386
  have hstable : (prefixWord ++ tailWord_1669386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669386).length < 2 ^ (prefixWord ++ tailWord_1669386).sum := by decide
  have hdescent : baseEnd_1669386 < baseStart_1669386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
