import V185TrunkScan22Chunk198

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1775244 : List Nat := [2, 2, 1, 2, 1, 1, 6, 2, 2, 3]
def baseStart_1775244 : Nat := 118140960795 + 1775244 * 2 ^ 59
def prefixEnd_1775244 : Nat := 4983230072969 + 3 ^ 40 * 1775244 * 2
def baseEnd_1775244 : Nat := 607702300673571722257205

theorem tailTrace_1775244 : CollatzResearch.WordTrace tailWord_1775244 prefixEnd_1775244 607702300673571722257205 := by
  unfold tailWord_1775244
  simp only [CollatzResearch.WordTrace]
  refine ⟨32374233990300825191158393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43165645320401100254877857 32374233990300825191158393)
  ·
    refine ⟨24280675492725618893368795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32374233990300825191158393 24280675492725618893368795)
    ·
      refine ⟨36421013239088428340053193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24280675492725618893368795 36421013239088428340053193)
      ·
        refine ⟨27315759929316321255039895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36421013239088428340053193 27315759929316321255039895)
        ·
          refine ⟨40973639893974481882559843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27315759929316321255039895 40973639893974481882559843)
          ·
            refine ⟨61460459840961722823839765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40973639893974481882559843 61460459840961722823839765)
            ·
              refine ⟨2880959055045080757367489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61460459840961722823839765 2880959055045080757367489)
              ·
                refine ⟨2160719291283810568025617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2880959055045080757367489 2160719291283810568025617)
                ·
                  refine ⟨1620539468462857926019213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2160719291283810568025617 1620539468462857926019213)
                  ·
                    refine ⟨607702300673571722257205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1620539468462857926019213 607702300673571722257205)
                    ·
                      rfl

theorem cell22_1775244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_1775244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775244 prefixEnd_1775244 := by exact prefixLift 1775244
  have htrace : WordTrace (prefixWord ++ tailWord_1775244) baseStart_1775244 baseEnd_1775244 := by
    simpa [prefixWord, tailWord_1775244, baseEnd_1775244] using wordTrace_append hprefix tailTrace_1775244
  have hstable : (prefixWord ++ tailWord_1775244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775244).length < 2 ^ (prefixWord ++ tailWord_1775244).sum := by decide
  have hdescent : baseEnd_1775244 < baseStart_1775244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775246 : List Nat := [4, 1, 1, 3, 1, 2, 4, 2, 4]
def baseStart_1775246 : Nat := 118140960795 + 1775246 * 2 ^ 59
def prefixEnd_1775246 : Nat := 4983230072969 + 3 ^ 40 * 1775246 * 2
def baseEnd_1775246 : Nat := 202567661771481461235733

theorem tailTrace_1775246 : CollatzResearch.WordTrace tailWord_1775246 prefixEnd_1775246 202567661771481461235733 := by
  unfold tailWord_1775246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8093567615824300590486199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43165693951062936482593061 8093567615824300590486199)
  ·
    refine ⟨12140351423736450885729299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8093567615824300590486199 12140351423736450885729299)
    ·
      refine ⟨18210527135604676328593949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12140351423736450885729299 18210527135604676328593949)
      ·
        refine ⟨6828947675851753623222731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18210527135604676328593949 6828947675851753623222731)
        ·
          refine ⟨10243421513777630434834097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6828947675851753623222731 10243421513777630434834097)
          ·
            refine ⟨7682566135333222826125573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10243421513777630434834097 7682566135333222826125573)
            ·
              refine ⟨1440481150374979279898545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7682566135333222826125573 1440481150374979279898545)
              ·
                refine ⟨1080360862781234459923909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1440481150374979279898545 1080360862781234459923909)
                ·
                  refine ⟨202567661771481461235733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1080360862781234459923909 202567661771481461235733)
                  ·
                    rfl

theorem cell22_1775246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_1775246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775246 prefixEnd_1775246 := by exact prefixLift 1775246
  have htrace : WordTrace (prefixWord ++ tailWord_1775246) baseStart_1775246 baseEnd_1775246 := by
    simpa [prefixWord, tailWord_1775246, baseEnd_1775246] using wordTrace_append hprefix tailTrace_1775246
  have hstable : (prefixWord ++ tailWord_1775246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775246).length < 2 ^ (prefixWord ++ tailWord_1775246).sum := by decide
  have hdescent : baseEnd_1775246 < baseStart_1775246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775306 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 3, 3]
def baseStart_1775306 : Nat := 118140960795 + 1775306 * 2 ^ 59
def prefixEnd_1775306 : Nat := 4983230072969 + 3 ^ 40 * 1775306 * 2
def baseEnd_1775306 : Nat := 607723524540624227207015

theorem tailTrace_1775306 : CollatzResearch.WordTrace tailWord_1775306 prefixEnd_1775306 607723524540624227207015 := by
  unfold tailWord_1775306
  simp only [CollatzResearch.WordTrace]
  refine ⟨16187682326594258742768443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43167152870918023314049181 16187682326594258742768443)
  ·
    refine ⟨24281523489891388114152665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16187682326594258742768443 24281523489891388114152665)
    ·
      refine ⟨18211142617418541085614499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24281523489891388114152665 18211142617418541085614499)
      ·
        refine ⟨27316713926127811628421749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18211142617418541085614499 27316713926127811628421749)
        ·
          refine ⟨2560941930574482340164539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27316713926127811628421749 2560941930574482340164539)
          ·
            refine ⟨3841412895861723510246809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2560941930574482340164539 3841412895861723510246809)
            ·
              refine ⟨2881059671896292632685107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3841412895861723510246809 2881059671896292632685107)
              ·
                refine ⟨4321589507844438949027661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2881059671896292632685107 4321589507844438949027661)
                ·
                  refine ⟨1620596065441664605885373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4321589507844438949027661 1620596065441664605885373)
                  ·
                    refine ⟨607723524540624227207015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1620596065441664605885373 607723524540624227207015)
                    ·
                      rfl

theorem cell22_1775306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_1775306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775306 prefixEnd_1775306 := by exact prefixLift 1775306
  have htrace : WordTrace (prefixWord ++ tailWord_1775306) baseStart_1775306 baseEnd_1775306 := by
    simpa [prefixWord, tailWord_1775306, baseEnd_1775306] using wordTrace_append hprefix tailTrace_1775306
  have hstable : (prefixWord ++ tailWord_1775306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775306).length < 2 ^ (prefixWord ++ tailWord_1775306).sum := by decide
  have hdescent : baseEnd_1775306 < baseStart_1775306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775319 : List Nat := [1, 1, 3, 2, 1, 3, 5, 1, 5]
def baseStart_1775319 : Nat := 118140960795 + 1775319 * 2 ^ 59
def prefixEnd_1775319 : Nat := 4983230072969 + 3 ^ 40 * 1775319 * 2
def baseEnd_1775319 : Nat := 202575991568765508877325

theorem tailTrace_1775319 : CollatzResearch.WordTrace tailWord_1775319 prefixEnd_1775319 202575991568765508877325 := by
  unfold tailWord_1775319
  simp only [CollatzResearch.WordTrace]
  refine ⟨64751203455329938191297011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43167468970219958794198007 64751203455329938191297011)
  ·
    refine ⟨97126805182994907286945517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64751203455329938191297011 97126805182994907286945517)
    ·
      refine ⟨36422551943623090232604569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97126805182994907286945517 36422551943623090232604569)
      ·
        refine ⟨27316913957717317674453427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36422551943623090232604569 27316913957717317674453427)
        ·
          refine ⟨40975370936575976511680141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27316913957717317674453427 40975370936575976511680141)
          ·
            refine ⟨15365764101215991191880053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40975370936575976511680141 15365764101215991191880053)
            ·
              refine ⟨1440540384488999174238755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15365764101215991191880053 1440540384488999174238755)
              ·
                refine ⟨2160810576733498761358133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440540384488999174238755 2160810576733498761358133)
                ·
                  refine ⟨202575991568765508877325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2160810576733498761358133 202575991568765508877325)
                  ·
                    rfl

theorem cell22_1775319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 5].length) (baseStart_1775319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775319 prefixEnd_1775319 := by exact prefixLift 1775319
  have htrace : WordTrace (prefixWord ++ tailWord_1775319) baseStart_1775319 baseEnd_1775319 := by
    simpa [prefixWord, tailWord_1775319, baseEnd_1775319] using wordTrace_append hprefix tailTrace_1775319
  have hstable : (prefixWord ++ tailWord_1775319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775319).length < 2 ^ (prefixWord ++ tailWord_1775319).sum := by decide
  have hdescent : baseEnd_1775319 < baseStart_1775319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775364 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 6]
def baseStart_1775364 : Nat := 118140960795 + 1775364 * 2 ^ 59
def prefixEnd_1775364 : Nat := 4983230072969 + 3 ^ 40 * 1775364 * 2
def baseEnd_1775364 : Nat := 202581126375310469752279

theorem tailTrace_1775364 : CollatzResearch.WordTrace tailWord_1775364 prefixEnd_1775364 202581126375310469752279 := by
  unfold tailWord_1775364
  simp only [CollatzResearch.WordTrace]
  refine ⟨32376422370083455438342573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43168563160111273917790097 32376422370083455438342573)
  ·
    refine ⟨12141158388781295789378465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32376422370083455438342573 12141158388781295789378465)
    ·
      refine ⟨9105868791585971842033849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12141158388781295789378465 9105868791585971842033849)
      ·
        refine ⟨6829401593689478881525387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9105868791585971842033849 6829401593689478881525387)
        ·
          refine ⟨10244102390534218322288081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6829401593689478881525387 10244102390534218322288081)
          ·
            refine ⟨7683076792900663741716061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10244102390534218322288081 7683076792900663741716061)
            ·
              refine ⟨2881153797337748903143523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7683076792900663741716061 2881153797337748903143523)
              ·
                refine ⟨4321730696006623354715285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2881153797337748903143523 4321730696006623354715285)
                ·
                  refine ⟨202581126375310469752279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4321730696006623354715285 202581126375310469752279)
                  ·
                    rfl

theorem cell22_1775364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_1775364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775364 prefixEnd_1775364 := by exact prefixLift 1775364
  have htrace : WordTrace (prefixWord ++ tailWord_1775364) baseStart_1775364 baseEnd_1775364 := by
    simpa [prefixWord, tailWord_1775364, baseEnd_1775364] using wordTrace_append hprefix tailTrace_1775364
  have hstable : (prefixWord ++ tailWord_1775364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775364).length < 2 ^ (prefixWord ++ tailWord_1775364).sum := by decide
  have hdescent : baseEnd_1775364 < baseStart_1775364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775377 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 6, 4]
def baseStart_1775377 : Nat := 118140960795 + 1775377 * 2 ^ 59
def prefixEnd_1775377 : Nat := 4983230072969 + 3 ^ 40 * 1775377 * 2
def baseEnd_1775377 : Nat := 607747829291603708681797

theorem tailTrace_1775377 : CollatzResearch.WordTrace tailWord_1775377 prefixEnd_1775377 607747829291603708681797 := by
  unfold tailWord_1775377
  simp only [CollatzResearch.WordTrace]
  refine ⟨64753318889119814096908385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43168879259413209397938923 64753318889119814096908385)
  ·
    refine ⟨48564989166839860572681289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64753318889119814096908385 48564989166839860572681289)
    ·
      refine ⟨36423741875129895429510967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48564989166839860572681289 36423741875129895429510967)
      ·
        refine ⟨54635612812694843144266451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36423741875129895429510967 54635612812694843144266451)
        ·
          refine ⟨81953419219042264716399677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54635612812694843144266451 81953419219042264716399677)
          ·
            refine ⟨30732532207140849268649879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81953419219042264716399677 30732532207140849268649879)
            ·
              refine ⟨46098798310711273902974819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30732532207140849268649879 46098798310711273902974819)
              ·
                refine ⟨69148197466066910854462229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46098798310711273902974819 69148197466066910854462229)
                ·
                  refine ⟨3241321756221886446302917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69148197466066910854462229 3241321756221886446302917)
                  ·
                    refine ⟨607747829291603708681797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3241321756221886446302917 607747829291603708681797)
                    ·
                      rfl

theorem cell22_1775377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_1775377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775377 prefixEnd_1775377 := by exact prefixLift 1775377
  have htrace : WordTrace (prefixWord ++ tailWord_1775377) baseStart_1775377 baseEnd_1775377 := by
    simpa [prefixWord, tailWord_1775377, baseEnd_1775377] using wordTrace_append hprefix tailTrace_1775377
  have hstable : (prefixWord ++ tailWord_1775377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775377).length < 2 ^ (prefixWord ++ tailWord_1775377).sum := by decide
  have hdescent : baseEnd_1775377 < baseStart_1775377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775392 : List Nat := [2, 1, 1, 5, 1, 1, 1, 10]
def baseStart_1775392 : Nat := 118140960795 + 1775392 * 2 ^ 59
def prefixEnd_1775392 : Nat := 4983230072969 + 3 ^ 40 * 1775392 * 2
def baseEnd_1775392 : Nat := 67528107122016518839639

theorem tailTrace_1775392 : CollatzResearch.WordTrace tailWord_1775392 prefixEnd_1775392 67528107122016518839639 := by
  unfold tailWord_1775392
  simp only [CollatzResearch.WordTrace]
  refine ⟨32376932992032735829352215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43169243989376981105802953 32376932992032735829352215)
  ·
    refine ⟨48565399488049103744028323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32376932992032735829352215 48565399488049103744028323)
    ·
      refine ⟨72848099232073655616042485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48565399488049103744028323 72848099232073655616042485)
      ·
        refine ⟨6829509303006905214003983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72848099232073655616042485 6829509303006905214003983)
        ·
          refine ⟨10244263954510357821005975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6829509303006905214003983 10244263954510357821005975)
          ·
            refine ⟨15366395931765536731508963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10244263954510357821005975 15366395931765536731508963)
            ·
              refine ⟨23049593897648305097263445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15366395931765536731508963 23049593897648305097263445)
              ·
                refine ⟨67528107122016518839639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23049593897648305097263445 67528107122016518839639)
                ·
                  rfl

theorem cell22_1775392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 10].length) (baseStart_1775392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775392 prefixEnd_1775392 := by exact prefixLift 1775392
  have htrace : WordTrace (prefixWord ++ tailWord_1775392) baseStart_1775392 baseEnd_1775392 := by
    simpa [prefixWord, tailWord_1775392, baseEnd_1775392] using wordTrace_append hprefix tailTrace_1775392
  have hstable : (prefixWord ++ tailWord_1775392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775392).length < 2 ^ (prefixWord ++ tailWord_1775392).sum := by decide
  have hdescent : baseEnd_1775392 < baseStart_1775392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775413 : List Nat := [1, 3, 3, 1, 4, 1, 2, 2, 2, 3]
def baseStart_1775413 : Nat := 118140960795 + 1775413 * 2 ^ 59
def prefixEnd_1775413 : Nat := 4983230072969 + 3 ^ 40 * 1775413 * 2
def baseEnd_1775413 : Nat := 607760152827311614781687

theorem tailTrace_1775413 : CollatzResearch.WordTrace tailWord_1775413 prefixEnd_1775413 607760152827311614781687 := by
  unfold tailWord_1775413
  simp only [CollatzResearch.WordTrace]
  refine ⟨64754631916989392245218893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43169754611326261496812595 64754631916989392245218893)
  ·
    refine ⟨24282986968871022091957085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64754631916989392245218893 24282986968871022091957085)
    ·
      refine ⟨9106120113326633284483907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24282986968871022091957085 9106120113326633284483907)
      ·
        refine ⟨13659180169989949926725861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9106120113326633284483907 13659180169989949926725861)
        ·
          refine ⟨2561096281873115611261099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13659180169989949926725861 2561096281873115611261099)
          ·
            refine ⟨3841644422809673416891649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2561096281873115611261099 3841644422809673416891649)
            ·
              refine ⟨2881233317107255062668737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3841644422809673416891649 2881233317107255062668737)
              ·
                refine ⟨2160924987830441297001553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2881233317107255062668737 2160924987830441297001553)
                ·
                  refine ⟨1620693740872830972751165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2160924987830441297001553 1620693740872830972751165)
                  ·
                    refine ⟨607760152827311614781687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1620693740872830972751165 607760152827311614781687)
                    ·
                      rfl

theorem cell22_1775413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_1775413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775413 prefixEnd_1775413 := by exact prefixLift 1775413
  have htrace : WordTrace (prefixWord ++ tailWord_1775413) baseStart_1775413 baseEnd_1775413 := by
    simpa [prefixWord, tailWord_1775413, baseEnd_1775413] using wordTrace_append hprefix tailTrace_1775413
  have hstable : (prefixWord ++ tailWord_1775413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775413).length < 2 ^ (prefixWord ++ tailWord_1775413).sum := by decide
  have hdescent : baseEnd_1775413 < baseStart_1775413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775430 : List Nat := [6, 1, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_1775430 : Nat := 118140960795 + 1775430 * 2 ^ 59
def prefixEnd_1775430 : Nat := 4983230072969 + 3 ^ 40 * 1775430 * 2
def baseEnd_1775430 : Nat := 607765972274729237106635

theorem tailTrace_1775430 : CollatzResearch.WordTrace tailWord_1775430 prefixEnd_1775430 607765972274729237106635 := by
  unfold tailWord_1775430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023601623685243879643367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43170167971951869432391829 2023601623685243879643367)
  ·
    refine ⟨3035402435527865819465051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2023601623685243879643367 3035402435527865819465051)
    ·
      refine ⟨4553103653291798729197577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3035402435527865819465051 4553103653291798729197577)
      ·
        refine ⟨3414827739968849046898183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4553103653291798729197577 3414827739968849046898183)
        ·
          refine ⟨5122241609953273570347275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3414827739968849046898183 5122241609953273570347275)
          ·
            refine ⟨7683362414929910355520913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5122241609953273570347275 7683362414929910355520913)
            ·
              refine ⟨5762521811197432766640685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7683362414929910355520913 5762521811197432766640685)
              ·
                refine ⟨2160945679199037287490257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5762521811197432766640685 2160945679199037287490257)
                ·
                  refine ⟨1620709259399277965617693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2160945679199037287490257 1620709259399277965617693)
                  ·
                    refine ⟨607765972274729237106635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1620709259399277965617693 607765972274729237106635)
                    ·
                      rfl

theorem cell22_1775430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_1775430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775430 prefixEnd_1775430 := by exact prefixLift 1775430
  have htrace : WordTrace (prefixWord ++ tailWord_1775430) baseStart_1775430 baseEnd_1775430 := by
    simpa [prefixWord, tailWord_1775430, baseEnd_1775430] using wordTrace_append hprefix tailTrace_1775430
  have hstable : (prefixWord ++ tailWord_1775430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775430).length < 2 ^ (prefixWord ++ tailWord_1775430).sum := by decide
  have hdescent : baseEnd_1775430 < baseStart_1775430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775441 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 3, 3]
def baseStart_1775441 : Nat := 118140960795 + 1775441 * 2 ^ 59
def prefixEnd_1775441 : Nat := 4983230072969 + 3 ^ 40 * 1775441 * 2
def baseEnd_1775441 : Nat := 607769737799528875081601

theorem tailTrace_1775441 : CollatzResearch.WordTrace tailWord_1775441 prefixEnd_1775441 607769737799528875081601 := by
  unfold tailWord_1775441
  simp only [CollatzResearch.WordTrace]
  refine ⟨64755653160887953027238177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43170435440591968684825451 64755653160887953027238177)
  ·
    refine ⟨48566739870665964770428633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64755653160887953027238177 48566739870665964770428633)
    ·
      refine ⟨36425054902999473577821475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48566739870665964770428633 36425054902999473577821475)
      ·
        refine ⟨54637582354499210366732213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36425054902999473577821475 54637582354499210366732213)
        ·
          refine ⟨5122273345734300971881145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54637582354499210366732213 5122273345734300971881145)
          ·
            refine ⟨3841705009300725728910859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5122273345734300971881145 3841705009300725728910859)
            ·
              refine ⟨5762557513951088593366289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3841705009300725728910859 5762557513951088593366289)
              ·
                refine ⟨4321918135463316445024717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5762557513951088593366289 4321918135463316445024717)
                ·
                  refine ⟨1620719300798743666884269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4321918135463316445024717 1620719300798743666884269)
                  ·
                    refine ⟨607769737799528875081601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1620719300798743666884269 607769737799528875081601)
                    ·
                      rfl

theorem cell22_1775441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_1775441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775441 prefixEnd_1775441 := by exact prefixLift 1775441
  have htrace : WordTrace (prefixWord ++ tailWord_1775441) baseStart_1775441 baseEnd_1775441 := by
    simpa [prefixWord, tailWord_1775441, baseEnd_1775441] using wordTrace_append hprefix tailTrace_1775441
  have hstable : (prefixWord ++ tailWord_1775441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775441).length < 2 ^ (prefixWord ++ tailWord_1775441).sum := by decide
  have hdescent : baseEnd_1775441 < baseStart_1775441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775469 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_1775469 : Nat := 118140960795 + 1775469 * 2 ^ 59
def prefixEnd_1775469 : Nat := 4983230072969 + 3 ^ 40 * 1775469 * 2
def baseEnd_1775469 : Nat := 607779322771746135381515

theorem tailTrace_1775469 : CollatzResearch.WordTrace tailWord_1775469 prefixEnd_1775469 607779322771746135381515 := by
  unfold tailWord_1775469
  simp only [CollatzResearch.WordTrace]
  refine ⟨64756674404786513809257461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43171116269857675872838307 64756674404786513809257461)
  ·
    refine ⟨6070938225448735669617887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64756674404786513809257461 6070938225448735669617887)
    ·
      refine ⟨9106407338173103504426831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6070938225448735669617887 9106407338173103504426831)
      ·
        refine ⟨13659611007259655256640247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9106407338173103504426831 13659611007259655256640247)
        ·
          refine ⟨20489416510889482884960371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13659611007259655256640247 20489416510889482884960371)
          ·
            refine ⟨30734124766334224327440557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20489416510889482884960371 30734124766334224327440557)
            ·
              refine ⟨11525296787375334122790209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30734124766334224327440557 11525296787375334122790209)
              ·
                refine ⟨8643972590531500592092657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11525296787375334122790209 8643972590531500592092657)
                ·
                  refine ⟨6482979442898625444069493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8643972590531500592092657 6482979442898625444069493)
                  ·
                    refine ⟨607779322771746135381515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6482979442898625444069493 607779322771746135381515)
                    ·
                      rfl

theorem cell22_1775469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_1775469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775469 prefixEnd_1775469 := by exact prefixLift 1775469
  have htrace : WordTrace (prefixWord ++ tailWord_1775469) baseStart_1775469 baseEnd_1775469 := by
    simpa [prefixWord, tailWord_1775469, baseEnd_1775469] using wordTrace_append hprefix tailTrace_1775469
  have hstable : (prefixWord ++ tailWord_1775469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775469).length < 2 ^ (prefixWord ++ tailWord_1775469).sum := by decide
  have hdescent : baseEnd_1775469 < baseStart_1775469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775544 : List Nat := [2, 1, 2, 1, 2, 3, 4, 7]
def baseStart_1775544 : Nat := 118140960795 + 1775544 * 2 ^ 59
def prefixEnd_1775544 : Nat := 4983230072969 + 3 ^ 40 * 1775544 * 2
def baseEnd_1775544 : Nat := 67533888533830104417365

theorem tailTrace_1775544 : CollatzResearch.WordTrace tailWord_1775544 prefixEnd_1775544 67533888533830104417365 := by
  unfold tailWord_1775544
  simp only [CollatzResearch.WordTrace]
  refine ⟨32379704939757400809118843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43172939919676534412158457 32379704939757400809118843)
  ·
    refine ⟨48569557409636101213678265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32379704939757400809118843 48569557409636101213678265)
    ·
      refine ⟨36427168057227075910258699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48569557409636101213678265 36427168057227075910258699)
      ·
        refine ⟨54640752085840613865388049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36427168057227075910258699 54640752085840613865388049)
        ·
          refine ⟨40980564064380460399041037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54640752085840613865388049 40980564064380460399041037)
          ·
            refine ⟨15367711524142672649640389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40980564064380460399041037 15367711524142672649640389)
            ·
              refine ⟨2881445910776751121807573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15367711524142672649640389 2881445910776751121807573)
              ·
                refine ⟨67533888533830104417365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2881445910776751121807573 67533888533830104417365)
                ·
                  rfl

theorem cell22_1775544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 7].length) (baseStart_1775544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775544 prefixEnd_1775544 := by exact prefixLift 1775544
  have htrace : WordTrace (prefixWord ++ tailWord_1775544) baseStart_1775544 baseEnd_1775544 := by
    simpa [prefixWord, tailWord_1775544, baseEnd_1775544] using wordTrace_append hprefix tailTrace_1775544
  have hstable : (prefixWord ++ tailWord_1775544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775544).length < 2 ^ (prefixWord ++ tailWord_1775544).sum := by decide
  have hdescent : baseEnd_1775544 < baseStart_1775544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775651 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 6]
def baseStart_1775651 : Nat := 118140960795 + 1775651 * 2 ^ 59
def prefixEnd_1775651 : Nat := 4983230072969 + 3 ^ 40 * 1775651 * 2
def baseEnd_1775651 : Nat := 202613875030386109110319

theorem tailTrace_1775651 : CollatzResearch.WordTrace tailWord_1775651 prefixEnd_1775651 202613875030386109110319 := by
  unfold tailWord_1775651
  simp only [CollatzResearch.WordTrace]
  refine ⟨64763312490127158892382807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43175541660084772594921871 64763312490127158892382807)
  ·
    refine ⟨97144968735190738338574211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64763312490127158892382807 97144968735190738338574211)
    ·
      refine ⟨145717453102786107507861317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97144968735190738338574211 145717453102786107507861317)
      ·
        refine ⟨27322022456772395157723997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145717453102786107507861317 27322022456772395157723997)
        ·
          refine ⟨10245758421289648184146499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27322022456772395157723997 10245758421289648184146499)
          ·
            refine ⟨15368637631934472276219749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10245758421289648184146499 15368637631934472276219749)
            ·
              refine ⟨2881619555987713551791203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15368637631934472276219749 2881619555987713551791203)
              ·
                refine ⟨4322429333981570327686805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2881619555987713551791203 4322429333981570327686805)
                ·
                  refine ⟨202613875030386109110319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4322429333981570327686805 202613875030386109110319)
                  ·
                    rfl

theorem cell22_1775651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 6].length) (baseStart_1775651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775651 prefixEnd_1775651 := by exact prefixLift 1775651
  have htrace : WordTrace (prefixWord ++ tailWord_1775651) baseStart_1775651 baseEnd_1775651 := by
    simpa [prefixWord, tailWord_1775651, baseEnd_1775651] using wordTrace_append hprefix tailTrace_1775651
  have hstable : (prefixWord ++ tailWord_1775651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775651).length < 2 ^ (prefixWord ++ tailWord_1775651).sum := by decide
  have hdescent : baseEnd_1775651 < baseStart_1775651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775670 : List Nat := [5, 1, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_1775670 : Nat := 118140960795 + 1775670 * 2 ^ 59
def prefixEnd_1775670 : Nat := 4983230072969 + 3 ^ 40 * 1775670 * 2
def baseEnd_1775670 : Nat := 607848129179448611105899

theorem tailTrace_1775670 : CollatzResearch.WordTrace tailWord_1775670 prefixEnd_1775670 607848129179448611105899 := by
  unfold tailWord_1775670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4047750342316145321082779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43176003651372216758216309 4047750342316145321082779)
  ·
    refine ⟨6071625513474217981624169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4047750342316145321082779 6071625513474217981624169)
    ·
      refine ⟨4553719135105663486218127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6071625513474217981624169 4553719135105663486218127)
      ·
        refine ⟨6830578702658495229327191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4553719135105663486218127 6830578702658495229327191)
        ·
          refine ⟨10245868053987742843990787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6830578702658495229327191 10245868053987742843990787)
          ·
            refine ⟨15368802080981614265986181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10245868053987742843990787 15368802080981614265986181)
            ·
              refine ⟨2881650390184052674872409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15368802080981614265986181 2881650390184052674872409)
              ·
                refine ⟨2161237792638039506154307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2881650390184052674872409 2161237792638039506154307)
                ·
                  refine ⟨3241856688957059259231461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2161237792638039506154307 3241856688957059259231461)
                  ·
                    refine ⟨607848129179448611105899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3241856688957059259231461 607848129179448611105899)
                    ·
                      rfl

theorem cell22_1775670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_1775670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775670 prefixEnd_1775670 := by exact prefixLift 1775670
  have htrace : WordTrace (prefixWord ++ tailWord_1775670) baseStart_1775670 baseEnd_1775670 := by
    simpa [prefixWord, tailWord_1775670, baseEnd_1775670] using wordTrace_append hprefix tailTrace_1775670
  have hstable : (prefixWord ++ tailWord_1775670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775670).length < 2 ^ (prefixWord ++ tailWord_1775670).sum := by decide
  have hdescent : baseEnd_1775670 < baseStart_1775670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775702 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_1775702 : Nat := 118140960795 + 1775702 * 2 ^ 59
def prefixEnd_1775702 : Nat := 4983230072969 + 3 ^ 40 * 1775702 * 2
def baseEnd_1775702 : Nat := 202619694477803731435267

theorem tailTrace_1775702 : CollatzResearch.WordTrace tailWord_1775702 prefixEnd_1775702 202619694477803731435267 := by
  unfold tailWord_1775702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4047823288308899662655585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43176781741961596401659573 4047823288308899662655585)
  ·
    refine ⟨3035867466231674746991689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4047823288308899662655585 3035867466231674746991689)
    ·
      refine ⟨2276900599673756060243767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3035867466231674746991689 2276900599673756060243767)
      ·
        refine ⟨3415350899510634090365651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2276900599673756060243767 3415350899510634090365651)
        ·
          refine ⟨5123026349265951135548477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3415350899510634090365651 5123026349265951135548477)
          ·
            refine ⟨1921134880974731675830679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5123026349265951135548477 1921134880974731675830679)
            ·
              refine ⟨2881702321462097513746019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1921134880974731675830679 2881702321462097513746019)
              ·
                refine ⟨4322553482193146270619029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2881702321462097513746019 4322553482193146270619029)
                ·
                  refine ⟨202619694477803731435267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4322553482193146270619029 202619694477803731435267)
                  ·
                    rfl

theorem cell22_1775702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_1775702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775702 prefixEnd_1775702 := by exact prefixLift 1775702
  have htrace : WordTrace (prefixWord ++ tailWord_1775702) baseStart_1775702 baseEnd_1775702 := by
    simpa [prefixWord, tailWord_1775702, baseEnd_1775702] using wordTrace_append hprefix tailTrace_1775702
  have hstable : (prefixWord ++ tailWord_1775702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775702).length < 2 ^ (prefixWord ++ tailWord_1775702).sum := by decide
  have hdescent : baseEnd_1775702 < baseStart_1775702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775717 : List Nat := [1, 3, 1, 3, 2, 4, 2, 1, 2, 3]
def baseStart_1775717 : Nat := 118140960795 + 1775717 * 2 ^ 59
def prefixEnd_1775717 : Nat := 4983230072969 + 3 ^ 40 * 1775717 * 2
def baseEnd_1775717 : Nat := 607864218239956155180755

theorem tailTrace_1775717 : CollatzResearch.WordTrace tailWord_1775717 prefixEnd_1775717 607864218239956155180755 := by
  unfold tailWord_1775717
  simp only [CollatzResearch.WordTrace]
  refine ⟨64765719707888052164285405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43177146471925368109523603 64765719707888052164285405)
  ·
    refine ⟨24287144890458019561607027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64765719707888052164285405 24287144890458019561607027)
    ·
      refine ⟨36430717335687029342410541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24287144890458019561607027 36430717335687029342410541)
      ·
        refine ⟨13661519000882636003403953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36430717335687029342410541 13661519000882636003403953)
        ·
          refine ⟨10246139250661977002552965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13661519000882636003403953 10246139250661977002552965)
          ·
            refine ⟨1921151109499120687978681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10246139250661977002552965 1921151109499120687978681)
            ·
              refine ⟨1440863332124340515984011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1921151109499120687978681 1440863332124340515984011)
              ·
                refine ⟨2161294998186510773976017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440863332124340515984011 2161294998186510773976017)
                ·
                  refine ⟨1620971248639883080482013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2161294998186510773976017 1620971248639883080482013)
                  ·
                    refine ⟨607864218239956155180755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1620971248639883080482013 607864218239956155180755)
                    ·
                      rfl

theorem cell22_1775717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_1775717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775717 prefixEnd_1775717 := by exact prefixLift 1775717
  have htrace : WordTrace (prefixWord ++ tailWord_1775717) baseStart_1775717 baseEnd_1775717 := by
    simpa [prefixWord, tailWord_1775717, baseEnd_1775717] using wordTrace_append hprefix tailTrace_1775717
  have hstable : (prefixWord ++ tailWord_1775717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775717).length < 2 ^ (prefixWord ++ tailWord_1775717).sum := by decide
  have hdescent : baseEnd_1775717 < baseStart_1775717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775762 : List Nat := [3, 2, 3, 1, 1, 1, 3, 4, 1, 3]
def baseStart_1775762 : Nat := 118140960795 + 1775762 * 2 ^ 59
def prefixEnd_1775762 : Nat := 4983230072969 + 3 ^ 40 * 1775762 * 2
def baseEnd_1775762 : Nat := 607879622659591037805617

theorem tailTrace_1775762 : CollatzResearch.WordTrace tailWord_1775762 prefixEnd_1775762 607879622659591037805617 := by
  unfold tailWord_1775762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16191840248181256212418385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43178240661816683233115693 16191840248181256212418385)
  ·
    refine ⟨12143880186135942159313789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16191840248181256212418385 12143880186135942159313789)
    ·
      refine ⟨4553955069800978309742671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12143880186135942159313789 4553955069800978309742671)
      ·
        refine ⟨6830932604701467464614007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4553955069800978309742671 6830932604701467464614007)
        ·
          refine ⟨10246398907052201196921011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6830932604701467464614007 10246398907052201196921011)
          ·
            refine ⟨15369598360578301795381517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10246398907052201196921011 15369598360578301795381517)
            ·
              refine ⟨5763599385216863173268069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15369598360578301795381517 5763599385216863173268069)
              ·
                refine ⟨1080674884728161844987763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5763599385216863173268069 1080674884728161844987763)
                ·
                  refine ⟨1621012327092242767481645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1080674884728161844987763 1621012327092242767481645)
                  ·
                    refine ⟨607879622659591037805617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1621012327092242767481645 607879622659591037805617)
                    ·
                      rfl

theorem cell22_1775762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_1775762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775762 prefixEnd_1775762 := by exact prefixLift 1775762
  have htrace : WordTrace (prefixWord ++ tailWord_1775762) baseStart_1775762 baseEnd_1775762 := by
    simpa [prefixWord, tailWord_1775762, baseEnd_1775762] using wordTrace_append hprefix tailTrace_1775762
  have hstable : (prefixWord ++ tailWord_1775762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775762).length < 2 ^ (prefixWord ++ tailWord_1775762).sum := by decide
  have hdescent : baseEnd_1775762 < baseStart_1775762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775771 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 5, 4]
def baseStart_1775771 : Nat := 118140960795 + 1775771 * 2 ^ 59
def prefixEnd_1775771 : Nat := 4983230072969 + 3 ^ 40 * 1775771 * 2
def baseEnd_1775771 : Nat := 607882703543518014330589

theorem tailTrace_1775771 : CollatzResearch.WordTrace tailWord_1775771 prefixEnd_1775771 607882703543518014330589 := by
  unfold tailWord_1775771
  simp only [CollatzResearch.WordTrace]
  refine ⟨64767689249692419386751167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43178459499794946257834111 64767689249692419386751167)
  ·
    refine ⟨97151533874538629080126751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64767689249692419386751167 97151533874538629080126751)
    ·
      refine ⟨145727300811807943620190127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97151533874538629080126751 145727300811807943620190127)
      ·
        refine ⟨218590951217711915430285191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145727300811807943620190127 218590951217711915430285191)
        ·
          refine ⟨327886426826567873145427787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218590951217711915430285191 327886426826567873145427787)
          ·
            refine ⟨491829640239851809718141681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327886426826567873145427787 491829640239851809718141681)
            ·
              refine ⟨368872230179888857288606261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491829640239851809718141681 368872230179888857288606261)
              ·
                refine ⟨34581771579364580370806837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 368872230179888857288606261 34581771579364580370806837)
                ·
                  refine ⟨3242041085565429409763141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34581771579364580370806837 3242041085565429409763141)
                  ·
                    refine ⟨607882703543518014330589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3242041085565429409763141 607882703543518014330589)
                    ·
                      rfl

theorem cell22_1775771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 4].length) (baseStart_1775771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775771 prefixEnd_1775771 := by exact prefixLift 1775771
  have htrace : WordTrace (prefixWord ++ tailWord_1775771) baseStart_1775771 baseEnd_1775771 := by
    simpa [prefixWord, tailWord_1775771, baseEnd_1775771] using wordTrace_append hprefix tailTrace_1775771
  have hstable : (prefixWord ++ tailWord_1775771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775771).length < 2 ^ (prefixWord ++ tailWord_1775771).sum := by decide
  have hdescent : baseEnd_1775771 < baseStart_1775771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775773 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1775773 : Nat := 118140960795 + 1775773 * 2 ^ 59
def prefixEnd_1775773 : Nat := 4983230072969 + 3 ^ 40 * 1775773 * 2
def baseEnd_1775773 : Nat := 607883388184390675780583

theorem tailTrace_1775773 : CollatzResearch.WordTrace tailWord_1775773 prefixEnd_1775773 607883388184390675780583 := by
  unfold tailWord_1775773
  simp only [CollatzResearch.WordTrace]
  refine ⟨64767762195685173728323973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43178508130456782485549315 64767762195685173728323973)
  ·
    refine ⟨12143955411690970074060745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64767762195685173728323973 12143955411690970074060745)
    ·
      refine ⟨9107966558768227555545559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12143955411690970074060745 9107966558768227555545559)
      ·
        refine ⟨13661949838152341333318339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9107966558768227555545559 13661949838152341333318339)
        ·
          refine ⟨20492924757228511999977509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13661949838152341333318339 20492924757228511999977509)
          ·
            refine ⟨3842423391980345999995783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20492924757228511999977509 3842423391980345999995783)
            ·
              refine ⟨5763635087970518999993675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3842423391980345999995783 5763635087970518999993675)
              ·
                refine ⟨8645452631955778499990513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5763635087970518999993675 8645452631955778499990513)
                ·
                  refine ⟨6484089473966833874992885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8645452631955778499990513 6484089473966833874992885)
                  ·
                    refine ⟨607883388184390675780583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6484089473966833874992885 607883388184390675780583)
                    ·
                      rfl

theorem cell22_1775773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1775773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775773 prefixEnd_1775773 := by exact prefixLift 1775773
  have htrace : WordTrace (prefixWord ++ tailWord_1775773) baseStart_1775773 baseEnd_1775773 := by
    simpa [prefixWord, tailWord_1775773, baseEnd_1775773] using wordTrace_append hprefix tailTrace_1775773
  have hstable : (prefixWord ++ tailWord_1775773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775773).length < 2 ^ (prefixWord ++ tailWord_1775773).sum := by decide
  have hdescent : baseEnd_1775773 < baseStart_1775773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775809 : List Nat := [1, 2, 6, 1, 3, 1, 1, 2, 5]
def baseStart_1775809 : Nat := 118140960795 + 1775809 * 2 ^ 59
def prefixEnd_1775809 : Nat := 4983230072969 + 3 ^ 40 * 1775809 * 2
def baseEnd_1775809 : Nat := 202631903906699527293491

theorem tailTrace_1775809 : CollatzResearch.WordTrace tailWord_1775809 prefixEnd_1775809 202631903906699527293491 := by
  unfold tailWord_1775809
  simp only [CollatzResearch.WordTrace]
  refine ⟨64769075223554751876634481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43179383482369834584422987 64769075223554751876634481)
  ·
    refine ⟨48576806417666063907475861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64769075223554751876634481 48576806417666063907475861)
    ·
      refine ⟨2277037800828096745662931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48576806417666063907475861 2277037800828096745662931)
      ·
        refine ⟨3415556701242145118494397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2277037800828096745662931 3415556701242145118494397)
        ·
          refine ⟨1280833762965804419435399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3415556701242145118494397 1280833762965804419435399)
          ·
            refine ⟨1921250644448706629153099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280833762965804419435399 1921250644448706629153099)
            ·
              refine ⟨2881875966673059943729649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1921250644448706629153099 2881875966673059943729649)
              ·
                refine ⟨2161406975004794957797237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2881875966673059943729649 2161406975004794957797237)
                ·
                  refine ⟨202631903906699527293491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2161406975004794957797237 202631903906699527293491)
                  ·
                    rfl

theorem cell22_1775809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 5].length) (baseStart_1775809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775809 prefixEnd_1775809 := by exact prefixLift 1775809
  have htrace : WordTrace (prefixWord ++ tailWord_1775809) baseStart_1775809 baseEnd_1775809 := by
    simpa [prefixWord, tailWord_1775809, baseEnd_1775809] using wordTrace_append hprefix tailTrace_1775809
  have hstable : (prefixWord ++ tailWord_1775809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775809).length < 2 ^ (prefixWord ++ tailWord_1775809).sum := by decide
  have hdescent : baseEnd_1775809 < baseStart_1775809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775831 : List Nat := [1, 1, 3, 2, 1, 2, 1, 11]
def baseStart_1775831 : Nat := 118140960795 + 1775831 * 2 ^ 59
def prefixEnd_1775831 : Nat := 4983230072969 + 3 ^ 40 * 1775831 * 2
def baseEnd_1775831 : Nat := 67544804752188650870045

theorem tailTrace_1775831 : CollatzResearch.WordTrace tailWord_1775831 prefixEnd_1775831 67544804752188650870045 := by
  unfold tailWord_1775831
  simp only [CollatzResearch.WordTrace]
  refine ⟨64769877629475049633935347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43179918419650033089290231 64769877629475049633935347)
  ·
    refine ⟨97154816444212574450903021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64769877629475049633935347 97154816444212574450903021)
    ·
      refine ⟨36433056166579715419088633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97154816444212574450903021 36433056166579715419088633)
      ·
        refine ⟨27324792124934786564316475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36433056166579715419088633 27324792124934786564316475)
        ·
          refine ⟨40987188187402179846474713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27324792124934786564316475 40987188187402179846474713)
          ·
            refine ⟨30740391140551634884856035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40987188187402179846474713 30740391140551634884856035)
            ·
              refine ⟨46110586710827452327284053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30740391140551634884856035 46110586710827452327284053)
              ·
                refine ⟨67544804752188650870045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 46110586710827452327284053 67544804752188650870045)
                ·
                  rfl

theorem cell22_1775831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 11].length) (baseStart_1775831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775831 prefixEnd_1775831 := by exact prefixLift 1775831
  have htrace : WordTrace (prefixWord ++ tailWord_1775831) baseStart_1775831 baseEnd_1775831 := by
    simpa [prefixWord, tailWord_1775831, baseEnd_1775831] using wordTrace_append hprefix tailTrace_1775831
  have hstable : (prefixWord ++ tailWord_1775831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775831).length < 2 ^ (prefixWord ++ tailWord_1775831).sum := by decide
  have hdescent : baseEnd_1775831 < baseStart_1775831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775848 : List Nat := [2, 1, 4, 1, 2, 3, 1, 8]
def baseStart_1775848 : Nat := 118140960795 + 1775848 * 2 ^ 59
def prefixEnd_1775848 : Nat := 4983230072969 + 3 ^ 40 * 1775848 * 2
def baseEnd_1775848 : Nat := 67545451357457275572817

theorem tailTrace_1775848 : CollatzResearch.WordTrace tailWord_1775848 prefixEnd_1775848 67545451357457275572817 := by
  unfold tailWord_1775848
  simp only [CollatzResearch.WordTrace]
  refine ⟨32385248835206730768652099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43180331780275641024869465 32385248835206730768652099)
  ·
    refine ⟨48577873252810096152978149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32385248835206730768652099 48577873252810096152978149)
    ·
      refine ⟨9108351234901893028683403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48577873252810096152978149 9108351234901893028683403)
      ·
        refine ⟨13662526852352839543025105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9108351234901893028683403 13662526852352839543025105)
        ·
          refine ⟨10246895139264629657268829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13662526852352839543025105 10246895139264629657268829)
          ·
            refine ⟨3842585677224236121475811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10246895139264629657268829 3842585677224236121475811)
            ·
              refine ⟨5763878515836354182213717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3842585677224236121475811 5763878515836354182213717)
              ·
                refine ⟨67545451357457275572817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5763878515836354182213717 67545451357457275572817)
                ·
                  rfl

theorem cell22_1775848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 8].length) (baseStart_1775848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775848 prefixEnd_1775848 := by exact prefixLift 1775848
  have htrace : WordTrace (prefixWord ++ tailWord_1775848) baseStart_1775848 baseEnd_1775848 := by
    simpa [prefixWord, tailWord_1775848, baseEnd_1775848] using wordTrace_append hprefix tailTrace_1775848
  have hstable : (prefixWord ++ tailWord_1775848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775848).length < 2 ^ (prefixWord ++ tailWord_1775848).sum := by decide
  have hdescent : baseEnd_1775848 < baseStart_1775848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775972 : List Nat := [2, 3, 1, 1, 3, 1, 4, 3, 4]
def baseStart_1775972 : Nat := 118140960795 + 1775972 * 2 ^ 59
def prefixEnd_1775972 : Nat := 4983230072969 + 3 ^ 40 * 1775972 * 2
def baseEnd_1775972 : Nat := 202650503317073496684991

theorem tailTrace_1775972 : CollatzResearch.WordTrace tailWord_1775972 prefixEnd_1775972 202650503317073496684991 := by
  unfold tailWord_1775972
  simp only [CollatzResearch.WordTrace]
  refine ⟨32387510160982115357409085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43183346881309487143212113 32387510160982115357409085)
  ·
    refine ⟨12145316310368293259028407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32387510160982115357409085 12145316310368293259028407)
    ·
      refine ⟨18217974465552439888542611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12145316310368293259028407 18217974465552439888542611)
      ·
        refine ⟨27326961698328659832813917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18217974465552439888542611 27326961698328659832813917)
        ·
          refine ⟨10247610636873247437305219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27326961698328659832813917 10247610636873247437305219)
          ·
            refine ⟨15371415955309871155957829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10247610636873247437305219 15371415955309871155957829)
            ·
              refine ⟨2882140491620600841742093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15371415955309871155957829 2882140491620600841742093)
              ·
                refine ⟨1080802684357725315653285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2882140491620600841742093 1080802684357725315653285)
                ·
                  refine ⟨202650503317073496684991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1080802684357725315653285 202650503317073496684991)
                  ·
                    rfl

theorem cell22_1775972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_1775972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775972 prefixEnd_1775972 := by exact prefixLift 1775972
  have htrace : WordTrace (prefixWord ++ tailWord_1775972) baseStart_1775972 baseEnd_1775972 := by
    simpa [prefixWord, tailWord_1775972, baseEnd_1775972] using wordTrace_append hprefix tailTrace_1775972
  have hstable : (prefixWord ++ tailWord_1775972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775972).length < 2 ^ (prefixWord ++ tailWord_1775972).sum := by decide
  have hdescent : baseEnd_1775972 < baseStart_1775972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776004 : List Nat := [2, 3, 2, 1, 1, 2, 5, 1, 2, 3]
def baseStart_1776004 : Nat := 118140960795 + 1776004 * 2 ^ 59
def prefixEnd_1776004 : Nat := 4983230072969 + 3 ^ 40 * 1776004 * 2
def baseEnd_1776004 : Nat := 607962464205183073254875

theorem tailTrace_1776004 : CollatzResearch.WordTrace tailWord_1776004 prefixEnd_1776004 607962464205183073254875 := by
  unfold tailWord_1776004
  simp only [CollatzResearch.WordTrace]
  refine ⟨32388093728924150089991533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43184124971898866786655377 32388093728924150089991533)
  ·
    refine ⟨12145535148346556283746825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32388093728924150089991533 12145535148346556283746825)
    ·
      refine ⟨9109151361259917212810119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12145535148346556283746825 9109151361259917212810119)
      ·
        refine ⟨13663727041889875819215179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9109151361259917212810119 13663727041889875819215179)
        ·
          refine ⟨20495590562834813728822769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13663727041889875819215179 20495590562834813728822769)
          ·
            refine ⟨15371692922126110296617077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20495590562834813728822769 15371692922126110296617077)
            ·
              refine ⟨1441096211449322840307851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15371692922126110296617077 1441096211449322840307851)
              ·
                refine ⟨2161644317173984260461777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1441096211449322840307851 2161644317173984260461777)
                ·
                  refine ⟨1621233237880488195346333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2161644317173984260461777 1621233237880488195346333)
                  ·
                    refine ⟨607962464205183073254875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1621233237880488195346333 607962464205183073254875)
                    ·
                      rfl

theorem cell22_1776004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_1776004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776004 prefixEnd_1776004 := by exact prefixLift 1776004
  have htrace : WordTrace (prefixWord ++ tailWord_1776004) baseStart_1776004 baseEnd_1776004 := by
    simpa [prefixWord, tailWord_1776004, baseEnd_1776004] using wordTrace_append hprefix tailTrace_1776004
  have hstable : (prefixWord ++ tailWord_1776004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776004).length < 2 ^ (prefixWord ++ tailWord_1776004).sum := by decide
  have hdescent : baseEnd_1776004 < baseStart_1776004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776049 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 3, 3]
def baseStart_1776049 : Nat := 118140960795 + 1776049 * 2 ^ 59
def prefixEnd_1776049 : Nat := 4983230072969 + 3 ^ 40 * 1776049 * 2
def baseEnd_1776049 : Nat := 607977868624817955879737

theorem tailTrace_1776049 : CollatzResearch.WordTrace tailWord_1776049 prefixEnd_1776049 607977868624817955879737 := by
  unfold tailWord_1776049
  simp only [CollatzResearch.WordTrace]
  refine ⟨64777828742685272865371201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43185219161790181910247467 64777828742685272865371201)
  ·
    refine ⟨48583371557013954649028401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64777828742685272865371201 48583371557013954649028401)
    ·
      refine ⟨36437528667760465986771301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48583371557013954649028401 36437528667760465986771301)
      ·
        refine ⟨6832036625205087372519619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36437528667760465986771301 6832036625205087372519619)
        ·
          refine ⟨10248054937807631058779429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6832036625205087372519619 10248054937807631058779429)
          ·
            refine ⟨1921510300838930823521143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10248054937807631058779429 1921510300838930823521143)
            ·
              refine ⟨2882265451258396235281715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1921510300838930823521143 2882265451258396235281715)
              ·
                refine ⟨4323398176887594352922573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2882265451258396235281715 4323398176887594352922573)
                ·
                  refine ⟨1621274316332847882345965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4323398176887594352922573 1621274316332847882345965)
                  ·
                    refine ⟨607977868624817955879737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1621274316332847882345965 607977868624817955879737)
                    ·
                      rfl

theorem cell22_1776049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_1776049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776049 prefixEnd_1776049 := by exact prefixLift 1776049
  have htrace : WordTrace (prefixWord ++ tailWord_1776049) baseStart_1776049 baseEnd_1776049 := by
    simpa [prefixWord, tailWord_1776049, baseEnd_1776049] using wordTrace_append hprefix tailTrace_1776049
  have hstable : (prefixWord ++ tailWord_1776049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776049).length < 2 ^ (prefixWord ++ tailWord_1776049).sum := by decide
  have hdescent : baseEnd_1776049 < baseStart_1776049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776107 : List Nat := [1, 1, 1, 1, 2, 3, 5, 4, 4]
def baseStart_1776107 : Nat := 118140960795 + 1776107 * 2 ^ 59
def prefixEnd_1776107 : Nat := 4983230072969 + 3 ^ 40 * 1776107 * 2
def baseEnd_1776107 : Nat := 202665907736708379309853

theorem tailTrace_1776107 : CollatzResearch.WordTrace tailWord_1776107 prefixEnd_1776107 202665907736708379309853 := by
  unfold tailWord_1776107
  simp only [CollatzResearch.WordTrace]
  refine ⟨64779944176475148770982575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43186629450983432513988383 64779944176475148770982575)
  ·
    refine ⟨97169916264712723156473863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64779944176475148770982575 97169916264712723156473863)
    ·
      refine ⟨145754874397069084734710795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97169916264712723156473863 145754874397069084734710795)
      ·
        refine ⟨218632311595603627102066193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145754874397069084734710795 218632311595603627102066193)
        ·
          refine ⟨163974233696702720326549645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218632311595603627102066193 163974233696702720326549645)
          ·
            refine ⟨61490337636263520122456117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163974233696702720326549645 61490337636263520122456117)
            ·
              refine ⟨5764719153399705011480261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61490337636263520122456117 5764719153399705011480261)
              ·
                refine ⟨1080884841262444689652549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5764719153399705011480261 1080884841262444689652549)
                ·
                  refine ⟨202665907736708379309853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1080884841262444689652549 202665907736708379309853)
                  ·
                    rfl

theorem cell22_1776107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 4].length) (baseStart_1776107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776107 prefixEnd_1776107 := by exact prefixLift 1776107
  have htrace : WordTrace (prefixWord ++ tailWord_1776107) baseStart_1776107 baseEnd_1776107 := by
    simpa [prefixWord, tailWord_1776107, baseEnd_1776107] using wordTrace_append hprefix tailTrace_1776107
  have hstable : (prefixWord ++ tailWord_1776107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776107).length < 2 ^ (prefixWord ++ tailWord_1776107).sum := by decide
  have hdescent : baseEnd_1776107 < baseStart_1776107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776120 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 1, 6]
def baseStart_1776120 : Nat := 118140960795 + 1776120 * 2 ^ 59
def prefixEnd_1776120 : Nat := 4983230072969 + 3 ^ 40 * 1776120 * 2
def baseEnd_1776120 : Nat := 608002173375797437354519

theorem tailTrace_1776120 : CollatzResearch.WordTrace tailWord_1776120 prefixEnd_1776120 608002173375797437354519 := by
  unfold tailWord_1776120
  simp only [CollatzResearch.WordTrace]
  refine ⟨32390209162714025995602907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43186945550285367994137209 32390209162714025995602907)
  ·
    refine ⟨48585313744071038993404361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32390209162714025995602907 48585313744071038993404361)
    ·
      refine ⟨36438985308053279245053271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48585313744071038993404361 36438985308053279245053271)
      ·
        refine ⟨54658477962079918867579907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36438985308053279245053271 54658477962079918867579907)
        ·
          refine ⟨81987716943119878301369861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54658477962079918867579907 81987716943119878301369861)
          ·
            refine ⟨15372696926834977181506849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81987716943119878301369861 15372696926834977181506849)
            ·
              refine ⟨11529522695126232886130137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15372696926834977181506849 11529522695126232886130137)
              ·
                refine ⟨8647142021344674664597603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11529522695126232886130137 8647142021344674664597603)
                ·
                  refine ⟨12970713032017011996896405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8647142021344674664597603 12970713032017011996896405)
                  ·
                    refine ⟨608002173375797437354519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12970713032017011996896405 608002173375797437354519)
                    ·
                      rfl

theorem cell22_1776120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_1776120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776120 prefixEnd_1776120 := by exact prefixLift 1776120
  have htrace : WordTrace (prefixWord ++ tailWord_1776120) baseStart_1776120 baseEnd_1776120 := by
    simpa [prefixWord, tailWord_1776120, baseEnd_1776120] using wordTrace_append hprefix tailTrace_1776120
  have hstable : (prefixWord ++ tailWord_1776120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776120).length < 2 ^ (prefixWord ++ tailWord_1776120).sum := by decide
  have hdescent : baseEnd_1776120 < baseStart_1776120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776156 : List Nat := [2, 2, 3, 1, 2, 4, 1, 2, 2, 3]
def baseStart_1776156 : Nat := 118140960795 + 1776156 * 2 ^ 59
def prefixEnd_1776156 : Nat := 4983230072969 + 3 ^ 40 * 1776156 * 2
def baseEnd_1776156 : Nat := 608014496911505343454409

theorem tailTrace_1776156 : CollatzResearch.WordTrace tailWord_1776156 prefixEnd_1776156 608014496911505343454409 := by
  unfold tailWord_1776156
  simp only [CollatzResearch.WordTrace]
  refine ⟨32390865676648815069758161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43187820902198420093010881 32390865676648815069758161)
  ·
    refine ⟨24293149257486611302318621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32390865676648815069758161 24293149257486611302318621)
    ·
      refine ⟨9109930971557479238369483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24293149257486611302318621 9109930971557479238369483)
      ·
        refine ⟨13664896457336218857554225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9109930971557479238369483 13664896457336218857554225)
        ·
          refine ⟨10248672343002164143165669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13664896457336218857554225 10248672343002164143165669)
          ·
            refine ⟨1921626064312905776843563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10248672343002164143165669 1921626064312905776843563)
            ·
              refine ⟨2882439096469358665265345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1921626064312905776843563 2882439096469358665265345)
              ·
                refine ⟨2161829322352018998949009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2882439096469358665265345 2161829322352018998949009)
                ·
                  refine ⟨1621371991764014249211757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2161829322352018998949009 1621371991764014249211757)
                  ·
                    refine ⟨608014496911505343454409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1621371991764014249211757 608014496911505343454409)
                    ·
                      rfl

theorem cell22_1776156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_1776156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776156 prefixEnd_1776156 := by exact prefixLift 1776156
  have htrace : WordTrace (prefixWord ++ tailWord_1776156) baseStart_1776156 baseEnd_1776156 := by
    simpa [prefixWord, tailWord_1776156, baseEnd_1776156] using wordTrace_append hprefix tailTrace_1776156
  have hstable : (prefixWord ++ tailWord_1776156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776156).length < 2 ^ (prefixWord ++ tailWord_1776156).sum := by decide
  have hdescent : baseEnd_1776156 < baseStart_1776156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776165 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 1, 8]
def baseStart_1776165 : Nat := 118140960795 + 1776165 * 2 ^ 59
def prefixEnd_1776165 : Nat := 4983230072969 + 3 ^ 40 * 1776165 * 2
def baseEnd_1776165 : Nat := 608017577795432319979381

theorem tailTrace_1776165 : CollatzResearch.WordTrace tailWord_1776165 prefixEnd_1776165 608017577795432319979381 := by
  unfold tailWord_1776165
  simp only [CollatzResearch.WordTrace]
  refine ⟨64782059610265024676593949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43188039740176683117729299 64782059610265024676593949)
  ·
    refine ⟨24293272353849384253722731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64782059610265024676593949 24293272353849384253722731)
    ·
      refine ⟨36439908530774076380584097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24293272353849384253722731 36439908530774076380584097)
      ·
        refine ⟨27329931398080557285438073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36439908530774076380584097 27329931398080557285438073)
        ·
          refine ⟨20497448548560417964078555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27329931398080557285438073 20497448548560417964078555)
          ·
            refine ⟨30746172822840626946117833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20497448548560417964078555 30746172822840626946117833)
            ·
              refine ⟨23059629617130470209588375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30746172822840626946117833 23059629617130470209588375)
              ·
                refine ⟨34589444425695705314382563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23059629617130470209588375 34589444425695705314382563)
                ·
                  refine ⟨51884166638543557971573845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34589444425695705314382563 51884166638543557971573845)
                  ·
                    refine ⟨608017577795432319979381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51884166638543557971573845 608017577795432319979381)
                    ·
                      rfl

theorem cell22_1776165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_1776165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776165 prefixEnd_1776165 := by exact prefixLift 1776165
  have htrace : WordTrace (prefixWord ++ tailWord_1776165) baseStart_1776165 baseEnd_1776165 := by
    simpa [prefixWord, tailWord_1776165, baseEnd_1776165] using wordTrace_append hprefix tailTrace_1776165
  have hstable : (prefixWord ++ tailWord_1776165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776165).length < 2 ^ (prefixWord ++ tailWord_1776165).sum := by decide
  have hdescent : baseEnd_1776165 < baseStart_1776165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776195 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 1, 7]
def baseStart_1776195 : Nat := 118140960795 + 1776195 * 2 ^ 59
def prefixEnd_1776195 : Nat := 4983230072969 + 3 ^ 40 * 1776195 * 2
def baseEnd_1776195 : Nat := 608027847408522241729289

theorem tailTrace_1776195 : CollatzResearch.WordTrace tailWord_1776195 prefixEnd_1776195 608027847408522241729289 := by
  unfold tailWord_1776195
  simp only [CollatzResearch.WordTrace]
  refine ⟨64783153800156339800186039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43188769200104226533457359 64783153800156339800186039)
  ·
    refine ⟨97174730700234509700279059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64783153800156339800186039 97174730700234509700279059)
    ·
      refine ⟨145762096050351764550418589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97174730700234509700279059 145762096050351764550418589)
      ·
        refine ⟨54660786018881911706406971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145762096050351764550418589 54660786018881911706406971)
        ·
          refine ⟨81991179028322867559610457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54660786018881911706406971 81991179028322867559610457)
          ·
            refine ⟨61493384271242150669707843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81991179028322867559610457 61493384271242150669707843)
            ·
              refine ⟨92240076406863226004561765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61493384271242150669707843 92240076406863226004561765)
              ·
                refine ⟨17295014326286854875855331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92240076406863226004561765 17295014326286854875855331)
                ·
                  refine ⟨25942521489430282313782997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17295014326286854875855331 25942521489430282313782997)
                  ·
                    refine ⟨608027847408522241729289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25942521489430282313782997 608027847408522241729289)
                    ·
                      rfl

theorem cell22_1776195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 7].length) (baseStart_1776195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776195 prefixEnd_1776195 := by exact prefixLift 1776195
  have htrace : WordTrace (prefixWord ++ tailWord_1776195) baseStart_1776195 baseEnd_1776195 := by
    simpa [prefixWord, tailWord_1776195, baseEnd_1776195] using wordTrace_append hprefix tailTrace_1776195
  have hstable : (prefixWord ++ tailWord_1776195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776195).length < 2 ^ (prefixWord ++ tailWord_1776195).sum := by decide
  have hdescent : baseEnd_1776195 < baseStart_1776195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776227 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 3, 4]
def baseStart_1776227 : Nat := 118140960795 + 1776227 * 2 ^ 59
def prefixEnd_1776227 : Nat := 4983230072969 + 3 ^ 40 * 1776227 * 2
def baseEnd_1776227 : Nat := 608038801662484824929191

theorem tailTrace_1776227 : CollatzResearch.WordTrace tailWord_1776227 prefixEnd_1776227 608038801662484824929191 := by
  unfold tailWord_1776227
  simp only [CollatzResearch.WordTrace]
  refine ⟨64784320936040409265350935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43189547290693606176900623 64784320936040409265350935)
  ·
    refine ⟨97176481404060613898026403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64784320936040409265350935 97176481404060613898026403)
    ·
      refine ⟨145764722106090920847039605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97176481404060613898026403 145764722106090920847039605)
      ·
        refine ⟨13665442697446023829409963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145764722106090920847039605 13665442697446023829409963)
        ·
          refine ⟨20498164046169035744114945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13665442697446023829409963 20498164046169035744114945)
          ·
            refine ⟨15373623034626776808086209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20498164046169035744114945 15373623034626776808086209)
            ·
              refine ⟨11530217275970082606064657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15373623034626776808086209 11530217275970082606064657)
              ·
                refine ⟨8647662956977561954548493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11530217275970082606064657 8647662956977561954548493)
                ·
                  refine ⟨3242873608866585732955685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8647662956977561954548493 3242873608866585732955685)
                  ·
                    refine ⟨608038801662484824929191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3242873608866585732955685 608038801662484824929191)
                    ·
                      rfl

theorem cell22_1776227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 4].length) (baseStart_1776227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776227 prefixEnd_1776227 := by exact prefixLift 1776227
  have htrace : WordTrace (prefixWord ++ tailWord_1776227) baseStart_1776227 baseEnd_1776227 := by
    simpa [prefixWord, tailWord_1776227, baseEnd_1776227] using wordTrace_append hprefix tailTrace_1776227
  have hstable : (prefixWord ++ tailWord_1776227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776227).length < 2 ^ (prefixWord ++ tailWord_1776227).sum := by decide
  have hdescent : baseEnd_1776227 < baseStart_1776227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776261 : List Nat := [1, 3, 1, 1, 4, 3, 3, 1, 1, 4]
def baseStart_1776261 : Nat := 118140960795 + 1776261 * 2 ^ 59
def prefixEnd_1776261 : Nat := 4983230072969 + 3 ^ 40 * 1776261 * 2
def baseEnd_1776261 : Nat := 608050440557320069579087

theorem tailTrace_1776261 : CollatzResearch.WordTrace tailWord_1776261 prefixEnd_1776261 608050440557320069579087 := by
  unfold tailWord_1776261
  simp only [CollatzResearch.WordTrace]
  refine ⟨64785561017917233072088637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43190374011944822048059091 64785561017917233072088637)
  ·
    refine ⟨24294585381718962402033239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64785561017917233072088637 24294585381718962402033239)
    ·
      refine ⟨36441878072578443603049859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24294585381718962402033239 36441878072578443603049859)
      ·
        refine ⟨54662817108867665404574789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36441878072578443603049859 54662817108867665404574789)
        ·
          refine ⟨10249278207912687263357773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54662817108867665404574789 10249278207912687263357773)
          ·
            refine ⟨3843479327967257723759165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10249278207912687263357773 3843479327967257723759165)
            ·
              refine ⟨1441304747987721646409687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3843479327967257723759165 1441304747987721646409687)
              ·
                refine ⟨2161957121981582469614531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1441304747987721646409687 2161957121981582469614531)
                ·
                  refine ⟨3242935682972373704421797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2161957121981582469614531 3242935682972373704421797)
                  ·
                    refine ⟨608050440557320069579087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3242935682972373704421797 608050440557320069579087)
                    ·
                      rfl

theorem cell22_1776261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_1776261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776261 prefixEnd_1776261 := by exact prefixLift 1776261
  have htrace : WordTrace (prefixWord ++ tailWord_1776261) baseStart_1776261 baseEnd_1776261 := by
    simpa [prefixWord, tailWord_1776261, baseEnd_1776261] using wordTrace_append hprefix tailTrace_1776261
  have hstable : (prefixWord ++ tailWord_1776261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776261).length < 2 ^ (prefixWord ++ tailWord_1776261).sum := by decide
  have hdescent : baseEnd_1776261 < baseStart_1776261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776310 : List Nat := [5, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_1776310 : Nat := 118140960795 + 1776310 * 2 ^ 59
def prefixEnd_1776310 : Nat := 4983230072969 + 3 ^ 40 * 1776310 * 2
def baseEnd_1776310 : Nat := 202689071419566758367979

theorem tailTrace_1776310 : CollatzResearch.WordTrace tailWord_1776310 prefixEnd_1776310 202689071419566758367979 := by
  unfold tailWord_1776310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4049209262171232152538899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43191565463159809627081589 4049209262171232152538899)
  ·
    refine ⟨6073813893256848228808349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4049209262171232152538899 6073813893256848228808349)
    ·
      refine ⟨2277680209971318085803131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6073813893256848228808349 2277680209971318085803131)
      ·
        refine ⟨3416520314956977128704697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2277680209971318085803131 3416520314956977128704697)
        ·
          refine ⟨2562390236217732846528523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3416520314956977128704697 2562390236217732846528523)
          ·
            refine ⟨3843585354326599269792785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2562390236217732846528523 3843585354326599269792785)
            ·
              refine ⟨2882689015744949452344589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3843585354326599269792785 2882689015744949452344589)
              ·
                refine ⟨1081008380904356044629221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2882689015744949452344589 1081008380904356044629221)
                ·
                  refine ⟨202689071419566758367979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1081008380904356044629221 202689071419566758367979)
                  ·
                    rfl

theorem cell22_1776310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_1776310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776310 prefixEnd_1776310 := by exact prefixLift 1776310
  have htrace : WordTrace (prefixWord ++ tailWord_1776310) baseStart_1776310 baseEnd_1776310 := by
    simpa [prefixWord, tailWord_1776310, baseEnd_1776310] using wordTrace_append hprefix tailTrace_1776310
  have hstable : (prefixWord ++ tailWord_1776310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776310).length < 2 ^ (prefixWord ++ tailWord_1776310).sum := by decide
  have hdescent : baseEnd_1776310 < baseStart_1776310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776321 : List Nat := [1, 2, 6, 2, 1, 1, 9]
def baseStart_1776321 : Nat := 118140960795 + 1776321 * 2 ^ 59
def prefixEnd_1776321 : Nat := 4983230072969 + 3 ^ 40 * 1776321 * 2
def baseEnd_1776321 : Nat := 22521147399388885669589

theorem tailTrace_1776321 : CollatzResearch.WordTrace tailWord_1776321 prefixEnd_1776321 22521147399388885669589 := by
  unfold tailWord_1776321
  simp only [CollatzResearch.WordTrace]
  refine ⟨64787749397699863319272817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43191832931799908879515211 64787749397699863319272817)
  ·
    refine ⟨48590812048274897489454613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64787749397699863319272817 48590812048274897489454613)
    ·
      refine ⟨2277694314762885819818185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48590812048274897489454613 2277694314762885819818185)
      ·
        refine ⟨1708270736072164364863639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2277694314762885819818185 1708270736072164364863639)
        ·
          refine ⟨2562406104108246547295459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1708270736072164364863639 2562406104108246547295459)
          ·
            refine ⟨3843609156162369820943189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2562406104108246547295459 3843609156162369820943189)
            ·
              refine ⟨22521147399388885669589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3843609156162369820943189 22521147399388885669589)
              ·
                rfl

theorem cell22_1776321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 9].length) (baseStart_1776321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776321 prefixEnd_1776321 := by exact prefixLift 1776321
  have htrace : WordTrace (prefixWord ++ tailWord_1776321) baseStart_1776321 baseEnd_1776321 := by
    simpa [prefixWord, tailWord_1776321, baseEnd_1776321] using wordTrace_append hprefix tailTrace_1776321
  have hstable : (prefixWord ++ tailWord_1776321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776321).length < 2 ^ (prefixWord ++ tailWord_1776321).sum := by decide
  have hdescent : baseEnd_1776321 < baseStart_1776321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776370 : List Nat := [3, 2, 1, 3, 1, 4, 1, 3, 1, 3]
def baseStart_1776370 : Nat := 118140960795 + 1776370 * 2 ^ 59
def prefixEnd_1776370 : Nat := 4983230072969 + 3 ^ 40 * 1776370 * 2
def baseEnd_1776370 : Nat := 608087753484880118603753

theorem tailTrace_1776370 : CollatzResearch.WordTrace tailWord_1776370 prefixEnd_1776370 608087753484880118603753 := by
  unfold tailWord_1776370
  simp only [CollatzResearch.WordTrace]
  refine ⟨16197384143630586171951641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43193024383014896458537709 16197384143630586171951641)
  ·
    refine ⟨12148038107722939628963731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16197384143630586171951641 12148038107722939628963731)
    ·
      refine ⟨18222057161584409443445597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12148038107722939628963731 18222057161584409443445597)
      ·
        refine ⟨6833271435594153541292099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18222057161584409443445597 6833271435594153541292099)
        ·
          refine ⟨10249907153391230311938149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6833271435594153541292099 10249907153391230311938149)
          ·
            refine ⟨1921857591260855683488403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10249907153391230311938149 1921857591260855683488403)
            ·
              refine ⟨2882786386891283525232605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1921857591260855683488403 2882786386891283525232605)
              ·
                refine ⟨1081044895084231321962227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2882786386891283525232605 1081044895084231321962227)
                ·
                  refine ⟨1621567342626346982943341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081044895084231321962227 1621567342626346982943341)
                  ·
                    refine ⟨608087753484880118603753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1621567342626346982943341 608087753484880118603753)
                    ·
                      rfl

theorem cell22_1776370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_1776370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776370 prefixEnd_1776370 := by exact prefixLift 1776370
  have htrace : WordTrace (prefixWord ++ tailWord_1776370) baseStart_1776370 baseEnd_1776370 := by
    simpa [prefixWord, tailWord_1776370, baseEnd_1776370] using wordTrace_append hprefix tailTrace_1776370
  have hstable : (prefixWord ++ tailWord_1776370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776370).length < 2 ^ (prefixWord ++ tailWord_1776370).sum := by decide
  have hdescent : baseEnd_1776370 < baseStart_1776370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776377 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 8]
def baseStart_1776377 : Nat := 118140960795 + 1776377 * 2 ^ 59
def prefixEnd_1776377 : Nat := 4983230072969 + 3 ^ 40 * 1776377 * 2
def baseEnd_1776377 : Nat := 202696716575978144559577

theorem tailTrace_1776377 : CollatzResearch.WordTrace tailWord_1776377 prefixEnd_1776377 202696716575978144559577 := by
  unfold tailWord_1776377
  simp only [CollatzResearch.WordTrace]
  refine ⟨64789791885496984883311385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43193194590331323255540923 64789791885496984883311385)
  ·
    refine ⟨48592343914122738662483539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64789791885496984883311385 48592343914122738662483539)
    ·
      refine ⟨72888515871184107993725309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48592343914122738662483539 72888515871184107993725309)
      ·
        refine ⟨27333193451694040497646991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72888515871184107993725309 27333193451694040497646991)
        ·
          refine ⟨40999790177541060746470487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27333193451694040497646991 40999790177541060746470487)
          ·
            refine ⟨61499685266311591119705731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40999790177541060746470487 61499685266311591119705731)
            ·
              refine ⟨92249527899467386679558597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61499685266311591119705731 92249527899467386679558597)
              ·
                refine ⟨17296786481150135002417237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92249527899467386679558597 17296786481150135002417237)
                ·
                  refine ⟨202696716575978144559577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17296786481150135002417237 202696716575978144559577)
                  ·
                    rfl

theorem cell22_1776377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 8].length) (baseStart_1776377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776377 prefixEnd_1776377 := by exact prefixLift 1776377
  have htrace : WordTrace (prefixWord ++ tailWord_1776377) baseStart_1776377 baseEnd_1776377 := by
    simpa [prefixWord, tailWord_1776377, baseEnd_1776377] using wordTrace_append hprefix tailTrace_1776377
  have hstable : (prefixWord ++ tailWord_1776377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776377).length < 2 ^ (prefixWord ++ tailWord_1776377).sum := by decide
  have hdescent : baseEnd_1776377 < baseStart_1776377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776409 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 6, 3]
def baseStart_1776409 : Nat := 118140960795 + 1776409 * 2 ^ 59
def prefixEnd_1776409 : Nat := 4983230072969 + 3 ^ 40 * 1776409 * 2
def baseEnd_1776409 : Nat := 608101103981897016878633

theorem tailTrace_1776409 : CollatzResearch.WordTrace tailWord_1776409 prefixEnd_1776409 608101103981897016878633 := by
  unfold tailWord_1776409
  simp only [CollatzResearch.WordTrace]
  refine ⟨64790959021381054348476281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43193972680920702898984187 64790959021381054348476281)
  ·
    refine ⟨48593219266035790761357211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64790959021381054348476281 48593219266035790761357211)
    ·
      refine ⟨72889828899053686142035817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48593219266035790761357211 72889828899053686142035817)
      ·
        refine ⟨54667371674290264606526863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72889828899053686142035817 54667371674290264606526863)
        ·
          refine ⟨82001057511435396909790295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54667371674290264606526863 82001057511435396909790295)
          ·
            refine ⟨123001586267153095364685443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82001057511435396909790295 123001586267153095364685443)
            ·
              refine ⟨184502379400729643047028165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123001586267153095364685443 184502379400729643047028165)
              ·
                refine ⟨34594196137636808071317781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184502379400729643047028165 34594196137636808071317781)
                ·
                  refine ⟨1621602943951725378343021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34594196137636808071317781 1621602943951725378343021)
                  ·
                    refine ⟨608101103981897016878633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1621602943951725378343021 608101103981897016878633)
                    ·
                      rfl

theorem cell22_1776409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 3].length) (baseStart_1776409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776409 prefixEnd_1776409 := by exact prefixLift 1776409
  have htrace : WordTrace (prefixWord ++ tailWord_1776409) baseStart_1776409 baseEnd_1776409 := by
    simpa [prefixWord, tailWord_1776409, baseEnd_1776409] using wordTrace_append hprefix tailTrace_1776409
  have hstable : (prefixWord ++ tailWord_1776409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776409).length < 2 ^ (prefixWord ++ tailWord_1776409).sum := by decide
  have hdescent : baseEnd_1776409 < baseStart_1776409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776413 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 3, 4]
def baseStart_1776413 : Nat := 118140960795 + 1776413 * 2 ^ 59
def prefixEnd_1776413 : Nat := 4983230072969 + 3 ^ 40 * 1776413 * 2
def baseEnd_1776413 : Nat := 608102473263642339778621

theorem tailTrace_1776413 : CollatzResearch.WordTrace tailWord_1776413 prefixEnd_1776413 608102473263642339778621 := by
  unfold tailWord_1776413
  simp only [CollatzResearch.WordTrace]
  refine ⟨64791104913366563031621893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43194069942244375354414595 64791104913366563031621893)
  ·
    refine ⟨12148332171256230568429105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64791104913366563031621893 12148332171256230568429105)
    ·
      refine ⟨9111249128442172926321829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12148332171256230568429105 9111249128442172926321829)
      ·
        refine ⟨1708359211582907423685343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9111249128442172926321829 1708359211582907423685343)
        ·
          refine ⟨2562538817374361135528015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1708359211582907423685343 2562538817374361135528015)
          ·
            refine ⟨3843808226061541703292023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2562538817374361135528015 3843808226061541703292023)
            ·
              refine ⟨5765712339092312554938035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3843808226061541703292023 5765712339092312554938035)
              ·
                refine ⟨8648568508638468832407053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5765712339092312554938035 8648568508638468832407053)
                ·
                  refine ⟨3243213190739425812152645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8648568508638468832407053 3243213190739425812152645)
                  ·
                    refine ⟨608102473263642339778621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3243213190739425812152645 608102473263642339778621)
                    ·
                      rfl

theorem cell22_1776413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_1776413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776413 prefixEnd_1776413 := by exact prefixLift 1776413
  have htrace : WordTrace (prefixWord ++ tailWord_1776413) baseStart_1776413 baseEnd_1776413 := by
    simpa [prefixWord, tailWord_1776413, baseEnd_1776413] using wordTrace_append hprefix tailTrace_1776413
  have hstable : (prefixWord ++ tailWord_1776413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776413).length < 2 ^ (prefixWord ++ tailWord_1776413).sum := by decide
  have hdescent : baseEnd_1776413 < baseStart_1776413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776430 : List Nat := [4, 1, 3, 2, 1, 2, 3, 1, 1, 4]
def baseStart_1776430 : Nat := 118140960795 + 1776430 * 2 ^ 59
def prefixEnd_1776430 : Nat := 4983230072969 + 3 ^ 40 * 1776430 * 2
def baseEnd_1776430 : Nat := 608108292711059962103569

theorem tailTrace_1776430 : CollatzResearch.WordTrace tailWord_1776430 prefixEnd_1776430 608108292711059962103569 := by
  unfold tailWord_1776430
  simp only [CollatzResearch.WordTrace]
  refine ⟨8098965619288121866873843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43194483302869983289993829 8098965619288121866873843)
  ·
    refine ⟨12148448428932182800310765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8098965619288121866873843 12148448428932182800310765)
    ·
      refine ⟨4555668160849568550116537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12148448428932182800310765 4555668160849568550116537)
      ·
        refine ⟨3416751120637176412587403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4555668160849568550116537 3416751120637176412587403)
        ·
          refine ⟨5125126680955764618881105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3416751120637176412587403 5125126680955764618881105)
          ·
            refine ⟨3843845010716823464160829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5125126680955764618881105 3843845010716823464160829)
            ·
              refine ⟨1441441879018808799060311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3843845010716823464160829 1441441879018808799060311)
              ·
                refine ⟨2162162818528213198590467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1441441879018808799060311 2162162818528213198590467)
                ·
                  refine ⟨3243244227792319797885701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2162162818528213198590467 3243244227792319797885701)
                  ·
                    refine ⟨608108292711059962103569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3243244227792319797885701 608108292711059962103569)
                    ·
                      rfl

theorem cell22_1776430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_1776430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776430 prefixEnd_1776430 := by exact prefixLift 1776430
  have htrace : WordTrace (prefixWord ++ tailWord_1776430) baseStart_1776430 baseEnd_1776430 := by
    simpa [prefixWord, tailWord_1776430, baseEnd_1776430] using wordTrace_append hprefix tailTrace_1776430
  have hstable : (prefixWord ++ tailWord_1776430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776430).length < 2 ^ (prefixWord ++ tailWord_1776430).sum := by decide
  have hdescent : baseEnd_1776430 < baseStart_1776430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776469 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 2, 6]
def baseStart_1776469 : Nat := 118140960795 + 1776469 * 2 ^ 59
def prefixEnd_1776469 : Nat := 4983230072969 + 3 ^ 40 * 1776469 * 2
def baseEnd_1776469 : Nat := 608121643208076860378449

theorem tailTrace_1776469 : CollatzResearch.WordTrace tailWord_1776469 prefixEnd_1776469 608121643208076860378449 := by
  unfold tailWord_1776469
  simp only [CollatzResearch.WordTrace]
  refine ⟨64793147401163684595660461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43195431600775789730440307 64793147401163684595660461)
  ·
    refine ⟨24297430275436381723372673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64793147401163684595660461 24297430275436381723372673)
    ·
      refine ⟨18223072706577286292529505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24297430275436381723372673 18223072706577286292529505)
      ·
        refine ⟨13667304529932964719397129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18223072706577286292529505 13667304529932964719397129)
        ·
          refine ⟨10250478397449723539547847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13667304529932964719397129 10250478397449723539547847)
          ·
            refine ⟨15375717596174585309321771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10250478397449723539547847 15375717596174585309321771)
            ·
              refine ⟨23063576394261877963982657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15375717596174585309321771 23063576394261877963982657)
              ·
                refine ⟨17297682295696408472986993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23063576394261877963982657 17297682295696408472986993)
                ·
                  refine ⟨12973261721772306354740245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17297682295696408472986993 12973261721772306354740245)
                  ·
                    refine ⟨608121643208076860378449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12973261721772306354740245 608121643208076860378449)
                    ·
                      rfl

theorem cell22_1776469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_1776469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776469 prefixEnd_1776469 := by exact prefixLift 1776469
  have htrace : WordTrace (prefixWord ++ tailWord_1776469) baseStart_1776469 baseEnd_1776469 := by
    simpa [prefixWord, tailWord_1776469, baseEnd_1776469] using wordTrace_append hprefix tailTrace_1776469
  have hstable : (prefixWord ++ tailWord_1776469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776469).length < 2 ^ (prefixWord ++ tailWord_1776469).sum := by decide
  have hdescent : baseEnd_1776469 < baseStart_1776469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776471 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 5, 3]
def baseStart_1776471 : Nat := 118140960795 + 1776471 * 2 ^ 59
def prefixEnd_1776471 : Nat := 4983230072969 + 3 ^ 40 * 1776471 * 2
def baseEnd_1776471 : Nat := 608122327848949521828443

theorem tailTrace_1776471 : CollatzResearch.WordTrace tailWord_1776471 prefixEnd_1776471 608122327848949521828443 := by
  unfold tailWord_1776471
  simp only [CollatzResearch.WordTrace]
  refine ⟨64793220347156438937233267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43195480231437625958155511 64793220347156438937233267)
  ·
    refine ⟨97189830520734658405849901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64793220347156438937233267 97189830520734658405849901)
    ·
      refine ⟨36446186445275496902193713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97189830520734658405849901 36446186445275496902193713)
      ·
        refine ⟨27334639833956622676645285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36446186445275496902193713 27334639833956622676645285)
        ·
          refine ⟨5125244968866866751870991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27334639833956622676645285 5125244968866866751870991)
          ·
            refine ⟨7687867453300300127806487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5125244968866866751870991 7687867453300300127806487)
            ·
              refine ⟨11531801179950450191709731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7687867453300300127806487 11531801179950450191709731)
              ·
                refine ⟨17297701769925675287564597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11531801179950450191709731 17297701769925675287564597)
                ·
                  refine ⟨1621659540930532058209181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17297701769925675287564597 1621659540930532058209181)
                  ·
                    refine ⟨608122327848949521828443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1621659540930532058209181 608122327848949521828443)
                    ·
                      rfl

theorem cell22_1776471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_1776471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776471 prefixEnd_1776471 := by exact prefixLift 1776471
  have htrace : WordTrace (prefixWord ++ tailWord_1776471) baseStart_1776471 baseEnd_1776471 := by
    simpa [prefixWord, tailWord_1776471, baseEnd_1776471] using wordTrace_append hprefix tailTrace_1776471
  have hstable : (prefixWord ++ tailWord_1776471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776471).length < 2 ^ (prefixWord ++ tailWord_1776471).sum := by decide
  have hdescent : baseEnd_1776471 < baseStart_1776471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776499 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 2, 5]
def baseStart_1776499 : Nat := 118140960795 + 1776499 * 2 ^ 59
def prefixEnd_1776499 : Nat := 4983230072969 + 3 ^ 40 * 1776499 * 2
def baseEnd_1776499 : Nat := 608131912821166782128357

theorem tailTrace_1776499 : CollatzResearch.WordTrace tailWord_1776499 prefixEnd_1776499 608131912821166782128357 := by
  unfold tailWord_1776499
  simp only [CollatzResearch.WordTrace]
  refine ⟨64794241591054999719252551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43196161060703333146168367 64794241591054999719252551)
  ·
    refine ⟨97191362386582499578878827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64794241591054999719252551 97191362386582499578878827)
    ·
      refine ⟨145787043579873749368318241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97191362386582499578878827 145787043579873749368318241)
      ·
        refine ⟨109340282684905312026238681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145787043579873749368318241 109340282684905312026238681)
        ·
          refine ⟨82005212013678984019679011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109340282684905312026238681 82005212013678984019679011)
          ·
            refine ⟨123007818020518476029518517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82005212013678984019679011 123007818020518476029518517)
            ·
              refine ⟨11531982939423607127767361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123007818020518476029518517 11531982939423607127767361)
              ·
                refine ⟨8648987204567705345825521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11531982939423607127767361 8648987204567705345825521)
                ·
                  refine ⟨6486740403425779009369141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8648987204567705345825521 6486740403425779009369141)
                  ·
                    refine ⟨608131912821166782128357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6486740403425779009369141 608131912821166782128357)
                    ·
                      rfl

theorem cell22_1776499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 5].length) (baseStart_1776499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776499 prefixEnd_1776499 := by exact prefixLift 1776499
  have htrace : WordTrace (prefixWord ++ tailWord_1776499) baseStart_1776499 baseEnd_1776499 := by
    simpa [prefixWord, tailWord_1776499, baseEnd_1776499] using wordTrace_append hprefix tailTrace_1776499
  have hstable : (prefixWord ++ tailWord_1776499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776499).length < 2 ^ (prefixWord ++ tailWord_1776499).sum := by decide
  have hdescent : baseEnd_1776499 < baseStart_1776499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776501 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 7]
def baseStart_1776501 : Nat := 118140960795 + 1776501 * 2 ^ 59
def prefixEnd_1776501 : Nat := 4983230072969 + 3 ^ 40 * 1776501 * 2
def baseEnd_1776501 : Nat := 202710865820679814526117

theorem tailTrace_1776501 : CollatzResearch.WordTrace tailWord_1776501 prefixEnd_1776501 202710865820679814526117 := by
  unfold tailWord_1776501
  simp only [CollatzResearch.WordTrace]
  refine ⟨64794314537047754060825357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43196209691365169373883571 64794314537047754060825357)
  ·
    refine ⟨24297867951392907772809509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64794314537047754060825357 24297867951392907772809509)
    ·
      refine ⟨4555850240886170207401783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24297867951392907772809509 4555850240886170207401783)
      ·
        refine ⟨6833775361329255311102675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4555850240886170207401783 6833775361329255311102675)
        ·
          refine ⟨10250663041993882966654013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6833775361329255311102675 10250663041993882966654013)
          ·
            refine ⟨3843998640747706112495255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10250663041993882966654013 3843998640747706112495255)
            ·
              refine ⟨5765997961121559168742883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3843998640747706112495255 5765997961121559168742883)
              ·
                refine ⟨8648996941682338753114325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5765997961121559168742883 8648996941682338753114325)
                ·
                  refine ⟨202710865820679814526117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8648996941682338753114325 202710865820679814526117)
                  ·
                    rfl

theorem cell22_1776501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_1776501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776501 prefixEnd_1776501 := by exact prefixLift 1776501
  have htrace : WordTrace (prefixWord ++ tailWord_1776501) baseStart_1776501 baseEnd_1776501 := by
    simpa [prefixWord, tailWord_1776501, baseEnd_1776501] using wordTrace_append hprefix tailTrace_1776501
  have hstable : (prefixWord ++ tailWord_1776501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776501).length < 2 ^ (prefixWord ++ tailWord_1776501).sum := by decide
  have hdescent : baseEnd_1776501 < baseStart_1776501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776559 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 3, 6]
def baseStart_1776559 : Nat := 118140960795 + 1776559 * 2 ^ 59
def prefixEnd_1776559 : Nat := 4983230072969 + 3 ^ 40 * 1776559 * 2
def baseEnd_1776559 : Nat := 608152452047346625628173

theorem tailTrace_1776559 : CollatzResearch.WordTrace tailWord_1776559 prefixEnd_1776559 608152452047346625628173 := by
  unfold tailWord_1776559
  simp only [CollatzResearch.WordTrace]
  refine ⟨64796429970837629966436731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43197619980558419977624487 64796429970837629966436731)
  ·
    refine ⟨97194644956256444949655097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64796429970837629966436731 97194644956256444949655097)
    ·
      refine ⟨72895983717192333712241323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97194644956256444949655097 72895983717192333712241323)
      ·
        refine ⟨109343975575788500568361985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72895983717192333712241323 109343975575788500568361985)
        ·
          refine ⟨82007981681841375426271489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109343975575788500568361985 82007981681841375426271489)
          ·
            refine ⟨61505986261381031569703617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82007981681841375426271489 61505986261381031569703617)
            ·
              refine ⟨46129489696035773677277713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61505986261381031569703617 46129489696035773677277713)
              ·
                refine ⟨34597117272026830257958285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46129489696035773677277713 34597117272026830257958285)
                ·
                  refine ⟨12973918977010061346734357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34597117272026830257958285 12973918977010061346734357)
                  ·
                    refine ⟨608152452047346625628173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12973918977010061346734357 608152452047346625628173)
                    ·
                      rfl

theorem cell22_1776559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_1776559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776559 prefixEnd_1776559 := by exact prefixLift 1776559
  have htrace : WordTrace (prefixWord ++ tailWord_1776559) baseStart_1776559 baseEnd_1776559 := by
    simpa [prefixWord, tailWord_1776559, baseEnd_1776559] using wordTrace_append hprefix tailTrace_1776559
  have hstable : (prefixWord ++ tailWord_1776559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776559).length < 2 ^ (prefixWord ++ tailWord_1776559).sum := by decide
  have hdescent : baseEnd_1776559 < baseStart_1776559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776610 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1776610 : Nat := 118140960795 + 1776610 * 2 ^ 59
def prefixEnd_1776610 : Nat := 4983230072969 + 3 ^ 40 * 1776610 * 2
def baseEnd_1776610 : Nat := 608169910389599492603017

theorem tailTrace_1776610 : CollatzResearch.WordTrace tailWord_1776610 prefixEnd_1776610 608169910389599492603017 := by
  unfold tailWord_1776610
  simp only [CollatzResearch.WordTrace]
  refine ⟨16199572523413216419135821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43198860062435243784362189 16199572523413216419135821)
  ·
    refine ⟨6074839696279956157175933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16199572523413216419135821 6074839696279956157175933)
    ·
      refine ⟨2278064886104983558940975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6074839696279956157175933 2278064886104983558940975)
      ·
        refine ⟨3417097329157475338411463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2278064886104983558940975 3417097329157475338411463)
        ·
          refine ⟨5125645993736213007617195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3417097329157475338411463 5125645993736213007617195)
          ·
            refine ⟨7688468990604319511425793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5125645993736213007617195 7688468990604319511425793)
            ·
              refine ⟨5766351742953239633569345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7688468990604319511425793 5766351742953239633569345)
              ·
                refine ⟨4324763807214929725177009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5766351742953239633569345 4324763807214929725177009)
                ·
                  refine ⟨3243572855411197293882757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4324763807214929725177009 3243572855411197293882757)
                  ·
                    refine ⟨608169910389599492603017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3243572855411197293882757 608169910389599492603017)
                    ·
                      rfl

theorem cell22_1776610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1776610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776610 prefixEnd_1776610 := by exact prefixLift 1776610
  have htrace : WordTrace (prefixWord ++ tailWord_1776610) baseStart_1776610 baseEnd_1776610 := by
    simpa [prefixWord, tailWord_1776610, baseEnd_1776610] using wordTrace_append hprefix tailTrace_1776610
  have hstable : (prefixWord ++ tailWord_1776610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776610).length < 2 ^ (prefixWord ++ tailWord_1776610).sum := by decide
  have hdescent : baseEnd_1776610 < baseStart_1776610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776642 : List Nat := [3, 4, 1, 3, 1, 1, 3, 6]
def baseStart_1776642 : Nat := 118140960795 + 1776642 * 2 ^ 59
def prefixEnd_1776642 : Nat := 4983230072969 + 3 ^ 40 * 1776642 * 2
def baseEnd_1776642 : Nat := 67575651627062452866991

theorem tailTrace_1776642 : CollatzResearch.WordTrace tailWord_1776642 prefixEnd_1776642 67575651627062452866991 := by
  unfold tailWord_1776642
  simp only [CollatzResearch.WordTrace]
  refine ⟨16199864307384233785427045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43199638153024623427805453 16199864307384233785427045)
  ·
    refine ⟨3037474557634543834767571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16199864307384233785427045 3037474557634543834767571)
    ·
      refine ⟨4556211836451815752151357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3037474557634543834767571 4556211836451815752151357)
      ·
        refine ⟨1708579438669430907056759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4556211836451815752151357 1708579438669430907056759)
        ·
          refine ⟨2562869158004146360585139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1708579438669430907056759 2562869158004146360585139)
          ·
            refine ⟨3844303737006219540877709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2562869158004146360585139 3844303737006219540877709)
            ·
              refine ⟨1441613901377332327829141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3844303737006219540877709 1441613901377332327829141)
              ·
                refine ⟨67575651627062452866991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1441613901377332327829141 67575651627062452866991)
                ·
                  rfl

theorem cell22_1776642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 6].length) (baseStart_1776642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776642 prefixEnd_1776642 := by exact prefixLift 1776642
  have htrace : WordTrace (prefixWord ++ tailWord_1776642) baseStart_1776642 baseEnd_1776642 := by
    simpa [prefixWord, tailWord_1776642, baseEnd_1776642] using wordTrace_append hprefix tailTrace_1776642
  have hstable : (prefixWord ++ tailWord_1776642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776642).length < 2 ^ (prefixWord ++ tailWord_1776642).sum := by decide
  have hdescent : baseEnd_1776642 < baseStart_1776642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776700 : List Nat := [2, 2, 2, 2, 2, 3, 2, 2, 1, 4]
def baseStart_1776700 : Nat := 118140960795 + 1776700 * 2 ^ 59
def prefixEnd_1776700 : Nat := 4983230072969 + 3 ^ 40 * 1776700 * 2
def baseEnd_1776700 : Nat := 608200719228869257852741

theorem tailTrace_1776700 : CollatzResearch.WordTrace tailWord_1776700 prefixEnd_1776700 608200719228869257852741 := by
  unfold tailWord_1776700
  simp only [CollatzResearch.WordTrace]
  refine ⟨32400786331663405523659777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43201048442217874031546369 32400786331663405523659777)
  ·
    refine ⟨24300589748747554142744833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32400786331663405523659777 24300589748747554142744833)
    ·
      refine ⟨18225442311560665607058625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24300589748747554142744833 18225442311560665607058625)
      ·
        refine ⟨13669081733670499205293969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18225442311560665607058625 13669081733670499205293969)
        ·
          refine ⟨10251811300252874403970477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13669081733670499205293969 10251811300252874403970477)
          ·
            refine ⟨3844429237594827901488929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10251811300252874403970477 3844429237594827901488929)
            ·
              refine ⟨2883321928196120926116697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3844429237594827901488929 2883321928196120926116697)
              ·
                refine ⟨2162491446147090694587523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2883321928196120926116697 2162491446147090694587523)
                ·
                  refine ⟨3243737169220636041881285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2162491446147090694587523 3243737169220636041881285)
                  ·
                    refine ⟨608200719228869257852741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3243737169220636041881285 608200719228869257852741)
                    ·
                      rfl

theorem cell22_1776700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_1776700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776700 prefixEnd_1776700 := by exact prefixLift 1776700
  have htrace : WordTrace (prefixWord ++ tailWord_1776700) baseStart_1776700 baseEnd_1776700 := by
    simpa [prefixWord, tailWord_1776700, baseEnd_1776700] using wordTrace_append hprefix tailTrace_1776700
  have hstable : (prefixWord ++ tailWord_1776700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776700).length < 2 ^ (prefixWord ++ tailWord_1776700).sum := by decide
  have hdescent : baseEnd_1776700 < baseStart_1776700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776728 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 2, 4]
def baseStart_1776728 : Nat := 118140960795 + 1776728 * 2 ^ 59
def prefixEnd_1776728 : Nat := 4983230072969 + 3 ^ 40 * 1776728 * 2
def baseEnd_1776728 : Nat := 608210304201086518152655

theorem tailTrace_1776728 : CollatzResearch.WordTrace tailWord_1776728 prefixEnd_1776728 608210304201086518152655 := by
  unfold tailWord_1776728
  simp only [CollatzResearch.WordTrace]
  refine ⟨32401296953612685914669419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43201729271483581219559225 32401296953612685914669419)
  ·
    refine ⟨48601945430419028872004129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32401296953612685914669419 48601945430419028872004129)
    ·
      refine ⟨36451459072814271654003097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48601945430419028872004129 36451459072814271654003097)
      ·
        refine ⟨27338594304610703740502323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36451459072814271654003097 27338594304610703740502323)
        ·
          refine ⟨41007891456916055610753485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27338594304610703740502323 41007891456916055610753485)
          ·
            refine ⟨15377959296343520854032557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41007891456916055610753485 15377959296343520854032557)
            ·
              refine ⟨5766734736128820320262209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15377959296343520854032557 5766734736128820320262209)
              ·
                refine ⟨4325051052096615240196657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5766734736128820320262209 4325051052096615240196657)
                ·
                  refine ⟨3243788289072461430147493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4325051052096615240196657 3243788289072461430147493)
                  ·
                    refine ⟨608210304201086518152655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3243788289072461430147493 608210304201086518152655)
                    ·
                      rfl

theorem cell22_1776728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_1776728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776728 prefixEnd_1776728 := by exact prefixLift 1776728
  have htrace : WordTrace (prefixWord ++ tailWord_1776728) baseStart_1776728 baseEnd_1776728 := by
    simpa [prefixWord, tailWord_1776728, baseEnd_1776728] using wordTrace_append hprefix tailTrace_1776728
  have hstable : (prefixWord ++ tailWord_1776728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776728).length < 2 ^ (prefixWord ++ tailWord_1776728).sum := by decide
  have hdescent : baseEnd_1776728 < baseStart_1776728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776732 : List Nat := [2, 2, 4, 1, 1, 1, 5, 2, 4]
def baseStart_1776732 : Nat := 118140960795 + 1776732 * 2 ^ 59
def prefixEnd_1776732 : Nat := 4983230072969 + 3 ^ 40 * 1776732 * 2
def baseEnd_1776732 : Nat := 202737224494277280350881

theorem tailTrace_1776732 : CollatzResearch.WordTrace tailWord_1776732 prefixEnd_1776732 202737224494277280350881 := by
  unfold tailWord_1776732
  simp only [CollatzResearch.WordTrace]
  refine ⟨32401369899605440256242225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43201826532807253674989633 32401369899605440256242225)
  ·
    refine ⟨24301027424704080192181669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32401369899605440256242225 24301027424704080192181669)
    ·
      refine ⟨4556442642132015036034063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24301027424704080192181669 4556442642132015036034063)
      ·
        refine ⟨6834663963198022554051095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4556442642132015036034063 6834663963198022554051095)
        ·
          refine ⟨10251995944797033831076643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6834663963198022554051095 10251995944797033831076643)
          ·
            refine ⟨15377993917195550746614965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10251995944797033831076643 15377993917195550746614965)
            ·
              refine ⟨1441686929737082882495153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15377993917195550746614965 1441686929737082882495153)
              ·
                refine ⟨1081265197302812161871365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1441686929737082882495153 1081265197302812161871365)
                ·
                  refine ⟨202737224494277280350881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1081265197302812161871365 202737224494277280350881)
                  ·
                    rfl

theorem cell22_1776732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_1776732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776732 prefixEnd_1776732 := by exact prefixLift 1776732
  have htrace : WordTrace (prefixWord ++ tailWord_1776732) baseStart_1776732 baseEnd_1776732 := by
    simpa [prefixWord, tailWord_1776732, baseEnd_1776732] using wordTrace_append hprefix tailTrace_1776732
  have hstable : (prefixWord ++ tailWord_1776732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776732).length < 2 ^ (prefixWord ++ tailWord_1776732).sum := by decide
  have hdescent : baseEnd_1776732 < baseStart_1776732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776743 : List Nat := [1, 1, 5, 1, 1, 4, 2, 7]
def baseStart_1776743 : Nat := 118140960795 + 1776743 * 2 ^ 59
def prefixEnd_1776743 : Nat := 4983230072969 + 3 ^ 40 * 1776743 * 2
def baseEnd_1776743 : Nat := 67579493223070164336401

theorem tailTrace_1776743 : CollatzResearch.WordTrace tailWord_1776743 prefixEnd_1776743 67579493223070164336401 := by
  unfold tailWord_1776743
  simp only [CollatzResearch.WordTrace]
  refine ⟨64803141002171029391134883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43202094001447352927423255 64803141002171029391134883)
  ·
    refine ⟨97204711503256544086702325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64803141002171029391134883 97204711503256544086702325)
    ·
      refine ⟨9112941703430301008128343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97204711503256544086702325 9112941703430301008128343)
      ·
        refine ⟨13669412555145451512192515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9112941703430301008128343 13669412555145451512192515)
        ·
          refine ⟨20504118832718177268288773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13669412555145451512192515 20504118832718177268288773)
          ·
            refine ⟨3844522281134658237804145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20504118832718177268288773 3844522281134658237804145)
            ·
              refine ⟨2883391710850993678353109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3844522281134658237804145 2883391710850993678353109)
              ·
                refine ⟨67579493223070164336401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2883391710850993678353109 67579493223070164336401)
                ·
                  rfl

theorem cell22_1776743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 7].length) (baseStart_1776743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776743 prefixEnd_1776743 := by exact prefixLift 1776743
  have htrace : WordTrace (prefixWord ++ tailWord_1776743) baseStart_1776743 baseEnd_1776743 := by
    simpa [prefixWord, tailWord_1776743, baseEnd_1776743] using wordTrace_append hprefix tailTrace_1776743
  have hstable : (prefixWord ++ tailWord_1776743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776743).length < 2 ^ (prefixWord ++ tailWord_1776743).sum := by decide
  have hdescent : baseEnd_1776743 < baseStart_1776743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776850 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 6]
def baseStart_1776850 : Nat := 118140960795 + 1776850 * 2 ^ 59
def prefixEnd_1776850 : Nat := 4983230072969 + 3 ^ 40 * 1776850 * 2
def baseEnd_1776850 : Nat := 202750689098106288867427

theorem tailTrace_1776850 : CollatzResearch.WordTrace tailWord_1776850 prefixEnd_1776850 202750689098106288867427 := by
  unfold tailWord_1776850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16201760903195846666320001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43204695741855591110186669 16201760903195846666320001)
  ·
    refine ⟨12151320677396884999740001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16201760903195846666320001 12151320677396884999740001)
    ·
      refine ⟨9113490508047663749805001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12151320677396884999740001 9113490508047663749805001)
      ·
        refine ⟨6835117881035747812353751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9113490508047663749805001 6835117881035747812353751)
        ·
          refine ⟨10252676821553621718530627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6835117881035747812353751 10252676821553621718530627)
          ·
            refine ⟨15379015232330432577795941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10252676821553621718530627 15379015232330432577795941)
            ·
              refine ⟨2883565356061956108336739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15379015232330432577795941 2883565356061956108336739)
              ·
                refine ⟨4325348034092934162505109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2883565356061956108336739 4325348034092934162505109)
                ·
                  refine ⟨202750689098106288867427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4325348034092934162505109 202750689098106288867427)
                  ·
                    rfl

theorem cell22_1776850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_1776850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776850 prefixEnd_1776850 := by exact prefixLift 1776850
  have htrace : WordTrace (prefixWord ++ tailWord_1776850) baseStart_1776850 baseEnd_1776850 := by
    simpa [prefixWord, tailWord_1776850, baseEnd_1776850] using wordTrace_append hprefix tailTrace_1776850
  have hstable : (prefixWord ++ tailWord_1776850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776850).length < 2 ^ (prefixWord ++ tailWord_1776850).sum := by decide
  have hdescent : baseEnd_1776850 < baseStart_1776850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776863 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 1, 6]
def baseStart_1776863 : Nat := 118140960795 + 1776863 * 2 ^ 59
def prefixEnd_1776863 : Nat := 4983230072969 + 3 ^ 40 * 1776863 * 2
def baseEnd_1776863 : Nat := 608256517459991166027241

theorem tailTrace_1776863 : CollatzResearch.WordTrace tailWord_1776863 prefixEnd_1776863 608256517459991166027241 := by
  unfold tailWord_1776863
  simp only [CollatzResearch.WordTrace]
  refine ⟨64807517761736289885503243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43205011841157526590335495 64807517761736289885503243)
  ·
    refine ⟨97211276642604434828254865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64807517761736289885503243 97211276642604434828254865)
    ·
      refine ⟨72908457481953326121191149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97211276642604434828254865 72908457481953326121191149)
      ·
        refine ⟨27340671555732497295446681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72908457481953326121191149 27340671555732497295446681)
        ·
          refine ⟨20505503666799372971585011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27340671555732497295446681 20505503666799372971585011)
          ·
            refine ⟨30758255500199059457377517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20505503666799372971585011 30758255500199059457377517)
            ·
              refine ⟨11534345812574647296516569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30758255500199059457377517 11534345812574647296516569)
              ·
                refine ⟨8650759359430985472387427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11534345812574647296516569 8650759359430985472387427)
                ·
                  refine ⟨12976139039146478208581141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8650759359430985472387427 12976139039146478208581141)
                  ·
                    refine ⟨608256517459991166027241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12976139039146478208581141 608256517459991166027241)
                    ·
                      rfl

theorem cell22_1776863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_1776863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776863 prefixEnd_1776863 := by exact prefixLift 1776863
  have htrace : WordTrace (prefixWord ++ tailWord_1776863) baseStart_1776863 baseEnd_1776863 := by
    simpa [prefixWord, tailWord_1776863, baseEnd_1776863] using wordTrace_append hprefix tailTrace_1776863
  have hstable : (prefixWord ++ tailWord_1776863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776863).length < 2 ^ (prefixWord ++ tailWord_1776863).sum := by decide
  have hdescent : baseEnd_1776863 < baseStart_1776863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776865 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 1, 5]
def baseStart_1776865 : Nat := 118140960795 + 1776865 * 2 ^ 59
def prefixEnd_1776865 : Nat := 4983230072969 + 3 ^ 40 * 1776865 * 2
def baseEnd_1776865 : Nat := 608257202100863827477235

theorem tailTrace_1776865 : CollatzResearch.WordTrace tailWord_1776865 prefixEnd_1776865 608257202100863827477235 := by
  unfold tailWord_1776865
  simp only [CollatzResearch.WordTrace]
  refine ⟨64807590707729044227076049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43205060471819362818050699 64807590707729044227076049)
  ·
    refine ⟨48605693030796783170307037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64807590707729044227076049 48605693030796783170307037)
    ·
      refine ⟨18227134886548793688865139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48605693030796783170307037 18227134886548793688865139)
      ·
        refine ⟨27340702329823190533297709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18227134886548793688865139 27340702329823190533297709)
        ·
          refine ⟨10252763373683696449986641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27340702329823190533297709 10252763373683696449986641)
          ·
            refine ⟨7689572530262772337489981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10252763373683696449986641 7689572530262772337489981)
            ·
              refine ⟨2883589698848539626558743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7689572530262772337489981 2883589698848539626558743)
              ·
                refine ⟨4325384548272809439838115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2883589698848539626558743 4325384548272809439838115)
                ·
                  refine ⟨6488076822409214159757173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4325384548272809439838115 6488076822409214159757173)
                  ·
                    refine ⟨608257202100863827477235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6488076822409214159757173 608257202100863827477235)
                    ·
                      rfl

theorem cell22_1776865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_1776865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776865 prefixEnd_1776865 := by exact prefixLift 1776865
  have htrace : WordTrace (prefixWord ++ tailWord_1776865) baseStart_1776865 baseEnd_1776865 := by
    simpa [prefixWord, tailWord_1776865, baseEnd_1776865] using wordTrace_append hprefix tailTrace_1776865
  have hstable : (prefixWord ++ tailWord_1776865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776865).length < 2 ^ (prefixWord ++ tailWord_1776865).sum := by decide
  have hdescent : baseEnd_1776865 < baseStart_1776865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776961 : List Nat := [1, 2, 5, 2, 1, 2, 1, 4, 1, 3]
def baseStart_1776961 : Nat := 118140960795 + 1776961 * 2 ^ 59
def prefixEnd_1776961 : Nat := 4983230072969 + 3 ^ 40 * 1776961 * 2
def baseEnd_1776961 : Nat := 608290064862751577076941

theorem tailTrace_1776961 : CollatzResearch.WordTrace tailWord_1776961 prefixEnd_1776961 608290064862751577076941 := by
  unfold tailWord_1776961
  simp only [CollatzResearch.WordTrace]
  refine ⟨64811092115381252622570737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43207394743587501748380491 64811092115381252622570737)
  ·
    refine ⟨48608319086535939466928053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64811092115381252622570737 48608319086535939466928053)
    ·
      refine ⟨4557029914362744325024505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48608319086535939466928053 4557029914362744325024505)
      ·
        refine ⟨3417772435772058243768379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4557029914362744325024505 3417772435772058243768379)
        ·
          refine ⟨5126658653658087365652569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3417772435772058243768379 5126658653658087365652569)
          ·
            refine ⟨3844993990243565524239427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5126658653658087365652569 3844993990243565524239427)
            ·
              refine ⟨5767490985365348286359141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3844993990243565524239427 5767490985365348286359141)
              ·
                refine ⟨1081404559756002803692339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5767490985365348286359141 1081404559756002803692339)
                ·
                  refine ⟨1622106839634004205538509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081404559756002803692339 1622106839634004205538509)
                  ·
                    refine ⟨608290064862751577076941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1622106839634004205538509 608290064862751577076941)
                    ·
                      rfl

theorem cell22_1776961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_1776961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1776961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1776961 prefixEnd_1776961 := by exact prefixLift 1776961
  have htrace : WordTrace (prefixWord ++ tailWord_1776961) baseStart_1776961 baseEnd_1776961 := by
    simpa [prefixWord, tailWord_1776961, baseEnd_1776961] using wordTrace_append hprefix tailTrace_1776961
  have hstable : (prefixWord ++ tailWord_1776961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776961).length < 2 ^ (prefixWord ++ tailWord_1776961).sum := by decide
  have hdescent : baseEnd_1776961 < baseStart_1776961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777004 : List Nat := [2, 2, 1, 1, 5, 1, 4, 1, 1, 4]
def baseStart_1777004 : Nat := 118140960795 + 1777004 * 2 ^ 59
def prefixEnd_1777004 : Nat := 4983230072969 + 3 ^ 40 * 1777004 * 2
def baseEnd_1777004 : Nat := 608304784641513798251809

theorem tailTrace_1777004 : CollatzResearch.WordTrace tailWord_1777004 prefixEnd_1777004 608304784641513798251809 := by
  unfold tailWord_1777004
  simp only [CollatzResearch.WordTrace]
  refine ⟨32406330227112735483193033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43208440302816980644257377 32406330227112735483193033)
  ·
    refine ⟨24304747670334551612394775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32406330227112735483193033 24304747670334551612394775)
    ·
      refine ⟨36457121505501827418592163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24304747670334551612394775 36457121505501827418592163)
      ·
        refine ⟨54685682258252741127888245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36457121505501827418592163 54685682258252741127888245)
        ·
          refine ⟨5126782711711194480739523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54685682258252741127888245 5126782711711194480739523)
          ·
            refine ⟨7690174067566791721109285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5126782711711194480739523 7690174067566791721109285)
            ·
              refine ⟨1441907637668773447707991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7690174067566791721109285 1441907637668773447707991)
              ·
                refine ⟨2162861456503160171561987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1441907637668773447707991 2162861456503160171561987)
                ·
                  refine ⟨3244292184754740257342981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2162861456503160171561987 3244292184754740257342981)
                  ·
                    refine ⟨608304784641513798251809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3244292184754740257342981 608304784641513798251809)
                    ·
                      rfl

theorem cell22_1777004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_1777004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777004 prefixEnd_1777004 := by exact prefixLift 1777004
  have htrace : WordTrace (prefixWord ++ tailWord_1777004) baseStart_1777004 baseEnd_1777004 := by
    simpa [prefixWord, tailWord_1777004, baseEnd_1777004] using wordTrace_append hprefix tailTrace_1777004
  have hstable : (prefixWord ++ tailWord_1777004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777004).length < 2 ^ (prefixWord ++ tailWord_1777004).sum := by decide
  have hdescent : baseEnd_1777004 < baseStart_1777004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777015 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 4, 4]
def baseStart_1777015 : Nat := 118140960795 + 1777015 * 2 ^ 59
def prefixEnd_1777015 : Nat := 4983230072969 + 3 ^ 40 * 1777015 * 2
def baseEnd_1777015 : Nat := 608308550166313436226775

theorem tailTrace_1777015 : CollatzResearch.WordTrace tailWord_1777015 prefixEnd_1777015 608308550166313436226775 := by
  unfold tailWord_1777015
  simp only [CollatzResearch.WordTrace]
  refine ⟨64813061657185619845036499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43208707771457079896690999 64813061657185619845036499)
  ·
    refine ⟨97219592485778429767554749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64813061657185619845036499 97219592485778429767554749)
    ·
      refine ⟨36457347182166911162833031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97219592485778429767554749 36457347182166911162833031)
      ·
        refine ⟨54686020773250366744249547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36457347182166911162833031 54686020773250366744249547)
        ·
          refine ⟨82029031159875550116374321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54686020773250366744249547 82029031159875550116374321)
          ·
            refine ⟨61521773369906662587280741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82029031159875550116374321 61521773369906662587280741)
            ·
              refine ⟨11535332506857499235115139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61521773369906662587280741 11535332506857499235115139)
              ·
                refine ⟨17302998760286248852672709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11535332506857499235115139 17302998760286248852672709)
                ·
                  refine ⟨3244312267553671659876133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17302998760286248852672709 3244312267553671659876133)
                  ·
                    refine ⟨608308550166313436226775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3244312267553671659876133 608308550166313436226775)
                    ·
                      rfl

theorem cell22_1777015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_1777015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777015 prefixEnd_1777015 := by exact prefixLift 1777015
  have htrace : WordTrace (prefixWord ++ tailWord_1777015) baseStart_1777015 baseEnd_1777015 := by
    simpa [prefixWord, tailWord_1777015, baseEnd_1777015] using wordTrace_append hprefix tailTrace_1777015
  have hstable : (prefixWord ++ tailWord_1777015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777015).length < 2 ^ (prefixWord ++ tailWord_1777015).sum := by decide
  have hdescent : baseEnd_1777015 < baseStart_1777015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777060 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_1777060 : Nat := 118140960795 + 1777060 * 2 ^ 59
def prefixEnd_1777060 : Nat := 4983230072969 + 3 ^ 40 * 1777060 * 2
def baseEnd_1777060 : Nat := 608323954585948318851637

theorem tailTrace_1777060 : CollatzResearch.WordTrace tailWord_1777060 prefixEnd_1777060 608323954585948318851637 := by
  unfold tailWord_1777060
  simp only [CollatzResearch.WordTrace]
  refine ⟨32407351471011296265212317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43209801961348395020283089 32407351471011296265212317)
  ·
    refine ⟨12152756801629236099454619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32407351471011296265212317 12152756801629236099454619)
    ·
      refine ⟨18229135202443854149181929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12152756801629236099454619 18229135202443854149181929)
      ·
        refine ⟨13671851401832890611886447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18229135202443854149181929 13671851401832890611886447)
        ·
          refine ⟨20507777102749335917829671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13671851401832890611886447 20507777102749335917829671)
          ·
            refine ⟨30761665654124003876744507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20507777102749335917829671 30761665654124003876744507)
            ·
              refine ⟨46142498481186005815116761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30761665654124003876744507 46142498481186005815116761)
              ·
                refine ⟨34606873860889504361337571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46142498481186005815116761 34606873860889504361337571)
                ·
                  refine ⟨51910310791334256542006357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34606873860889504361337571 51910310791334256542006357)
                  ·
                    refine ⟨608323954585948318851637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51910310791334256542006357 608323954585948318851637)
                    ·
                      rfl

theorem cell22_1777060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_1777060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777060 prefixEnd_1777060 := by exact prefixLift 1777060
  have htrace : WordTrace (prefixWord ++ tailWord_1777060) baseStart_1777060 baseEnd_1777060 := by
    simpa [prefixWord, tailWord_1777060, baseEnd_1777060] using wordTrace_append hprefix tailTrace_1777060
  have hstable : (prefixWord ++ tailWord_1777060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777060).length < 2 ^ (prefixWord ++ tailWord_1777060).sum := by decide
  have hdescent : baseEnd_1777060 < baseStart_1777060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777064 : List Nat := [2, 1, 6, 1, 2, 2, 8]
def baseStart_1777064 : Nat := 118140960795 + 1777064 * 2 ^ 59
def prefixEnd_1777064 : Nat := 4983230072969 + 3 ^ 40 * 1777064 * 2
def baseEnd_1777064 : Nat := 22530567550655320064875

theorem tailTrace_1777064 : CollatzResearch.WordTrace tailWord_1777064 prefixEnd_1777064 22530567550655320064875 := by
  unfold tailWord_1777064
  simp only [CollatzResearch.WordTrace]
  refine ⟨32407424417004050606785123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43209899222672067475713497 32407424417004050606785123)
  ·
    refine ⟨48611136625506075910177685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32407424417004050606785123 48611136625506075910177685)
    ·
      refine ⟨2278647029320597308289579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48611136625506075910177685 2278647029320597308289579)
      ·
        refine ⟨3417970543980895962434369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2278647029320597308289579 3417970543980895962434369)
        ·
          refine ⟨2563477907985671971825777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3417970543980895962434369 2563477907985671971825777)
          ·
            refine ⟨1922608430989253978869333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2563477907985671971825777 1922608430989253978869333)
            ·
              refine ⟨22530567550655320064875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1922608430989253978869333 22530567550655320064875)
              ·
                rfl

theorem cell22_1777064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 8].length) (baseStart_1777064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777064 prefixEnd_1777064 := by exact prefixLift 1777064
  have htrace : WordTrace (prefixWord ++ tailWord_1777064) baseStart_1777064 baseEnd_1777064 := by
    simpa [prefixWord, tailWord_1777064, baseEnd_1777064] using wordTrace_append hprefix tailTrace_1777064
  have hstable : (prefixWord ++ tailWord_1777064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777064).length < 2 ^ (prefixWord ++ tailWord_1777064).sum := by decide
  have hdescent : baseEnd_1777064 < baseStart_1777064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777120 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 10]
def baseStart_1777120 : Nat := 118140960795 + 1777120 * 2 ^ 59
def prefixEnd_1777120 : Nat := 4983230072969 + 3 ^ 40 * 1777120 * 2
def baseEnd_1777120 : Nat := 202781497937376054117151

theorem tailTrace_1777120 : CollatzResearch.WordTrace tailWord_1777120 prefixEnd_1777120 202781497937376054117151 := by
  unfold tailWord_1777120
  simp only [CollatzResearch.WordTrace]
  refine ⟨32408445660902611388804407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43211260881203481851739209 32408445660902611388804407)
  ·
    refine ⟨48612668491353917083206611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32408445660902611388804407 48612668491353917083206611)
    ·
      refine ⟨72919002737030875624809917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48612668491353917083206611 72919002737030875624809917)
      ·
        refine ⟨27344626026386578359303719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72919002737030875624809917 27344626026386578359303719)
        ·
          refine ⟨41016939039579867538955579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27344626026386578359303719 41016939039579867538955579)
          ·
            refine ⟨61525408559369801308433369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41016939039579867538955579 61525408559369801308433369)
            ·
              refine ⟨46144056419527350981325027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61525408559369801308433369 46144056419527350981325027)
              ·
                refine ⟨69216084629291026471987541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46144056419527350981325027 69216084629291026471987541)
                ·
                  refine ⟨202781497937376054117151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 69216084629291026471987541 202781497937376054117151)
                  ·
                    rfl

theorem cell22_1777120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 10].length) (baseStart_1777120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777120 prefixEnd_1777120 := by exact prefixLift 1777120
  have htrace : WordTrace (prefixWord ++ tailWord_1777120) baseStart_1777120 baseEnd_1777120 := by
    simpa [prefixWord, tailWord_1777120, baseEnd_1777120] using wordTrace_append hprefix tailTrace_1777120
  have hstable : (prefixWord ++ tailWord_1777120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777120).length < 2 ^ (prefixWord ++ tailWord_1777120).sum := by decide
  have hdescent : baseEnd_1777120 < baseStart_1777120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777130 : List Nat := [3, 1, 3, 1, 4, 2, 2, 2, 1, 3]
def baseStart_1777130 : Nat := 118140960795 + 1777130 * 2 ^ 59
def prefixEnd_1777130 : Nat := 4983230072969 + 3 ^ 40 * 1777130 * 2
def baseEnd_1777130 : Nat := 608347917016491469601423

theorem tailTrace_1777130 : CollatzResearch.WordTrace tailWord_1777130 prefixEnd_1777130 608347917016491469601423 := by
  unfold tailWord_1777130
  simp only [CollatzResearch.WordTrace]
  refine ⟨16204314012942248621368211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43211504034512662990315229 16204314012942248621368211)
  ·
    refine ⟨24306471019413372932052317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16204314012942248621368211 24306471019413372932052317)
    ·
      refine ⟨9114926632280014849519619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24306471019413372932052317 9114926632280014849519619)
      ·
        refine ⟨13672389948420022274279429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9114926632280014849519619 13672389948420022274279429)
        ·
          refine ⟨2563573115328754176427393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13672389948420022274279429 2563573115328754176427393)
          ·
            refine ⟨1922679836496565632320545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2563573115328754176427393 1922679836496565632320545)
            ·
              refine ⟨1442009877372424224240409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1922679836496565632320545 1442009877372424224240409)
              ·
                refine ⟨1081507408029318168180307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1442009877372424224240409 1081507408029318168180307)
                ·
                  refine ⟨1622261112043977252270461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081507408029318168180307 1622261112043977252270461)
                  ·
                    refine ⟨608347917016491469601423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1622261112043977252270461 608347917016491469601423)
                    ·
                      rfl

theorem cell22_1777130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_1777130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777130 prefixEnd_1777130 := by exact prefixLift 1777130
  have htrace : WordTrace (prefixWord ++ tailWord_1777130) baseStart_1777130 baseEnd_1777130 := by
    simpa [prefixWord, tailWord_1777130, baseEnd_1777130] using wordTrace_append hprefix tailTrace_1777130
  have hstable : (prefixWord ++ tailWord_1777130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777130).length < 2 ^ (prefixWord ++ tailWord_1777130).sum := by decide
  have hdescent : baseEnd_1777130 < baseStart_1777130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777154 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 8]
def baseStart_1777154 : Nat := 118140960795 + 1777154 * 2 ^ 59
def prefixEnd_1777154 : Nat := 4983230072969 + 3 ^ 40 * 1777154 * 2
def baseEnd_1777154 : Nat := 202785377568987802333783

theorem tailTrace_1777154 : CollatzResearch.WordTrace tailWord_1777154 prefixEnd_1777154 202785377568987802333783 := by
  unfold tailWord_1777154
  simp only [CollatzResearch.WordTrace]
  refine ⟨16204532850920511646086629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43212087602454697722897677 16204532850920511646086629)
  ·
    refine ⟨3038349909547595933641243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16204532850920511646086629 3038349909547595933641243)
    ·
      refine ⟨4557524864321393900461865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3038349909547595933641243 4557524864321393900461865)
      ·
        refine ⟨3418143648241045425346399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4557524864321393900461865 3418143648241045425346399)
        ·
          refine ⟨5127215472361568138019599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3418143648241045425346399 5127215472361568138019599)
          ·
            refine ⟨7690823208542352207029399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5127215472361568138019599 7690823208542352207029399)
            ·
              refine ⟨11536234812813528310544099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7690823208542352207029399 11536234812813528310544099)
              ·
                refine ⟨17304352219220292465816149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11536234812813528310544099 17304352219220292465816149)
                ·
                  refine ⟨202785377568987802333783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17304352219220292465816149 202785377568987802333783)
                  ·
                    rfl

theorem cell22_1777154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_1777154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777154 prefixEnd_1777154 := by exact prefixLift 1777154
  have htrace : WordTrace (prefixWord ++ tailWord_1777154) baseStart_1777154 baseEnd_1777154 := by
    simpa [prefixWord, tailWord_1777154, baseEnd_1777154] using wordTrace_append hprefix tailTrace_1777154
  have hstable : (prefixWord ++ tailWord_1777154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777154).length < 2 ^ (prefixWord ++ tailWord_1777154).sum := by decide
  have hdescent : baseEnd_1777154 < baseStart_1777154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777186 : List Nat := [3, 3, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_1777186 : Nat := 118140960795 + 1777186 * 2 ^ 59
def prefixEnd_1777186 : Nat := 4983230072969 + 3 ^ 40 * 1777186 * 2
def baseEnd_1777186 : Nat := 608367086960925990201251

theorem tailTrace_1777186 : CollatzResearch.WordTrace tailWord_1777186 prefixEnd_1777186 608367086960925990201251 := by
  unfold tailWord_1777186
  simp only [CollatzResearch.WordTrace]
  refine ⟨16204824634891529012377853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43212865693044077366340941 16204824634891529012377853)
  ·
    refine ⟨6076809238084323379641695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16204824634891529012377853 6076809238084323379641695)
    ·
      refine ⟨9115213857126485069462543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6076809238084323379641695 9115213857126485069462543)
      ·
        refine ⟨13672820785689727604193815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9115213857126485069462543 13672820785689727604193815)
        ·
          refine ⟨20509231178534591406290723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13672820785689727604193815 20509231178534591406290723)
          ·
            refine ⟨30763846767801887109436085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20509231178534591406290723 30763846767801887109436085)
            ·
              refine ⟨2884110634481426916509633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30763846767801887109436085 2884110634481426916509633)
              ·
                refine ⟨2163082975861070187382225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2884110634481426916509633 2163082975861070187382225)
                ·
                  refine ⟨1622312231895802640536669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2163082975861070187382225 1622312231895802640536669)
                  ·
                    refine ⟨608367086960925990201251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1622312231895802640536669 608367086960925990201251)
                    ·
                      rfl

theorem cell22_1777186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_1777186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777186 prefixEnd_1777186 := by exact prefixLift 1777186
  have htrace : WordTrace (prefixWord ++ tailWord_1777186) baseStart_1777186 baseEnd_1777186 := by
    simpa [prefixWord, tailWord_1777186, baseEnd_1777186] using wordTrace_append hprefix tailTrace_1777186
  have hstable : (prefixWord ++ tailWord_1777186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777186).length < 2 ^ (prefixWord ++ tailWord_1777186).sum := by decide
  have hdescent : baseEnd_1777186 < baseStart_1777186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777222 : List Nat := [6, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_1777222 : Nat := 118140960795 + 1777222 * 2 ^ 59
def prefixEnd_1777222 : Nat := 4983230072969 + 3 ^ 40 * 1777222 * 2
def baseEnd_1777222 : Nat := 202793136832211298767047

theorem tailTrace_1777222 : CollatzResearch.WordTrace tailWord_1777222 prefixEnd_1777222 202793136832211298767047 := by
  unfold tailWord_1777222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2025644111482365443681935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43213741044957129465214613 2025644111482365443681935)
  ·
    refine ⟨3038466167223548165522903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2025644111482365443681935 3038466167223548165522903)
    ·
      refine ⟨4557699250835322248284355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3038466167223548165522903 4557699250835322248284355)
      ·
        refine ⟨6836548876252983372426533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4557699250835322248284355 6836548876252983372426533)
        ·
          refine ⟨1281852914297434382329975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6836548876252983372426533 1281852914297434382329975)
          ·
            refine ⟨1922779371446151573494963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281852914297434382329975 1922779371446151573494963)
            ·
              refine ⟨2884169057169227360242445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1922779371446151573494963 2884169057169227360242445)
              ·
                refine ⟨1081563396438460260090917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2884169057169227360242445 1081563396438460260090917)
                ·
                  refine ⟨202793136832211298767047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1081563396438460260090917 202793136832211298767047)
                  ·
                    rfl

theorem cell22_1777222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_1777222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777222 prefixEnd_1777222 := by exact prefixLift 1777222
  have htrace : WordTrace (prefixWord ++ tailWord_1777222) baseStart_1777222 baseEnd_1777222 := by
    simpa [prefixWord, tailWord_1777222, baseEnd_1777222] using wordTrace_append hprefix tailTrace_1777222
  have hstable : (prefixWord ++ tailWord_1777222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777222).length < 2 ^ (prefixWord ++ tailWord_1777222).sum := by decide
  have hdescent : baseEnd_1777222 < baseStart_1777222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777242 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 4, 5]
def baseStart_1777242 : Nat := 118140960795 + 1777242 * 2 ^ 59
def prefixEnd_1777242 : Nat := 4983230072969 + 3 ^ 40 * 1777242 * 2
def baseEnd_1777242 : Nat := 608386256905360510801079

theorem tailTrace_1777242 : CollatzResearch.WordTrace tailWord_1777242 prefixEnd_1777242 608386256905360510801079 := by
  unfold tailWord_1777242
  simp only [CollatzResearch.WordTrace]
  refine ⟨16205335256840809403387495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43214227351575491742366653 16205335256840809403387495)
  ·
    refine ⟨24308002885261214105081243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16205335256840809403387495 24308002885261214105081243)
    ·
      refine ⟨36462004327891821157621865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24308002885261214105081243 36462004327891821157621865)
      ·
        refine ⟨27346503245918865868216399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36462004327891821157621865 27346503245918865868216399)
        ·
          refine ⟨41019754868878298802324599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27346503245918865868216399 41019754868878298802324599)
          ·
            refine ⟨61529632303317448203486899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41019754868878298802324599 61529632303317448203486899)
            ·
              refine ⟨92294448454976172305230349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61529632303317448203486899 92294448454976172305230349)
              ·
                refine ⟨34610418170616064614461381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92294448454976172305230349 34610418170616064614461381)
                ·
                  refine ⟨6489453406990512115211509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34610418170616064614461381 6489453406990512115211509)
                  ·
                    refine ⟨608386256905360510801079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6489453406990512115211509 608386256905360510801079)
                    ·
                      rfl

theorem cell22_1777242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_1777242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777242 prefixEnd_1777242 := by exact prefixLift 1777242
  have htrace : WordTrace (prefixWord ++ tailWord_1777242) baseStart_1777242 baseEnd_1777242 := by
    simpa [prefixWord, tailWord_1777242, baseEnd_1777242] using wordTrace_append hprefix tailTrace_1777242
  have hstable : (prefixWord ++ tailWord_1777242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777242).length < 2 ^ (prefixWord ++ tailWord_1777242).sum := by decide
  have hdescent : baseEnd_1777242 < baseStart_1777242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777244 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 7]
def baseStart_1777244 : Nat := 118140960795 + 1777244 * 2 ^ 59
def prefixEnd_1777244 : Nat := 4983230072969 + 3 ^ 40 * 1777244 * 2
def baseEnd_1777244 : Nat := 202795647182077724083691

theorem tailTrace_1777244 : CollatzResearch.WordTrace tailWord_1777244 prefixEnd_1777244 202795647182077724083691 := by
  unfold tailWord_1777244
  simp only [CollatzResearch.WordTrace]
  refine ⟨32410706986677995977561393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43214275982237327970081857 32410706986677995977561393)
  ·
    refine ⟨24308030240008496983171045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32410706986677995977561393 24308030240008496983171045)
    ·
      refine ⟨4557755670001593184344571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24308030240008496983171045 4557755670001593184344571)
      ·
        refine ⟨6836633505002389776516857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4557755670001593184344571 6836633505002389776516857)
        ·
          refine ⟨5127475128751792332387643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6836633505002389776516857 5127475128751792332387643)
          ·
            refine ⟨7691212693127688498581465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5127475128751792332387643 7691212693127688498581465)
            ·
              refine ⟨5768409519845766373936099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7691212693127688498581465 5768409519845766373936099)
              ·
                refine ⟨8652614279768649560904149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5768409519845766373936099 8652614279768649560904149)
                ·
                  refine ⟨202795647182077724083691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8652614279768649560904149 202795647182077724083691)
                  ·
                    rfl

theorem cell22_1777244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_1777244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777244 prefixEnd_1777244 := by exact prefixLift 1777244
  have htrace : WordTrace (prefixWord ++ tailWord_1777244) baseStart_1777244 baseEnd_1777244 := by
    simpa [prefixWord, tailWord_1777244, baseEnd_1777244] using wordTrace_append hprefix tailTrace_1777244
  have hstable : (prefixWord ++ tailWord_1777244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777244).length < 2 ^ (prefixWord ++ tailWord_1777244).sum := by decide
  have hdescent : baseEnd_1777244 < baseStart_1777244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777261 : List Nat := [1, 5, 1, 1, 4, 1, 1, 3, 5]
def baseStart_1777261 : Nat := 118140960795 + 1777261 * 2 ^ 59
def prefixEnd_1777261 : Nat := 4983230072969 + 3 ^ 40 * 1777261 * 2
def baseEnd_1777261 : Nat := 202797586997883598192007

theorem tailTrace_1777261 : CollatzResearch.WordTrace tailWord_1777261 prefixEnd_1777261 202797586997883598192007 := by
  unfold tailWord_1777261
  simp only [CollatzResearch.WordTrace]
  refine ⟨64822034014294403858491637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43214689342862935905661091 64822034014294403858491637)
  ·
    refine ⟨6077065688840100361733591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64822034014294403858491637 6077065688840100361733591)
    ·
      refine ⟨9115598533260150542600387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6077065688840100361733591 9115598533260150542600387)
      ·
        refine ⟨13673397799890225813900581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9115598533260150542600387 13673397799890225813900581)
        ·
          refine ⟨2563762087479417340106359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13673397799890225813900581 2563762087479417340106359)
          ·
            refine ⟨3845643131219126010159539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2563762087479417340106359 3845643131219126010159539)
            ·
              refine ⟨5768464696828689015239309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3845643131219126010159539 5768464696828689015239309)
              ·
                refine ⟨2163174261310758380714741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5768464696828689015239309 2163174261310758380714741)
                ·
                  refine ⟨202797586997883598192007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2163174261310758380714741 202797586997883598192007)
                  ·
                    rfl

theorem cell22_1777261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_1777261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777261 prefixEnd_1777261 := by exact prefixLift 1777261
  have htrace : WordTrace (prefixWord ++ tailWord_1777261) baseStart_1777261 baseEnd_1777261 := by
    simpa [prefixWord, tailWord_1777261, baseEnd_1777261] using wordTrace_append hprefix tailTrace_1777261
  have hstable : (prefixWord ++ tailWord_1777261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777261).length < 2 ^ (prefixWord ++ tailWord_1777261).sum := by decide
  have hdescent : baseEnd_1777261 < baseStart_1777261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777274 : List Nat := [3, 1, 1, 1, 1, 1, 1, 8, 1, 4]
def baseStart_1777274 : Nat := 118140960795 + 1777274 * 2 ^ 59
def prefixEnd_1777274 : Nat := 4983230072969 + 3 ^ 40 * 1777274 * 2
def baseEnd_1777274 : Nat := 608397211159323094000981

theorem tailTrace_1777274 : CollatzResearch.WordTrace tailWord_1777274 prefixEnd_1777274 608397211159323094000981 := by
  unfold tailWord_1777274
  simp only [CollatzResearch.WordTrace]
  refine ⟨16205627040811826769678719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43215005442164871385809917 16205627040811826769678719)
  ·
    refine ⟨24308440561217740154518079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16205627040811826769678719 24308440561217740154518079)
    ·
      refine ⟨36462660841826610231777119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24308440561217740154518079 36462660841826610231777119)
      ·
        refine ⟨54693991262739915347665679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36462660841826610231777119 54693991262739915347665679)
        ·
          refine ⟨82040986894109873021498519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54693991262739915347665679 82040986894109873021498519)
          ·
            refine ⟨123061480341164809532247779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82040986894109873021498519 123061480341164809532247779)
            ·
              refine ⟨184592220511747214298371669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123061480341164809532247779 184592220511747214298371669)
              ·
                refine ⟨2163190084122037667559043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 184592220511747214298371669 2163190084122037667559043)
                ·
                  refine ⟨3244785126183056501338565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163190084122037667559043 3244785126183056501338565)
                  ·
                    refine ⟨608397211159323094000981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3244785126183056501338565 608397211159323094000981)
                    ·
                      rfl

theorem cell22_1777274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_1777274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777274 prefixEnd_1777274 := by exact prefixLift 1777274
  have htrace : WordTrace (prefixWord ++ tailWord_1777274) baseStart_1777274 baseEnd_1777274 := by
    simpa [prefixWord, tailWord_1777274, baseEnd_1777274] using wordTrace_append hprefix tailTrace_1777274
  have hstable : (prefixWord ++ tailWord_1777274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777274).length < 2 ^ (prefixWord ++ tailWord_1777274).sum := by decide
  have hdescent : baseEnd_1777274 < baseStart_1777274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777291 : List Nat := [1, 1, 1, 1, 4, 1, 7, 1, 1, 4]
def baseStart_1777291 : Nat := 118140960795 + 1777291 * 2 ^ 59
def prefixEnd_1777291 : Nat := 4983230072969 + 3 ^ 40 * 1777291 * 2
def baseEnd_1777291 : Nat := 608403030606740716325929

theorem tailTrace_1777291 : CollatzResearch.WordTrace tailWord_1777291 prefixEnd_1777291 608403030606740716325929 := by
  unfold tailWord_1777291
  simp only [CollatzResearch.WordTrace]
  refine ⟨64823128204185718982083727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43215418802790479321389151 64823128204185718982083727)
  ·
    refine ⟨97234692306278578473125591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64823128204185718982083727 97234692306278578473125591)
    ·
      refine ⟨145852038459417867709688387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97234692306278578473125591 145852038459417867709688387)
      ·
        refine ⟨218778057689126801564532581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145852038459417867709688387 218778057689126801564532581)
        ·
          refine ⟨41020885816711275293349859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218778057689126801564532581 41020885816711275293349859)
          ·
            refine ⟨61531328725066912940024789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41020885816711275293349859 61531328725066912940024789)
            ·
              refine ⟨1442140516993755772031831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 61531328725066912940024789 1442140516993755772031831)
              ·
                refine ⟨2163210775490633658047747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442140516993755772031831 2163210775490633658047747)
                ·
                  refine ⟨3244816163235950487071621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163210775490633658047747 3244816163235950487071621)
                  ·
                    refine ⟨608403030606740716325929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3244816163235950487071621 608403030606740716325929)
                    ·
                      rfl

theorem cell22_1777291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 1, 4].length) (baseStart_1777291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777291 prefixEnd_1777291 := by exact prefixLift 1777291
  have htrace : WordTrace (prefixWord ++ tailWord_1777291) baseStart_1777291 baseEnd_1777291 := by
    simpa [prefixWord, tailWord_1777291, baseEnd_1777291] using wordTrace_append hprefix tailTrace_1777291
  have hstable : (prefixWord ++ tailWord_1777291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777291).length < 2 ^ (prefixWord ++ tailWord_1777291).sum := by decide
  have hdescent : baseEnd_1777291 < baseStart_1777291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777372 : List Nat := [2, 2, 5, 1, 2, 1, 3, 1, 2, 3]
def baseStart_1777372 : Nat := 118140960795 + 1777372 * 2 ^ 59
def prefixEnd_1777372 : Nat := 4983230072969 + 3 ^ 40 * 1777372 * 2
def baseEnd_1777372 : Nat := 608430758562083505050681

theorem tailTrace_1777372 : CollatzResearch.WordTrace tailWord_1777372 prefixEnd_1777372 608430758562083505050681 := by
  unfold tailWord_1777372
  simp only [CollatzResearch.WordTrace]
  refine ⟨32413041258446134907891185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43217388344594846543854913 32413041258446134907891185)
  ·
    refine ⟨24309780943834601180918389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32413041258446134907891185 24309780943834601180918389)
    ·
      refine ⟨2279041963484493860711099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24309780943834601180918389 2279041963484493860711099)
      ·
        refine ⟨3418562945226740791066649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2279041963484493860711099 3418562945226740791066649)
        ·
          refine ⟨2563922208920055593299987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3418562945226740791066649 2563922208920055593299987)
          ·
            refine ⟨3845883313380083389949981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2563922208920055593299987 3845883313380083389949981)
            ·
              refine ⟨1442206242517531271231243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3845883313380083389949981 1442206242517531271231243)
              ·
                refine ⟨2163309363776296906846865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442206242517531271231243 2163309363776296906846865)
                ·
                  refine ⟨1622482022832222680135149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2163309363776296906846865 1622482022832222680135149)
                  ·
                    refine ⟨608430758562083505050681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1622482022832222680135149 608430758562083505050681)
                    ·
                      rfl

theorem cell22_1777372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_1777372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777372 prefixEnd_1777372 := by exact prefixLift 1777372
  have htrace : WordTrace (prefixWord ++ tailWord_1777372) baseStart_1777372 baseEnd_1777372 := by
    simpa [prefixWord, tailWord_1777372, baseEnd_1777372] using wordTrace_append hprefix tailTrace_1777372
  have hstable : (prefixWord ++ tailWord_1777372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777372).length < 2 ^ (prefixWord ++ tailWord_1777372).sum := by decide
  have hdescent : baseEnd_1777372 < baseStart_1777372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777475 : List Nat := [1, 1, 1, 3, 1, 7, 2, 2, 4]
def baseStart_1777475 : Nat := 118140960795 + 1777475 * 2 ^ 59
def prefixEnd_1777475 : Nat := 4983230072969 + 3 ^ 40 * 1777475 * 2
def baseEnd_1777475 : Nat := 202822005855675189908455

theorem tailTrace_1777475 : CollatzResearch.WordTrace tailWord_1777475 prefixEnd_1777475 202822005855675189908455 := by
  unfold tailWord_1777475
  simp only [CollatzResearch.WordTrace]
  refine ⟨64829839235519118406781879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43219892823679412271187919 64829839235519118406781879)
  ·
    refine ⟨97244758853278677610172819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64829839235519118406781879 97244758853278677610172819)
    ·
      refine ⟨145867138279918016415259229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97244758853278677610172819 145867138279918016415259229)
      ·
        refine ⟨54700176854969256155722211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145867138279918016415259229 54700176854969256155722211)
        ·
          refine ⟨82050265282453884233583317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54700176854969256155722211 82050265282453884233583317)
          ·
            refine ⟨1923053092557512911724609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 82050265282453884233583317 1923053092557512911724609)
            ·
              refine ⟨1442289819418134683793457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1923053092557512911724609 1442289819418134683793457)
              ·
                refine ⟨1081717364563601012845093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1442289819418134683793457 1081717364563601012845093)
                ·
                  refine ⟨202822005855675189908455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1081717364563601012845093 202822005855675189908455)
                  ·
                    rfl

theorem cell22_1777475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 4].length) (baseStart_1777475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777475 prefixEnd_1777475 := by exact prefixLift 1777475
  have htrace : WordTrace (prefixWord ++ tailWord_1777475) baseStart_1777475 baseEnd_1777475 := by
    simpa [prefixWord, tailWord_1777475, baseEnd_1777475] using wordTrace_append hprefix tailTrace_1777475
  have hstable : (prefixWord ++ tailWord_1777475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777475).length < 2 ^ (prefixWord ++ tailWord_1777475).sum := by decide
  have hdescent : baseEnd_1777475 < baseStart_1777475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777561 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 3, 4]
def baseStart_1777561 : Nat := 118140960795 + 1777561 * 2 ^ 59
def prefixEnd_1777561 : Nat := 4983230072969 + 3 ^ 40 * 1777561 * 2
def baseEnd_1777561 : Nat := 608495457124550012075101

theorem tailTrace_1777561 : CollatzResearch.WordTrace tailWord_1777561 prefixEnd_1777561 608495457124550012075101 := by
  unfold tailWord_1777561
  simp only [CollatzResearch.WordTrace]
  refine ⟨64832975913207555094412537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43221983942138370062941691 64832975913207555094412537)
  ·
    refine ⟨48624731934905666320809403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64832975913207555094412537 48624731934905666320809403)
    ·
      refine ⟨72937097902358499481214105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48624731934905666320809403 72937097902358499481214105)
      ·
        refine ⟨54702823426768874610910579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72937097902358499481214105 54702823426768874610910579)
        ·
          refine ⟨82054235140153311916365869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54702823426768874610910579 82054235140153311916365869)
          ·
            refine ⟨30770338177557491968637201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82054235140153311916365869 30770338177557491968637201)
            ·
              refine ⟨23077753633168118976477901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30770338177557491968637201 23077753633168118976477901)
              ·
                refine ⟨8654157612438044616179213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23077753633168118976477901 8654157612438044616179213)
                ·
                  refine ⟨3245309104664266731067205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8654157612438044616179213 3245309104664266731067205)
                  ·
                    refine ⟨608495457124550012075101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3245309104664266731067205 608495457124550012075101)
                    ·
                      rfl

theorem cell22_1777561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_1777561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777561 prefixEnd_1777561 := by exact prefixLift 1777561
  have htrace : WordTrace (prefixWord ++ tailWord_1777561) baseStart_1777561 baseEnd_1777561 := by
    simpa [prefixWord, tailWord_1777561, baseEnd_1777561] using wordTrace_append hprefix tailTrace_1777561
  have hstable : (prefixWord ++ tailWord_1777561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777561).length < 2 ^ (prefixWord ++ tailWord_1777561).sum := by decide
  have hdescent : baseEnd_1777561 < baseStart_1777561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777569 : List Nat := [1, 2, 3, 4, 2, 2, 1, 3, 1, 3]
def baseStart_1777569 : Nat := 118140960795 + 1777569 * 2 ^ 59
def prefixEnd_1777569 : Nat := 4983230072969 + 3 ^ 40 * 1777569 * 2
def baseEnd_1777569 : Nat := 608498195688040657875077

theorem tailTrace_1777569 : CollatzResearch.WordTrace tailWord_1777569 prefixEnd_1777569 608498195688040657875077 := by
  unfold tailWord_1777569
  simp only [CollatzResearch.WordTrace]
  refine ⟨64833267697178572460703761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43222178464785714973802507 64833267697178572460703761)
  ·
    refine ⟨48624950772883929345527821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64833267697178572460703761 48624950772883929345527821)
    ·
      refine ⟨18234356539831473504572933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48624950772883929345527821 18234356539831473504572933)
      ·
        refine ⟨3418941851218401282107425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18234356539831473504572933 3418941851218401282107425)
        ·
          refine ⟨2564206388413800961580569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3418941851218401282107425 2564206388413800961580569)
          ·
            refine ⟨1923154791310350721185427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2564206388413800961580569 1923154791310350721185427)
            ·
              refine ⟨2884732186965526081778141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923154791310350721185427 2884732186965526081778141)
              ·
                refine ⟨1081774570112072280666803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2884732186965526081778141 1081774570112072280666803)
                ·
                  refine ⟨1622661855168108421000205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081774570112072280666803 1622661855168108421000205)
                  ·
                    refine ⟨608498195688040657875077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1622661855168108421000205 608498195688040657875077)
                    ·
                      rfl

theorem cell22_1777569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_1777569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777569 prefixEnd_1777569 := by exact prefixLift 1777569
  have htrace : WordTrace (prefixWord ++ tailWord_1777569) baseStart_1777569 baseEnd_1777569 := by
    simpa [prefixWord, tailWord_1777569, baseEnd_1777569] using wordTrace_append hprefix tailTrace_1777569
  have hstable : (prefixWord ++ tailWord_1777569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777569).length < 2 ^ (prefixWord ++ tailWord_1777569).sum := by decide
  have hdescent : baseEnd_1777569 < baseStart_1777569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777623 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 2, 4]
def baseStart_1777623 : Nat := 118140960795 + 1777623 * 2 ^ 59
def prefixEnd_1777623 : Nat := 4983230072969 + 3 ^ 40 * 1777623 * 2
def baseEnd_1777623 : Nat := 608516680991602517024911

theorem tailTrace_1777623 : CollatzResearch.WordTrace tailWord_1777623 prefixEnd_1777623 608516680991602517024911 := by
  unfold tailWord_1777623
  simp only [CollatzResearch.WordTrace]
  refine ⟨64835237238982939683169523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43223491492655293122113015 64835237238982939683169523)
  ·
    refine ⟨97252855858474409524754285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64835237238982939683169523 97252855858474409524754285)
    ·
      refine ⟨36469820946927903571782857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97252855858474409524754285 36469820946927903571782857)
      ·
        refine ⟨27352365710195927678837143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36469820946927903571782857 27352365710195927678837143)
        ·
          refine ⟨41028548565293891518255715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27352365710195927678837143 41028548565293891518255715)
          ·
            refine ⟨61542822847940837277383573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41028548565293891518255715 61542822847940837277383573)
            ·
              refine ⟨2884819820997226747377355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61542822847940837277383573 2884819820997226747377355)
              ·
                refine ⟨4327229731495840121066033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2884819820997226747377355 4327229731495840121066033)
                ·
                  refine ⟨3245422298621880090799525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4327229731495840121066033 3245422298621880090799525)
                  ·
                    refine ⟨608516680991602517024911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3245422298621880090799525 608516680991602517024911)
                    ·
                      rfl

theorem cell22_1777623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_1777623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777623 prefixEnd_1777623 := by exact prefixLift 1777623
  have htrace : WordTrace (prefixWord ++ tailWord_1777623) baseStart_1777623 baseEnd_1777623 := by
    simpa [prefixWord, tailWord_1777623, baseEnd_1777623] using wordTrace_append hprefix tailTrace_1777623
  have hstable : (prefixWord ++ tailWord_1777623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777623).length < 2 ^ (prefixWord ++ tailWord_1777623).sum := by decide
  have hdescent : baseEnd_1777623 < baseStart_1777623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777698 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_1777698 : Nat := 118140960795 + 1777698 * 2 ^ 59
def prefixEnd_1777698 : Nat := 4983230072969 + 3 ^ 40 * 1777698 * 2
def baseEnd_1777698 : Nat := 608542355024327321399681

theorem tailTrace_1777698 : CollatzResearch.WordTrace tailWord_1777698 prefixEnd_1777698 608542355024327321399681 := by
  unfold tailWord_1777698
  simp only [CollatzResearch.WordTrace]
  refine ⟨16209493178427806873037437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43225315142474151661433165 16209493178427806873037437)
  ·
    refine ⟨6078559941910427577389039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16209493178427806873037437 6078559941910427577389039)
    ·
      refine ⟨9117839912865641366083559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6078559941910427577389039 9117839912865641366083559)
      ·
        refine ⟨13676759869298462049125339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9117839912865641366083559 13676759869298462049125339)
        ·
          refine ⟨20515139803947693073688009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13676759869298462049125339 20515139803947693073688009)
          ·
            refine ⟨15386354852960769805266007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20515139803947693073688009 15386354852960769805266007)
            ·
              refine ⟨23079532279441154707899011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15386354852960769805266007 23079532279441154707899011)
              ·
                refine ⟨34619298419161732061848517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23079532279441154707899011 34619298419161732061848517)
                ·
                  refine ⟨6491118453592824761596597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34619298419161732061848517 6491118453592824761596597)
                  ·
                    refine ⟨608542355024327321399681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6491118453592824761596597 608542355024327321399681)
                    ·
                      rfl

theorem cell22_1777698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_1777698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777698 prefixEnd_1777698 := by exact prefixLift 1777698
  have htrace : WordTrace (prefixWord ++ tailWord_1777698) baseStart_1777698 baseEnd_1777698 := by
    simpa [prefixWord, tailWord_1777698, baseEnd_1777698] using wordTrace_append hprefix tailTrace_1777698
  have hstable : (prefixWord ++ tailWord_1777698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777698).length < 2 ^ (prefixWord ++ tailWord_1777698).sum := by decide
  have hdescent : baseEnd_1777698 < baseStart_1777698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777700 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 7]
def baseStart_1777700 : Nat := 118140960795 + 1777700 * 2 ^ 59
def prefixEnd_1777700 : Nat := 4983230072969 + 3 ^ 40 * 1777700 * 2
def baseEnd_1777700 : Nat := 202847679888399994283225

theorem tailTrace_1777700 : CollatzResearch.WordTrace tailWord_1777700 prefixEnd_1777700 202847679888399994283225 := by
  unfold tailWord_1777700
  simp only [CollatzResearch.WordTrace]
  refine ⟨32419022829851990916861277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43225363773135987889148369 32419022829851990916861277)
  ·
    refine ⟨12157133561194496593822979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32419022829851990916861277 12157133561194496593822979)
    ·
      refine ⟨18235700341791744890734469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12157133561194496593822979 18235700341791744890734469)
      ·
        refine ⟨3419193814085952167012713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18235700341791744890734469 3419193814085952167012713)
        ·
          refine ⟨2564395360564464125259535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3419193814085952167012713 2564395360564464125259535)
          ·
            refine ⟨3846593040846696187889303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2564395360564464125259535 3846593040846696187889303)
            ·
              refine ⟨5769889561270044281833955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3846593040846696187889303 5769889561270044281833955)
              ·
                refine ⟨8654834341905066422750933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5769889561270044281833955 8654834341905066422750933)
                ·
                  refine ⟨202847679888399994283225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8654834341905066422750933 202847679888399994283225)
                  ·
                    rfl

theorem cell22_1777700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_1777700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777700 prefixEnd_1777700 := by exact prefixLift 1777700
  have htrace : WordTrace (prefixWord ++ tailWord_1777700) baseStart_1777700 baseEnd_1777700 := by
    simpa [prefixWord, tailWord_1777700, baseEnd_1777700] using wordTrace_append hprefix tailTrace_1777700
  have hstable : (prefixWord ++ tailWord_1777700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777700).length < 2 ^ (prefixWord ++ tailWord_1777700).sum := by decide
  have hdescent : baseEnd_1777700 < baseStart_1777700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777704 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 3, 3]
def baseStart_1777704 : Nat := 118140960795 + 1777704 * 2 ^ 59
def prefixEnd_1777704 : Nat := 4983230072969 + 3 ^ 40 * 1777704 * 2
def baseEnd_1777704 : Nat := 608544408946945305749663

theorem tailTrace_1777704 : CollatzResearch.WordTrace tailWord_1777704 prefixEnd_1777704 608544408946945305749663 := by
  unfold tailWord_1777704
  simp only [CollatzResearch.WordTrace]
  refine ⟨32419095775844745258434083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43225461034459660344578777 32419095775844745258434083)
  ·
    refine ⟨48628643663767117887651125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32419095775844745258434083 48628643663767117887651125)
    ·
      refine ⟨4558935343478167301967293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48628643663767117887651125 4558935343478167301967293)
      ·
        refine ⟨1709600753804312738237735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4558935343478167301967293 1709600753804312738237735)
        ·
          refine ⟨2564401130706469107356603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1709600753804312738237735 2564401130706469107356603)
          ·
            refine ⟨3846601696059703661034905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2564401130706469107356603 3846601696059703661034905)
            ·
              refine ⟨2884951272044777745776179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3846601696059703661034905 2884951272044777745776179)
              ·
                refine ⟨4327426908067166618664269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2884951272044777745776179 4327426908067166618664269)
                ·
                  refine ⟨1622785090525187481999101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4327426908067166618664269 1622785090525187481999101)
                  ·
                    refine ⟨608544408946945305749663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1622785090525187481999101 608544408946945305749663)
                    ·
                      rfl

theorem cell22_1777704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_1777704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777704 prefixEnd_1777704 := by exact prefixLift 1777704
  have htrace : WordTrace (prefixWord ++ tailWord_1777704) baseStart_1777704 baseEnd_1777704 := by
    simpa [prefixWord, tailWord_1777704, baseEnd_1777704] using wordTrace_append hprefix tailTrace_1777704
  have hstable : (prefixWord ++ tailWord_1777704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777704).length < 2 ^ (prefixWord ++ tailWord_1777704).sum := by decide
  have hdescent : baseEnd_1777704 < baseStart_1777704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777728 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 6]
def baseStart_1777728 : Nat := 118140960795 + 1777728 * 2 ^ 59
def prefixEnd_1777728 : Nat := 4983230072969 + 3 ^ 40 * 1777728 * 2
def baseEnd_1777728 : Nat := 202850874879139081049863

theorem tailTrace_1777728 : CollatzResearch.WordTrace tailWord_1777728 prefixEnd_1777728 202850874879139081049863 := by
  unfold tailWord_1777728
  simp only [CollatzResearch.WordTrace]
  refine ⟨32419533451801271307870919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43226044602401695077161225 32419533451801271307870919)
  ·
    refine ⟨48629300177701906961806379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32419533451801271307870919 48629300177701906961806379)
    ·
      refine ⟨72943950266552860442709569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48629300177701906961806379 72943950266552860442709569)
      ·
        refine ⟨54707962699914645332032177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72943950266552860442709569 54707962699914645332032177)
        ·
          refine ⟨41030972024935983999024133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54707962699914645332032177 41030972024935983999024133)
          ·
            refine ⟨7693307254675496999817025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41030972024935983999024133 7693307254675496999817025)
            ·
              refine ⟨5769980441006622749862769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7693307254675496999817025 5769980441006622749862769)
              ·
                refine ⟨4327485330754967062397077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5769980441006622749862769 4327485330754967062397077)
                ·
                  refine ⟨202850874879139081049863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4327485330754967062397077 202850874879139081049863)
                  ·
                    rfl

theorem cell22_1777728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 6].length) (baseStart_1777728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777728 prefixEnd_1777728 := by exact prefixLift 1777728
  have htrace : WordTrace (prefixWord ++ tailWord_1777728) baseStart_1777728 baseEnd_1777728 := by
    simpa [prefixWord, tailWord_1777728, baseEnd_1777728] using wordTrace_append hprefix tailTrace_1777728
  have hstable : (prefixWord ++ tailWord_1777728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777728).length < 2 ^ (prefixWord ++ tailWord_1777728).sum := by decide
  have hdescent : baseEnd_1777728 < baseStart_1777728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777760 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 4, 3]
def baseStart_1777760 : Nat := 118140960795 + 1777760 * 2 ^ 59
def prefixEnd_1777760 : Nat := 4983230072969 + 3 ^ 40 * 1777760 * 2
def baseEnd_1777760 : Nat := 608563578891379826349491

theorem tailTrace_1777760 : CollatzResearch.WordTrace tailWord_1777760 prefixEnd_1777760 608563578891379826349491 := by
  unfold tailWord_1777760
  simp only [CollatzResearch.WordTrace]
  refine ⟨32420117019743306040453367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43226822692991074720604489 32420117019743306040453367)
  ·
    refine ⟨48630175529614959060680051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32420117019743306040453367 48630175529614959060680051)
    ·
      refine ⟨72945263294422438591020077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48630175529614959060680051 72945263294422438591020077)
      ·
        refine ⟨27354473735408414471632529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72945263294422438591020077 27354473735408414471632529)
        ·
          refine ⟨20515855301556310853724397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27354473735408414471632529 20515855301556310853724397)
          ·
            refine ⟨7693445738083616570146649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20515855301556310853724397 7693445738083616570146649)
            ·
              refine ⟨5770084303562712427609987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7693445738083616570146649 5770084303562712427609987)
              ·
                refine ⟨8655126455344068641414981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5770084303562712427609987 8655126455344068641414981)
                ·
                  refine ⟨1622836210377012870265309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8655126455344068641414981 1622836210377012870265309)
                  ·
                    refine ⟨608563578891379826349491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1622836210377012870265309 608563578891379826349491)
                    ·
                      rfl

theorem cell22_1777760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 4, 3].length) (baseStart_1777760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777760 prefixEnd_1777760 := by exact prefixLift 1777760
  have htrace : WordTrace (prefixWord ++ tailWord_1777760) baseStart_1777760 baseEnd_1777760 := by
    simpa [prefixWord, tailWord_1777760, baseEnd_1777760] using wordTrace_append hprefix tailTrace_1777760
  have hstable : (prefixWord ++ tailWord_1777760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777760).length < 2 ^ (prefixWord ++ tailWord_1777760).sum := by decide
  have hdescent : baseEnd_1777760 < baseStart_1777760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777880 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 6]
def baseStart_1777880 : Nat := 118140960795 + 1777880 * 2 ^ 59
def prefixEnd_1777880 : Nat := 4983230072969 + 3 ^ 40 * 1777880 * 2
def baseEnd_1777880 : Nat := 202868219114579837783041

theorem tailTrace_1777880 : CollatzResearch.WordTrace tailWord_1777880 prefixEnd_1777880 202868219114579837783041 := by
  unfold tailWord_1777880
  simp only [CollatzResearch.WordTrace]
  refine ⟨32422305399525936287637547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43229740532701248383516729 32422305399525936287637547)
  ·
    refine ⟨48633458099288904431456321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32422305399525936287637547 48633458099288904431456321)
    ·
      refine ⟨36475093574466678323592241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48633458099288904431456321 36475093574466678323592241)
      ·
        refine ⟨27356320180850008742694181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36475093574466678323592241 27356320180850008742694181)
        ·
          refine ⟨5129310033909376639255159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27356320180850008742694181 5129310033909376639255159)
          ·
            refine ⟨7693965050864064958882739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5129310033909376639255159 7693965050864064958882739)
            ·
              refine ⟨11540947576296097438324109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7693965050864064958882739 11540947576296097438324109)
              ·
                refine ⟨4327855341111036539371541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11540947576296097438324109 4327855341111036539371541)
                ·
                  refine ⟨202868219114579837783041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4327855341111036539371541 202868219114579837783041)
                  ·
                    rfl

theorem cell22_1777880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 6].length) (baseStart_1777880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777880 prefixEnd_1777880 := by exact prefixLift 1777880
  have htrace : WordTrace (prefixWord ++ tailWord_1777880) baseStart_1777880 baseEnd_1777880 := by
    simpa [prefixWord, tailWord_1777880, baseEnd_1777880] using wordTrace_append hprefix tailTrace_1777880
  have hstable : (prefixWord ++ tailWord_1777880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777880).length < 2 ^ (prefixWord ++ tailWord_1777880).sum := by decide
  have hdescent : baseEnd_1777880 < baseStart_1777880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777914 : List Nat := [3, 1, 1, 1, 1, 7, 1, 3, 4]
def baseStart_1777914 : Nat := 118140960795 + 1777914 * 2 ^ 59
def prefixEnd_1777914 : Nat := 4983230072969 + 3 ^ 40 * 1777914 * 2
def baseEnd_1777914 : Nat := 202872098746191585999673

theorem tailTrace_1777914 : CollatzResearch.WordTrace tailWord_1777914 prefixEnd_1777914 202872098746191585999673 := by
  unfold tailWord_1777914
  simp only [CollatzResearch.WordTrace]
  refine ⟨16211462720232174095503199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43230567253952464254675197 16211462720232174095503199)
  ·
    refine ⟨24317194080348261143254799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16211462720232174095503199 24317194080348261143254799)
    ·
      refine ⟨36475791120522391714882199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24317194080348261143254799 36475791120522391714882199)
      ·
        refine ⟨54713686680783587572323299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36475791120522391714882199 54713686680783587572323299)
        ·
          refine ⟨82070530021175381358484949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54713686680783587572323299 82070530021175381358484949)
          ·
            refine ⟨1923528047371298000589491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 82070530021175381358484949 1923528047371298000589491)
            ·
              refine ⟨2885292071056947000884237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923528047371298000589491 2885292071056947000884237)
              ·
                refine ⟨1081984526646355125331589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2885292071056947000884237 1081984526646355125331589)
                ·
                  refine ⟨202872098746191585999673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1081984526646355125331589 202872098746191585999673)
                  ·
                    rfl

theorem cell22_1777914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_1777914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1777914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1777914 prefixEnd_1777914 := by exact prefixLift 1777914
  have htrace : WordTrace (prefixWord ++ tailWord_1777914) baseStart_1777914 baseEnd_1777914 := by
    simpa [prefixWord, tailWord_1777914, baseEnd_1777914] using wordTrace_append hprefix tailTrace_1777914
  have hstable : (prefixWord ++ tailWord_1777914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777914).length < 2 ^ (prefixWord ++ tailWord_1777914).sum := by decide
  have hdescent : baseEnd_1777914 < baseStart_1777914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778015 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 8]
def baseStart_1778015 : Nat := 118140960795 + 1778015 * 2 ^ 59
def prefixEnd_1778015 : Nat := 4983230072969 + 3 ^ 40 * 1778015 * 2
def baseEnd_1778015 : Nat := 202883623534214720407903

theorem tailTrace_1778015 : CollatzResearch.WordTrace tailWord_1778015 prefixEnd_1778015 202883623534214720407903 := by
  unfold tailWord_1778015
  simp only [CollatzResearch.WordTrace]
  refine ⟨64849534653562790631439499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43233023102375193754292999 64849534653562790631439499)
  ·
    refine ⟨97274301980344185947159249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64849534653562790631439499 97274301980344185947159249)
    ·
      refine ⟨72955726485258139460369437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97274301980344185947159249 72955726485258139460369437)
      ·
        refine ⟨27358397431971802297638539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72955726485258139460369437 27358397431971802297638539)
        ·
          refine ⟨41037596147957703446457809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27358397431971802297638539 41037596147957703446457809)
          ·
            refine ⟨30778197110968277584843357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41037596147957703446457809 30778197110968277584843357)
            ·
              refine ⟨11541823916613104094316259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30778197110968277584843357 11541823916613104094316259)
              ·
                refine ⟨17312735874919656141474389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11541823916613104094316259 17312735874919656141474389)
                ·
                  refine ⟨202883623534214720407903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17312735874919656141474389 202883623534214720407903)
                  ·
                    rfl

theorem cell22_1778015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 8].length) (baseStart_1778015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778015 prefixEnd_1778015 := by exact prefixLift 1778015
  have htrace : WordTrace (prefixWord ++ tailWord_1778015) baseStart_1778015 baseEnd_1778015 := by
    simpa [prefixWord, tailWord_1778015, baseEnd_1778015] using wordTrace_append hprefix tailTrace_1778015
  have hstable : (prefixWord ++ tailWord_1778015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778015).length < 2 ^ (prefixWord ++ tailWord_1778015).sum := by decide
  have hdescent : baseEnd_1778015 < baseStart_1778015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778034 : List Nat := [3, 2, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_1778034 : Nat := 118140960795 + 1778034 * 2 ^ 59
def prefixEnd_1778034 : Nat := 4983230072969 + 3 ^ 40 * 1778034 * 2
def baseEnd_1778034 : Nat := 608657374690934444998651

theorem tailTrace_1778034 : CollatzResearch.WordTrace tailWord_1778034 prefixEnd_1778034 608657374690934444998651 := by
  unfold tailWord_1778034
  simp only [CollatzResearch.WordTrace]
  refine ⟨16212556910123489219095289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43233485093662637917587437 16212556910123489219095289)
  ·
    refine ⟨12159417682592616914321467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16212556910123489219095289 12159417682592616914321467)
    ·
      refine ⟨18239126523888925371482201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12159417682592616914321467 18239126523888925371482201)
      ·
        refine ⟨13679344892916694028611651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18239126523888925371482201 13679344892916694028611651)
        ·
          refine ⟨20519017339375041042917477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13679344892916694028611651 20519017339375041042917477)
          ·
            refine ⟨3847315751132820195547027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20519017339375041042917477 3847315751132820195547027)
            ·
              refine ⟨5770973626699230293320541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3847315751132820195547027 5770973626699230293320541)
              ·
                refine ⟨2164115110012211359995203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5770973626699230293320541 2164115110012211359995203)
                ·
                  refine ⟨3246172665018317039992805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2164115110012211359995203 3246172665018317039992805)
                  ·
                    refine ⟨608657374690934444998651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3246172665018317039992805 608657374690934444998651)
                    ·
                      rfl

theorem cell22_1778034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_1778034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778034 prefixEnd_1778034 := by exact prefixLift 1778034
  have htrace : WordTrace (prefixWord ++ tailWord_1778034) baseStart_1778034 baseEnd_1778034 := by
    simpa [prefixWord, tailWord_1778034, baseEnd_1778034] using wordTrace_append hprefix tailTrace_1778034
  have hstable : (prefixWord ++ tailWord_1778034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778034).length < 2 ^ (prefixWord ++ tailWord_1778034).sum := by decide
  have hdescent : baseEnd_1778034 < baseStart_1778034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778038 : List Nat := [5, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_1778038 : Nat := 118140960795 + 1778038 * 2 ^ 59
def prefixEnd_1778038 : Nat := 4983230072969 + 3 ^ 40 * 1778038 * 2
def baseEnd_1778038 : Nat := 202886247990893255966213

theorem tailTrace_1778038 : CollatzResearch.WordTrace tailWord_1778038 prefixEnd_1778038 202886247990893255966213 := by
  unfold tailWord_1778038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4053148345779966597470423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43233582354986310373017845 4053148345779966597470423)
  ·
    refine ⟨6079722518669949896205635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4053148345779966597470423 6079722518669949896205635)
    ·
      refine ⟨9119583778004924844308453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6079722518669949896205635 9119583778004924844308453)
      ·
        refine ⟨1709921958375923408307835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9119583778004924844308453 1709921958375923408307835)
        ·
          refine ⟨2564882937563885112461753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1709921958375923408307835 2564882937563885112461753)
          ·
            refine ⟨1923662203172913834346315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2564882937563885112461753 1923662203172913834346315)
            ·
              refine ⟨2885493304759370751519473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923662203172913834346315 2885493304759370751519473)
              ·
                refine ⟨2164119978569528063639605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2885493304759370751519473 2164119978569528063639605)
                ·
                  refine ⟨202886247990893255966213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2164119978569528063639605 202886247990893255966213)
                  ·
                    rfl

theorem cell22_1778038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_1778038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778038 prefixEnd_1778038 := by exact prefixLift 1778038
  have htrace : WordTrace (prefixWord ++ tailWord_1778038) baseStart_1778038 baseEnd_1778038 := by
    simpa [prefixWord, tailWord_1778038, baseEnd_1778038] using wordTrace_append hprefix tailTrace_1778038
  have hstable : (prefixWord ++ tailWord_1778038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778038).length < 2 ^ (prefixWord ++ tailWord_1778038).sum := by decide
  have hdescent : baseEnd_1778038 < baseStart_1778038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778047 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 4, 3]
def baseStart_1778047 : Nat := 118140960795 + 1778047 * 2 ^ 59
def prefixEnd_1778047 : Nat := 4983230072969 + 3 ^ 40 * 1778047 * 2
def baseEnd_1778047 : Nat := 608661824856606744423611

theorem tailTrace_1778047 : CollatzResearch.WordTrace tailWord_1778047 prefixEnd_1778047 608661824856606744423611 := by
  unfold tailWord_1778047
  simp only [CollatzResearch.WordTrace]
  refine ⟨64850701789446860096604395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43233801192964573397736263 64850701789446860096604395)
  ·
    refine ⟨97276052684170290144906593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64850701789446860096604395 97276052684170290144906593)
    ·
      refine ⟨72957039513127717608679945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97276052684170290144906593 72957039513127717608679945)
      ·
        refine ⟨54717779634845788206509959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72957039513127717608679945 54717779634845788206509959)
        ·
          refine ⟨82076669452268682309764939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54717779634845788206509959 82076669452268682309764939)
          ·
            refine ⟨123115004178403023464647409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82076669452268682309764939 123115004178403023464647409)
            ·
              refine ⟨92336253133802267598485557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123115004178403023464647409 92336253133802267598485557)
              ·
                refine ⟨8656523731293962587358021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92336253133802267598485557 8656523731293962587358021)
                ·
                  refine ⟨1623098199617617985129629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8656523731293962587358021 1623098199617617985129629)
                  ·
                    refine ⟨608661824856606744423611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1623098199617617985129629 608661824856606744423611)
                    ·
                      rfl

theorem cell22_1778047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 3].length) (baseStart_1778047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778047 prefixEnd_1778047 := by exact prefixLift 1778047
  have htrace : WordTrace (prefixWord ++ tailWord_1778047) baseStart_1778047 baseEnd_1778047 := by
    simpa [prefixWord, tailWord_1778047, baseEnd_1778047] using wordTrace_append hprefix tailTrace_1778047
  have hstable : (prefixWord ++ tailWord_1778047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778047).length < 2 ^ (prefixWord ++ tailWord_1778047).sum := by decide
  have hdescent : baseEnd_1778047 < baseStart_1778047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778049 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 6]
def baseStart_1778049 : Nat := 118140960795 + 1778049 * 2 ^ 59
def prefixEnd_1778049 : Nat := 4983230072969 + 3 ^ 40 * 1778049 * 2
def baseEnd_1778049 : Nat := 202887503165826468624535

theorem tailTrace_1778049 : CollatzResearch.WordTrace tailWord_1778049 prefixEnd_1778049 202887503165826468624535 := by
  unfold tailWord_1778049
  simp only [CollatzResearch.WordTrace]
  refine ⟨64850774735439614438177201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43233849823626409625451467 64850774735439614438177201)
  ·
    refine ⟨48638081051579710828632901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64850774735439614438177201 48638081051579710828632901)
    ·
      refine ⟨9119640197171195780368669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48638081051579710828632901 9119640197171195780368669)
      ·
        refine ⟨3419865073939198417638251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9119640197171195780368669 3419865073939198417638251)
        ·
          refine ⟨5129797610908797626457377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3419865073939198417638251 5129797610908797626457377)
          ·
            refine ⟨3847348208181598219843033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5129797610908797626457377 3847348208181598219843033)
            ·
              refine ⟨2885511156136198664882275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3847348208181598219843033 2885511156136198664882275)
              ·
                refine ⟨4328266734204297997323413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885511156136198664882275 4328266734204297997323413)
                ·
                  refine ⟨202887503165826468624535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4328266734204297997323413 202887503165826468624535)
                  ·
                    rfl

theorem cell22_1778049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 6].length) (baseStart_1778049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778049 prefixEnd_1778049 := by exact prefixLift 1778049
  have htrace : WordTrace (prefixWord ++ tailWord_1778049) baseStart_1778049 baseEnd_1778049 := by
    simpa [prefixWord, tailWord_1778049, baseEnd_1778049] using wordTrace_append hprefix tailTrace_1778049
  have hstable : (prefixWord ++ tailWord_1778049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778049).length < 2 ^ (prefixWord ++ tailWord_1778049).sum := by decide
  have hdescent : baseEnd_1778049 < baseStart_1778049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778100 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 6]
def baseStart_1778100 : Nat := 118140960795 + 1778100 * 2 ^ 59
def prefixEnd_1778100 : Nat := 4983230072969 + 3 ^ 40 * 1778100 * 2
def baseEnd_1778100 : Nat := 202893322613244090949483

theorem tailTrace_1778100 : CollatzResearch.WordTrace tailWord_1778100 prefixEnd_1778100 202893322613244090949483 := by
  unfold tailWord_1778100
  simp only [CollatzResearch.WordTrace]
  refine ⟨32426317429127425074141877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43235089905503233432189169 32426317429127425074141877)
  ·
    refine ⟨3039967258980696100700801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32426317429127425074141877 3039967258980696100700801)
    ·
      refine ⟨2279975444235522075525601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3039967258980696100700801 2279975444235522075525601)
      ·
        refine ⟨1709981583176641556644201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2279975444235522075525601 1709981583176641556644201)
        ·
          refine ⟨1282486187382481167483151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1709981583176641556644201 1282486187382481167483151)
          ·
            refine ⟨1923729281073721751224727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282486187382481167483151 1923729281073721751224727)
            ·
              refine ⟨2885593921610582626837091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923729281073721751224727 2885593921610582626837091)
              ·
                refine ⟨4328390882415873940255637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885593921610582626837091 4328390882415873940255637)
                ·
                  refine ⟨202893322613244090949483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4328390882415873940255637 202893322613244090949483)
                  ·
                    rfl

theorem cell22_1778100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_1778100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778100 prefixEnd_1778100 := by exact prefixLift 1778100
  have htrace : WordTrace (prefixWord ++ tailWord_1778100) baseStart_1778100 baseEnd_1778100 := by
    simpa [prefixWord, tailWord_1778100, baseEnd_1778100] using wordTrace_append hprefix tailTrace_1778100
  have hstable : (prefixWord ++ tailWord_1778100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778100).length < 2 ^ (prefixWord ++ tailWord_1778100).sum := by decide
  have hdescent : baseEnd_1778100 < baseStart_1778100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778233 : List Nat := [1, 2, 1, 5, 1, 1, 5, 1, 2, 3]
def baseStart_1778233 : Nat := 118140960795 + 1778233 * 2 ^ 59
def prefixEnd_1778233 : Nat := 4983230072969 + 3 ^ 40 * 1778233 * 2
def baseEnd_1778233 : Nat := 608725496457764259273041

theorem tailTrace_1778233 : CollatzResearch.WordTrace tailWord_1778233 prefixEnd_1778233 608725496457764259273041 := by
  unfold tailWord_1778233
  simp only [CollatzResearch.WordTrace]
  refine ⟨64857485766773013862875353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43238323844515342575250235 64857485766773013862875353)
  ·
    refine ⟨48643114325079760397156515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64857485766773013862875353 48643114325079760397156515)
    ·
      refine ⟨72964671487619640595734773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48643114325079760397156515 72964671487619640595734773)
      ·
        refine ⟨6840437951964341305850135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72964671487619640595734773 6840437951964341305850135)
        ·
          refine ⟨10260656927946511958775203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6840437951964341305850135 10260656927946511958775203)
          ·
            refine ⟨15390985391919767938162805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10260656927946511958775203 15390985391919767938162805)
            ·
              refine ⟨1442904880492478244202763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15390985391919767938162805 1442904880492478244202763)
              ·
                refine ⟨2164357320738717366304145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442904880492478244202763 2164357320738717366304145)
                ·
                  refine ⟨1623267990554038024728109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2164357320738717366304145 1623267990554038024728109)
                  ·
                    refine ⟨608725496457764259273041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1623267990554038024728109 608725496457764259273041)
                    ·
                      rfl

theorem cell22_1778233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 2, 3].length) (baseStart_1778233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778233 prefixEnd_1778233 := by exact prefixLift 1778233
  have htrace : WordTrace (prefixWord ++ tailWord_1778233) baseStart_1778233 baseEnd_1778233 := by
    simpa [prefixWord, tailWord_1778233, baseEnd_1778233] using wordTrace_append hprefix tailTrace_1778233
  have hstable : (prefixWord ++ tailWord_1778233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778233).length < 2 ^ (prefixWord ++ tailWord_1778233).sum := by decide
  have hdescent : baseEnd_1778233 < baseStart_1778233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778351 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 1, 5]
def baseStart_1778351 : Nat := 118140960795 + 1778351 * 2 ^ 59
def prefixEnd_1778351 : Nat := 4983230072969 + 3 ^ 40 * 1778351 * 2
def baseEnd_1778351 : Nat := 608765890269251284822679

theorem tailTrace_1778351 : CollatzResearch.WordTrace tailWord_1778351 prefixEnd_1778351 608765890269251284822679 := by
  unfold tailWord_1778351
  simp only [CollatzResearch.WordTrace]
  refine ⟨64861789580345520015670907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43241193053563680010447271 64861789580345520015670907)
  ·
    refine ⟨97292684370518280023506361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64861789580345520015670907 97292684370518280023506361)
    ·
      refine ⟨72969513277888710017629771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97292684370518280023506361 72969513277888710017629771)
      ·
        refine ⟨109454269916833065026444657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72969513277888710017629771 109454269916833065026444657)
        ·
          refine ⟨82090702437624798769833493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109454269916833065026444657 82090702437624798769833493)
          ·
            refine ⟨3848001676763662442335945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82090702437624798769833493 3848001676763662442335945)
            ·
              refine ⟨2886001257572746831751959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3848001676763662442335945 2886001257572746831751959)
              ·
                refine ⟨4329001886359120247627939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886001257572746831751959 4329001886359120247627939)
                ·
                  refine ⟨6493502829538680371441909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4329001886359120247627939 6493502829538680371441909)
                  ·
                    refine ⟨608765890269251284822679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6493502829538680371441909 608765890269251284822679)
                    ·
                      rfl

theorem cell22_1778351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_1778351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778351 prefixEnd_1778351 := by exact prefixLift 1778351
  have htrace : WordTrace (prefixWord ++ tailWord_1778351) baseStart_1778351 baseEnd_1778351 := by
    simpa [prefixWord, tailWord_1778351, baseEnd_1778351] using wordTrace_append hprefix tailTrace_1778351
  have hstable : (prefixWord ++ tailWord_1778351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778351).length < 2 ^ (prefixWord ++ tailWord_1778351).sum := by decide
  have hdescent : baseEnd_1778351 < baseStart_1778351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778353 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 6]
def baseStart_1778353 : Nat := 118140960795 + 1778353 * 2 ^ 59
def prefixEnd_1778353 : Nat := 4983230072969 + 3 ^ 40 * 1778353 * 2
def baseEnd_1778353 : Nat := 202922191636707982090891

theorem tailTrace_1778353 : CollatzResearch.WordTrace tailWord_1778353 prefixEnd_1778353 202922191636707982090891 := by
  unfold tailWord_1778353
  simp only [CollatzResearch.WordTrace]
  refine ⟨64861862526338274357243713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43241241684225516238162475 64861862526338274357243713)
  ·
    refine ⟨48646396894753705767932785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64861862526338274357243713 48646396894753705767932785)
    ·
      refine ⟨36484797671065279325949589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48646396894753705767932785 36484797671065279325949589)
      ·
        refine ⟨1710224890831184968403887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36484797671065279325949589 1710224890831184968403887)
        ·
          refine ⟨2565337336246777452605831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1710224890831184968403887 2565337336246777452605831)
          ·
            refine ⟨3848006004370166178908747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2565337336246777452605831 3848006004370166178908747)
            ·
              refine ⟨5772009006555249268363121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3848006004370166178908747 5772009006555249268363121)
              ·
                refine ⟨4329006754916436951272341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5772009006555249268363121 4329006754916436951272341)
                ·
                  refine ⟨202922191636707982090891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4329006754916436951272341 202922191636707982090891)
                  ·
                    rfl

theorem cell22_1778353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 6].length) (baseStart_1778353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778353 prefixEnd_1778353 := by exact prefixLift 1778353
  have htrace : WordTrace (prefixWord ++ tailWord_1778353) baseStart_1778353 baseEnd_1778353 := by
    simpa [prefixWord, tailWord_1778353, baseEnd_1778353] using wordTrace_append hprefix tailTrace_1778353
  have hstable : (prefixWord ++ tailWord_1778353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778353).length < 2 ^ (prefixWord ++ tailWord_1778353).sum := by decide
  have hdescent : baseEnd_1778353 < baseStart_1778353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778366 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1778366 : Nat := 118140960795 + 1778366 * 2 ^ 59
def prefixEnd_1778366 : Nat := 4983230072969 + 3 ^ 40 * 1778366 * 2
def baseEnd_1778366 : Nat := 608771025075796245697633

theorem tailTrace_1778366 : CollatzResearch.WordTrace tailWord_1778366 prefixEnd_1778366 608771025075796245697633 := by
  unfold tailWord_1778366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8107792084411397197183369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43241557783527451718311301 8107792084411397197183369)
  ·
    refine ⟨6080844063308547897887527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8107792084411397197183369 6080844063308547897887527)
    ·
      refine ⟨9121266094962821846831291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6080844063308547897887527 9121266094962821846831291)
      ·
        refine ⟨13681899142444232770246937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9121266094962821846831291 13681899142444232770246937)
        ·
          refine ⟨10261424356833174577685203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13681899142444232770246937 10261424356833174577685203)
          ·
            refine ⟨15392136535249761866527805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10261424356833174577685203 15392136535249761866527805)
            ·
              refine ⟨5772051200718660699947927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15392136535249761866527805 5772051200718660699947927)
              ·
                refine ⟨8658076801077991049921891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5772051200718660699947927 8658076801077991049921891)
                ·
                  refine ⟨12987115201616986574882837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8658076801077991049921891 12987115201616986574882837)
                  ·
                    refine ⟨608771025075796245697633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12987115201616986574882837 608771025075796245697633)
                    ·
                      rfl

theorem cell22_1778366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1778366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778366 prefixEnd_1778366 := by exact prefixLift 1778366
  have htrace : WordTrace (prefixWord ++ tailWord_1778366) baseStart_1778366 baseEnd_1778366 := by
    simpa [prefixWord, tailWord_1778366, baseEnd_1778366] using wordTrace_append hprefix tailTrace_1778366
  have hstable : (prefixWord ++ tailWord_1778366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778366).length < 2 ^ (prefixWord ++ tailWord_1778366).sum := by decide
  have hdescent : baseEnd_1778366 < baseStart_1778366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778413 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_1778413 : Nat := 118140960795 + 1778413 * 2 ^ 59
def prefixEnd_1778413 : Nat := 4983230072969 + 3 ^ 40 * 1778413 * 2
def baseEnd_1778413 : Nat := 608787114136303789772489

theorem tailTrace_1778413 : CollatzResearch.WordTrace tailWord_1778413 prefixEnd_1778413 608787114136303789772489 := by
  unfold tailWord_1778413
  simp only [CollatzResearch.WordTrace]
  refine ⟨64864050906120904604427893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43242700604080603069618595 64864050906120904604427893)
  ·
    refine ⟨6081004772448834806665115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64864050906120904604427893 6081004772448834806665115)
    ·
      refine ⟨9121507158673252209997673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6081004772448834806665115 9121507158673252209997673)
      ·
        refine ⟨6841130369004939157498255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9121507158673252209997673 6841130369004939157498255)
        ·
          refine ⟨10261695553507408736247383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6841130369004939157498255 10261695553507408736247383)
          ·
            refine ⟨15392543330261113104371075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10261695553507408736247383 15392543330261113104371075)
            ·
              refine ⟨23088814995391669656556613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15392543330261113104371075 23088814995391669656556613)
              ·
                refine ⟨4329152811635938060604365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23088814995391669656556613 4329152811635938060604365)
                ·
                  refine ⟨1623432304363476772726637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4329152811635938060604365 1623432304363476772726637)
                  ·
                    refine ⟨608787114136303789772489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1623432304363476772726637 608787114136303789772489)
                    ·
                      rfl

theorem cell22_1778413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_1778413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778413 prefixEnd_1778413 := by exact prefixLift 1778413
  have htrace : WordTrace (prefixWord ++ tailWord_1778413) baseStart_1778413 baseEnd_1778413 := by
    simpa [prefixWord, tailWord_1778413, baseEnd_1778413] using wordTrace_append hprefix tailTrace_1778413
  have hstable : (prefixWord ++ tailWord_1778413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778413).length < 2 ^ (prefixWord ++ tailWord_1778413).sum := by decide
  have hdescent : baseEnd_1778413 < baseStart_1778413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778421 : List Nat := [1, 3, 6, 1, 2, 1, 1, 3, 4]
def baseStart_1778421 : Nat := 118140960795 + 1778421 * 2 ^ 59
def prefixEnd_1778421 : Nat := 4983230072969 + 3 ^ 40 * 1778421 * 2
def baseEnd_1778421 : Nat := 202929950899931478524155

theorem tailTrace_1778421 : CollatzResearch.WordTrace tailWord_1778421 prefixEnd_1778421 202929950899931478524155 := by
  unfold tailWord_1778421
  simp only [CollatzResearch.WordTrace]
  refine ⟨64864342690091921970719117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43242895126727947980479411 64864342690091921970719117)
  ·
    refine ⟨24324128508784470739019669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64864342690091921970719117 24324128508784470739019669)
    ·
      refine ⟨1140193523849272065891547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24324128508784470739019669 1140193523849272065891547)
      ·
        refine ⟨1710290285773908098837321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1140193523849272065891547 1710290285773908098837321)
        ·
          refine ⟨1282717714330431074127991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1710290285773908098837321 1282717714330431074127991)
          ·
            refine ⟨1924076571495646611191987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282717714330431074127991 1924076571495646611191987)
            ·
              refine ⟨2886114857243469916787981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1924076571495646611191987 2886114857243469916787981)
              ·
                refine ⟨1082293071466301218795493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2886114857243469916787981 1082293071466301218795493)
                ·
                  refine ⟨202929950899931478524155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1082293071466301218795493 202929950899931478524155)
                  ·
                    rfl

theorem cell22_1778421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_1778421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778421 prefixEnd_1778421 := by exact prefixLift 1778421
  have htrace : WordTrace (prefixWord ++ tailWord_1778421) baseStart_1778421 baseEnd_1778421 := by
    simpa [prefixWord, tailWord_1778421, baseEnd_1778421] using wordTrace_append hprefix tailTrace_1778421
  have hstable : (prefixWord ++ tailWord_1778421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778421).length < 2 ^ (prefixWord ++ tailWord_1778421).sum := by decide
  have hdescent : baseEnd_1778421 < baseStart_1778421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778456 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 3, 4]
def baseStart_1778456 : Nat := 118140960795 + 1778456 * 2 ^ 59
def prefixEnd_1778456 : Nat := 4983230072969 + 3 ^ 40 * 1778456 * 2
def baseEnd_1778456 : Nat := 608801833915066010947357

theorem tailTrace_1778456 : CollatzResearch.WordTrace tailWord_1778456 prefixEnd_1778456 608801833915066010947357 := by
  unfold tailWord_1778456
  simp only [CollatzResearch.WordTrace]
  refine ⟨32432809622482561474121611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43243746163310081965495481 32432809622482561474121611)
  ·
    refine ⟨48649214433723842211182417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32432809622482561474121611 48649214433723842211182417)
    ·
      refine ⟨36486910825292881658386813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48649214433723842211182417 36486910825292881658386813)
      ·
        refine ⟨13682591559484830621895055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36486910825292881658386813 13682591559484830621895055)
        ·
          refine ⟨20523887339227245932842583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13682591559484830621895055 20523887339227245932842583)
          ·
            refine ⟨30785831008840868899263875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20523887339227245932842583 30785831008840868899263875)
            ·
              refine ⟨46178746513261303348895813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30785831008840868899263875 46178746513261303348895813)
              ·
                refine ⟨8658514971236494377917965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46178746513261303348895813 8658514971236494377917965)
                ·
                  refine ⟨3246943114213685391719237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8658514971236494377917965 3246943114213685391719237)
                  ·
                    refine ⟨608801833915066010947357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3246943114213685391719237 608801833915066010947357)
                    ·
                      rfl

theorem cell22_1778456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_1778456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778456 prefixEnd_1778456 := by exact prefixLift 1778456
  have htrace : WordTrace (prefixWord ++ tailWord_1778456) baseStart_1778456 baseEnd_1778456 := by
    simpa [prefixWord, tailWord_1778456, baseEnd_1778456] using wordTrace_append hprefix tailTrace_1778456
  have hstable : (prefixWord ++ tailWord_1778456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778456).length < 2 ^ (prefixWord ++ tailWord_1778456).sum := by decide
  have hdescent : baseEnd_1778456 < baseStart_1778456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778460 : List Nat := [2, 2, 3, 1, 1, 5, 2, 1, 5]
def baseStart_1778460 : Nat := 118140960795 + 1778460 * 2 ^ 59
def prefixEnd_1778460 : Nat := 4983230072969 + 3 ^ 40 * 1778460 * 2
def baseEnd_1778460 : Nat := 202934401065603777949115

theorem tailTrace_1778460 : CollatzResearch.WordTrace tailWord_1778460 prefixEnd_1778460 202934401065603777949115 := by
  unfold tailWord_1778460
  simp only [CollatzResearch.WordTrace]
  refine ⟨32432882568475315815694417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43243843424633754420925889 32432882568475315815694417)
  ·
    refine ⟨24324661926356486861770813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32432882568475315815694417 24324661926356486861770813)
    ·
      refine ⟨9121748222383682573164055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24324661926356486861770813 9121748222383682573164055)
      ·
        refine ⟨13682622333575523859746083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9121748222383682573164055 13682622333575523859746083)
        ·
          refine ⟨20523933500363285789619125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13682622333575523859746083 20523933500363285789619125)
          ·
            refine ⟨1924118765659058042776793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20523933500363285789619125 1924118765659058042776793)
            ·
              refine ⟨1443089074244293532082595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1924118765659058042776793 1443089074244293532082595)
              ·
                refine ⟨2164633611366440298123893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443089074244293532082595 2164633611366440298123893)
                ·
                  refine ⟨202934401065603777949115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2164633611366440298123893 202934401065603777949115)
                  ·
                    rfl

theorem cell22_1778460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_1778460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778460 prefixEnd_1778460 := by exact prefixLift 1778460
  have htrace : WordTrace (prefixWord ++ tailWord_1778460) baseStart_1778460 baseEnd_1778460 := by
    simpa [prefixWord, tailWord_1778460, baseEnd_1778460] using wordTrace_append hprefix tailTrace_1778460
  have hstable : (prefixWord ++ tailWord_1778460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778460).length < 2 ^ (prefixWord ++ tailWord_1778460).sum := by decide
  have hdescent : baseEnd_1778460 < baseStart_1778460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778488 : List Nat := [2, 1, 2, 1, 3, 2, 2, 5, 4]
def baseStart_1778488 : Nat := 118140960795 + 1778488 * 2 ^ 59
def prefixEnd_1778488 : Nat := 4983230072969 + 3 ^ 40 * 1778488 * 2
def baseEnd_1778488 : Nat := 202937596056342864715753

theorem tailTrace_1778488 : CollatzResearch.WordTrace tailWord_1778488 prefixEnd_1778488 202937596056342864715753 := by
  unfold tailWord_1778488
  simp only [CollatzResearch.WordTrace]
  refine ⟨32433393190424596206704059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43244524253899461608938745 32433393190424596206704059)
  ·
    refine ⟨48650089785636894310056089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32433393190424596206704059 48650089785636894310056089)
    ·
      refine ⟨36487567339227670732542067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48650089785636894310056089 36487567339227670732542067)
      ·
        refine ⟨54731351008841506098813101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36487567339227670732542067 54731351008841506098813101)
        ·
          refine ⟨20524256628315564787054913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54731351008841506098813101 20524256628315564787054913)
          ·
            refine ⟨15393192471236673590291185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20524256628315564787054913 15393192471236673590291185)
            ·
              refine ⟨11544894353427505192718389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15393192471236673590291185 11544894353427505192718389)
              ·
                refine ⟨1082333845633828611817349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11544894353427505192718389 1082333845633828611817349)
                ·
                  refine ⟨202937596056342864715753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1082333845633828611817349 202937596056342864715753)
                  ·
                    rfl

theorem cell22_1778488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 4].length) (baseStart_1778488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778488 prefixEnd_1778488 := by exact prefixLift 1778488
  have htrace : WordTrace (prefixWord ++ tailWord_1778488) baseStart_1778488 baseEnd_1778488 := by
    simpa [prefixWord, tailWord_1778488, baseEnd_1778488] using wordTrace_append hprefix tailTrace_1778488
  have hstable : (prefixWord ++ tailWord_1778488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778488).length < 2 ^ (prefixWord ++ tailWord_1778488).sum := by decide
  have hdescent : baseEnd_1778488 < baseStart_1778488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778501 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 4, 4]
def baseStart_1778501 : Nat := 118140960795 + 1778501 * 2 ^ 59
def prefixEnd_1778501 : Nat := 4983230072969 + 3 ^ 40 * 1778501 * 2
def baseEnd_1778501 : Nat := 608817238334700893572219

theorem tailTrace_1778501 : CollatzResearch.WordTrace tailWord_1778501 prefixEnd_1778501 608817238334700893572219 := by
  unfold tailWord_1778501
  simp only [CollatzResearch.WordTrace]
  refine ⟨64867260529802095633631357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43244840353201397089087571 64867260529802095633631357)
  ·
    refine ⟨24325222698675785862611759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64867260529802095633631357 24325222698675785862611759)
    ·
      refine ⟨36487834048013678793917639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24325222698675785862611759 36487834048013678793917639)
      ·
        refine ⟨54731751072020518190876459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36487834048013678793917639 54731751072020518190876459)
        ·
          refine ⟨82097626608030777286314689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54731751072020518190876459 82097626608030777286314689)
          ·
            refine ⟨61573219956023082964736017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82097626608030777286314689 61573219956023082964736017)
            ·
              refine ⟨46179914967017312223552013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61573219956023082964736017 46179914967017312223552013)
              ·
                refine ⟨17317468112631492083832005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46179914967017312223552013 17317468112631492083832005)
                ·
                  refine ⟨3247025271118404765718501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17317468112631492083832005 3247025271118404765718501)
                  ·
                    refine ⟨608817238334700893572219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3247025271118404765718501 608817238334700893572219)
                    ·
                      rfl

theorem cell22_1778501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_1778501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778501 prefixEnd_1778501 := by exact prefixLift 1778501
  have htrace : WordTrace (prefixWord ++ tailWord_1778501) baseStart_1778501 baseEnd_1778501 := by
    simpa [prefixWord, tailWord_1778501, baseEnd_1778501] using wordTrace_append hprefix tailTrace_1778501
  have hstable : (prefixWord ++ tailWord_1778501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778501).length < 2 ^ (prefixWord ++ tailWord_1778501).sum := by decide
  have hdescent : baseEnd_1778501 < baseStart_1778501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778505 : List Nat := [1, 2, 1, 1, 2, 5, 4, 2, 4]
def baseStart_1778505 : Nat := 118140960795 + 1778505 * 2 ^ 59
def prefixEnd_1778505 : Nat := 4983230072969 + 3 ^ 40 * 1778505 * 2
def baseEnd_1778505 : Nat := 202939535872148738824069

theorem tailTrace_1778505 : CollatzResearch.WordTrace tailWord_1778505 prefixEnd_1778505 202939535872148738824069 := by
  unfold tailWord_1778505
  simp only [CollatzResearch.WordTrace]
  refine ⟨64867406421787604316776969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43244937614525069544517979 64867406421787604316776969)
  ·
    refine ⟨48650554816340703237582727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64867406421787604316776969 48650554816340703237582727)
    ·
      refine ⟨72975832224511054856374091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48650554816340703237582727 72975832224511054856374091)
      ·
        refine ⟨109463748336766582284561137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72975832224511054856374091 109463748336766582284561137)
        ·
          refine ⟨82097811252574936713420853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109463748336766582284561137 82097811252574936713420853)
          ·
            refine ⟨7696669804928900316883205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82097811252574936713420853 7696669804928900316883205)
            ·
              refine ⟨1443125588424168809415601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7696669804928900316883205 1443125588424168809415601)
              ·
                refine ⟨1082344191318126607061701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1443125588424168809415601 1082344191318126607061701)
                ·
                  refine ⟨202939535872148738824069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1082344191318126607061701 202939535872148738824069)
                  ·
                    rfl

theorem cell22_1778505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 4].length) (baseStart_1778505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778505 prefixEnd_1778505 := by exact prefixLift 1778505
  have htrace : WordTrace (prefixWord ++ tailWord_1778505) baseStart_1778505 baseEnd_1778505 := by
    simpa [prefixWord, tailWord_1778505, baseEnd_1778505] using wordTrace_append hprefix tailTrace_1778505
  have hstable : (prefixWord ++ tailWord_1778505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778505).length < 2 ^ (prefixWord ++ tailWord_1778505).sum := by decide
  have hdescent : baseEnd_1778505 < baseStart_1778505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778535 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 2, 4]
def baseStart_1778535 : Nat := 118140960795 + 1778535 * 2 ^ 59
def prefixEnd_1778535 : Nat := 4983230072969 + 3 ^ 40 * 1778535 * 2
def baseEnd_1778535 : Nat := 608828877229536138222115

theorem tailTrace_1778535 : CollatzResearch.WordTrace tailWord_1778535 prefixEnd_1778535 608828877229536138222115 := by
  unfold tailWord_1778535
  simp only [CollatzResearch.WordTrace]
  refine ⟨64868500611678919440369059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43245667074452612960246039 64868500611678919440369059)
  ·
    refine ⟨97302750917518379160553589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64868500611678919440369059 97302750917518379160553589)
    ·
      refine ⟨9122132898517348046301899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97302750917518379160553589 9122132898517348046301899)
      ·
        refine ⟨13683199347776022069452849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9122132898517348046301899 13683199347776022069452849)
        ·
          refine ⟨10262399510832016552089637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13683199347776022069452849 10262399510832016552089637)
          ·
            refine ⟨1924199908281003103516807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10262399510832016552089637 1924199908281003103516807)
            ·
              refine ⟨2886299862421504655275211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1924199908281003103516807 2886299862421504655275211)
              ·
                refine ⟨4329449793632256982912817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886299862421504655275211 4329449793632256982912817)
                ·
                  refine ⟨3247087345224192737184613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4329449793632256982912817 3247087345224192737184613)
                  ·
                    refine ⟨608828877229536138222115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3247087345224192737184613 608828877229536138222115)
                    ·
                      rfl

theorem cell22_1778535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_1778535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778535 prefixEnd_1778535 := by exact prefixLift 1778535
  have htrace : WordTrace (prefixWord ++ tailWord_1778535) baseStart_1778535 baseEnd_1778535 := by
    simpa [prefixWord, tailWord_1778535, baseEnd_1778535] using wordTrace_append hprefix tailTrace_1778535
  have hstable : (prefixWord ++ tailWord_1778535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778535).length < 2 ^ (prefixWord ++ tailWord_1778535).sum := by decide
  have hdescent : baseEnd_1778535 < baseStart_1778535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778565 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 3, 3]
def baseStart_1778565 : Nat := 118140960795 + 1778565 * 2 ^ 59
def prefixEnd_1778565 : Nat := 4983230072969 + 3 ^ 40 * 1778565 * 2
def baseEnd_1778565 : Nat := 608839146842626059972023

theorem tailTrace_1778565 : CollatzResearch.WordTrace tailWord_1778565 prefixEnd_1778565 608839146842626059972023 := by
  unfold tailWord_1778565
  simp only [CollatzResearch.WordTrace]
  refine ⟨64869594801570234563961149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43246396534380156375974099 64869594801570234563961149)
  ·
    refine ⟨24326098050588837961485431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64869594801570234563961149 24326098050588837961485431)
    ·
      refine ⟨36489147075883256942228147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24326098050588837961485431 36489147075883256942228147)
      ·
        refine ⟨54733720613824885413342221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36489147075883256942228147 54733720613824885413342221)
        ·
          refine ⟨20525145230184332030003333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54733720613824885413342221 20525145230184332030003333)
          ·
            refine ⟨3848464730659562255625625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20525145230184332030003333 3848464730659562255625625)
            ·
              refine ⟨2886348547994671691719219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3848464730659562255625625 2886348547994671691719219)
              ·
                refine ⟨4329522821992007537578829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886348547994671691719219 4329522821992007537578829)
                ·
                  refine ⟨1623571058247002826592061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4329522821992007537578829 1623571058247002826592061)
                  ·
                    refine ⟨608839146842626059972023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1623571058247002826592061 608839146842626059972023)
                    ·
                      rfl

theorem cell22_1778565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_1778565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778565 prefixEnd_1778565 := by exact prefixLift 1778565
  have htrace : WordTrace (prefixWord ++ tailWord_1778565) baseStart_1778565 baseEnd_1778565 := by
    simpa [prefixWord, tailWord_1778565, baseEnd_1778565] using wordTrace_append hprefix tailTrace_1778565
  have hstable : (prefixWord ++ tailWord_1778565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778565).length < 2 ^ (prefixWord ++ tailWord_1778565).sum := by decide
  have hdescent : baseEnd_1778565 < baseStart_1778565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778576 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 6, 5]
def baseStart_1778576 : Nat := 118140960795 + 1778576 * 2 ^ 59
def prefixEnd_1778576 : Nat := 4983230072969 + 3 ^ 40 * 1778576 * 2
def baseEnd_1778576 : Nat := 608842912367425697946989

theorem tailTrace_1778576 : CollatzResearch.WordTrace tailWord_1778576 prefixEnd_1778576 608842912367425697946989 := by
  unfold tailWord_1778576
  simp only [CollatzResearch.WordTrace]
  refine ⟨32434998002265191721305791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43246664003020255628407721 32434998002265191721305791)
  ·
    refine ⟨48652497003397787581958687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32434998002265191721305791 48652497003397787581958687)
    ·
      refine ⟨72978745505096681372938031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48652497003397787581958687 72978745505096681372938031)
      ·
        refine ⟨109468118257645022059407047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72978745505096681372938031 109468118257645022059407047)
        ·
          refine ⟨164202177386467533089110571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109468118257645022059407047 164202177386467533089110571)
          ·
            refine ⟨246303266079701299633665857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164202177386467533089110571 246303266079701299633665857)
            ·
              refine ⟨184727449559775974725249393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246303266079701299633665857 184727449559775974725249393)
              ·
                refine ⟨138545587169831981043937045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184727449559775974725249393 138545587169831981043937045)
                ·
                  refine ⟨6494324398585874111434549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138545587169831981043937045 6494324398585874111434549)
                  ·
                    refine ⟨608842912367425697946989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6494324398585874111434549 608842912367425697946989)
                    ·
                      rfl

theorem cell22_1778576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_1778576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778576 prefixEnd_1778576 := by exact prefixLift 1778576
  have htrace : WordTrace (prefixWord ++ tailWord_1778576) baseStart_1778576 baseEnd_1778576 := by
    simpa [prefixWord, tailWord_1778576, baseEnd_1778576] using wordTrace_append hprefix tailTrace_1778576
  have hstable : (prefixWord ++ tailWord_1778576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778576).length < 2 ^ (prefixWord ++ tailWord_1778576).sum := by decide
  have hdescent : baseEnd_1778576 < baseStart_1778576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778642 : List Nat := [3, 2, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_1778642 : Nat := 118140960795 + 1778642 * 2 ^ 59
def prefixEnd_1778642 : Nat := 4983230072969 + 3 ^ 40 * 1778642 * 2
def baseEnd_1778642 : Nat := 608865505516223525796787

theorem tailTrace_1778642 : CollatzResearch.WordTrace tailWord_1778642 prefixEnd_1778642 608865505516223525796787 := by
  unfold tailWord_1778642
  simp only [CollatzResearch.WordTrace]
  refine ⟨16218100805572819178628545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43248268814860851143009453 16218100805572819178628545)
  ·
    refine ⟨12163575604179614383971409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16218100805572819178628545 12163575604179614383971409)
    ·
      refine ⟨9122681703134710787978557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12163575604179614383971409 9122681703134710787978557)
      ·
        refine ⟨3421005638675516545491959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9122681703134710787978557 3421005638675516545491959)
        ·
          refine ⟨5131508458013274818237939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3421005638675516545491959 5131508458013274818237939)
          ·
            refine ⟨7697262687019912227356909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5131508458013274818237939 7697262687019912227356909)
            ·
              refine ⟨2886473507632467085258841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7697262687019912227356909 2886473507632467085258841)
              ·
                refine ⟨2164855130724350313944131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2886473507632467085258841 2164855130724350313944131)
                ·
                  refine ⟨3247282696086525470916197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2164855130724350313944131 3247282696086525470916197)
                  ·
                    refine ⟨608865505516223525796787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3247282696086525470916197 608865505516223525796787)
                    ·
                      rfl

theorem cell22_1778642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_1778642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778642 prefixEnd_1778642 := by exact prefixLift 1778642
  have htrace : WordTrace (prefixWord ++ tailWord_1778642) baseStart_1778642 baseEnd_1778642 := by
    simpa [prefixWord, tailWord_1778642, baseEnd_1778642] using wordTrace_append hprefix tailTrace_1778642
  have hstable : (prefixWord ++ tailWord_1778642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778642).length < 2 ^ (prefixWord ++ tailWord_1778642).sum := by decide
  have hdescent : baseEnd_1778642 < baseStart_1778642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778655 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 1, 5]
def baseStart_1778655 : Nat := 118140960795 + 1778655 * 2 ^ 59
def prefixEnd_1778655 : Nat := 4983230072969 + 3 ^ 40 * 1778655 * 2
def baseEnd_1778655 : Nat := 608869955681895825221747

theorem tailTrace_1778655 : CollatzResearch.WordTrace tailWord_1778655 prefixEnd_1778655 608869955681895825221747 := by
  unfold tailWord_1778655
  simp only [CollatzResearch.WordTrace]
  refine ⟨64872877371244179934737419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43248584914162786623158279 64872877371244179934737419)
  ·
    refine ⟨97309316056866269902106129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64872877371244179934737419 97309316056866269902106129)
    ·
      refine ⟨72981987042649702426579597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97309316056866269902106129 72981987042649702426579597)
      ·
        refine ⟨27368245140993638409967349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72981987042649702426579597 27368245140993638409967349)
        ·
          refine ⟨2565772981968153600934439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27368245140993638409967349 2565772981968153600934439)
          ·
            refine ⟨3848659472952230401401659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2565772981968153600934439 3848659472952230401401659)
            ·
              refine ⟨5772989209428345602102489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3848659472952230401401659 5772989209428345602102489)
              ·
                refine ⟨4329741907071259201576867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5772989209428345602102489 4329741907071259201576867)
                ·
                  refine ⟨6494612860606888802365301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4329741907071259201576867 6494612860606888802365301)
                  ·
                    refine ⟨608869955681895825221747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6494612860606888802365301 608869955681895825221747)
                    ·
                      rfl

theorem cell22_1778655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_1778655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778655 prefixEnd_1778655 := by exact prefixLift 1778655
  have htrace : WordTrace (prefixWord ++ tailWord_1778655) baseStart_1778655 baseEnd_1778655 := by
    simpa [prefixWord, tailWord_1778655, baseEnd_1778655] using wordTrace_append hprefix tailTrace_1778655
  have hstable : (prefixWord ++ tailWord_1778655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778655).length < 2 ^ (prefixWord ++ tailWord_1778655).sum := by decide
  have hdescent : baseEnd_1778655 < baseStart_1778655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778674 : List Nat := [3, 2, 1, 5, 1, 1, 1, 4, 4]
def baseStart_1778674 : Nat := 118140960795 + 1778674 * 2 ^ 59
def prefixEnd_1778674 : Nat := 4983230072969 + 3 ^ 40 * 1778674 * 2
def baseEnd_1778674 : Nat := 202958819923395369665563

theorem tailTrace_1778674 : CollatzResearch.WordTrace tailWord_1778674 prefixEnd_1778674 202958819923395369665563 := by
  unfold tailWord_1778674
  simp only [CollatzResearch.WordTrace]
  refine ⟨16218392589543836544919769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43249046905450230786452717 16218392589543836544919769)
  ·
    refine ⟨12163794442157877408689827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16218392589543836544919769 12163794442157877408689827)
    ·
      refine ⟨18245691663236816113034741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12163794442157877408689827 18245691663236816113034741)
      ·
        refine ⟨1710533593428451510597007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18245691663236816113034741 1710533593428451510597007)
        ·
          refine ⟨2565800390142677265895511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1710533593428451510597007 2565800390142677265895511)
          ·
            refine ⟨3848700585214015898843267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2565800390142677265895511 3848700585214015898843267)
            ·
              refine ⟨5773050877821023848264901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3848700585214015898843267 5773050877821023848264901)
              ·
                refine ⟨1082447039591441971549669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5773050877821023848264901 1082447039591441971549669)
                ·
                  refine ⟨202958819923395369665563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1082447039591441971549669 202958819923395369665563)
                  ·
                    rfl

theorem cell22_1778674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_1778674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778674 prefixEnd_1778674 := by exact prefixLift 1778674
  have htrace : WordTrace (prefixWord ++ tailWord_1778674) baseStart_1778674 baseEnd_1778674 := by
    simpa [prefixWord, tailWord_1778674, baseEnd_1778674] using wordTrace_append hprefix tailTrace_1778674
  have hstable : (prefixWord ++ tailWord_1778674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778674).length < 2 ^ (prefixWord ++ tailWord_1778674).sum := by decide
  have hdescent : baseEnd_1778674 < baseStart_1778674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778700 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 5, 3]
def baseStart_1778700 : Nat := 118140960795 + 1778700 * 2 ^ 59
def prefixEnd_1778700 : Nat := 4983230072969 + 3 ^ 40 * 1778700 * 2
def baseEnd_1778700 : Nat := 608885360101530707846609

theorem tailTrace_1778700 : CollatzResearch.WordTrace tailWord_1778700 prefixEnd_1778700 608885360101530707846609 := by
  unfold tailWord_1778700
  simp only [CollatzResearch.WordTrace]
  refine ⟨32437259328040576310062777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43249679104054101746750369 32437259328040576310062777)
  ·
    refine ⟨24327944496030432232547083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32437259328040576310062777 24327944496030432232547083)
    ·
      refine ⟨36491916744045648348820625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24327944496030432232547083 36491916744045648348820625)
      ·
        refine ⟨27368937558034236261615469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36491916744045648348820625 27368937558034236261615469)
        ·
          refine ⟨10263351584262838598105801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27368937558034236261615469 10263351584262838598105801)
          ·
            refine ⟨7697513688197128948579351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10263351584262838598105801 7697513688197128948579351)
            ·
              refine ⟨11546270532295693422869027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7697513688197128948579351 11546270532295693422869027)
              ·
                refine ⟨17319405798443540134303541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11546270532295693422869027 17319405798443540134303541)
                ·
                  refine ⟨1623694293604081887590957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17319405798443540134303541 1623694293604081887590957)
                  ·
                    refine ⟨608885360101530707846609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1623694293604081887590957 608885360101530707846609)
                    ·
                      rfl

theorem cell22_1778700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_1778700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778700 prefixEnd_1778700 := by exact prefixLift 1778700
  have htrace : WordTrace (prefixWord ++ tailWord_1778700) baseStart_1778700 baseEnd_1778700 := by
    simpa [prefixWord, tailWord_1778700, baseEnd_1778700] using wordTrace_append hprefix tailTrace_1778700
  have hstable : (prefixWord ++ tailWord_1778700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778700).length < 2 ^ (prefixWord ++ tailWord_1778700).sum := by decide
  have hdescent : baseEnd_1778700 < baseStart_1778700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778734 : List Nat := [4, 1, 3, 1, 1, 1, 1, 6, 1, 3]
def baseStart_1778734 : Nat := 118140960795 + 1778734 * 2 ^ 59
def prefixEnd_1778734 : Nat := 4983230072969 + 3 ^ 40 * 1778734 * 2
def baseEnd_1778734 : Nat := 608896998996365952496505

theorem tailTrace_1778734 : CollatzResearch.WordTrace tailWord_1778734 prefixEnd_1778734 608896998996365952496505 := by
  unfold tailWord_1778734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8109469842244747053357907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43250505825305317617908837 8109469842244747053357907)
  ·
    refine ⟨12164204763367120580036861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8109469842244747053357907 12164204763367120580036861)
    ·
      refine ⟨4561576786262670217513823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12164204763367120580036861 4561576786262670217513823)
      ·
        refine ⟨6842365179394005326270735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4561576786262670217513823 6842365179394005326270735)
        ·
          refine ⟨10263547769091007989406103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6842365179394005326270735 10263547769091007989406103)
          ·
            refine ⟨15395321653636511984109155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10263547769091007989406103 15395321653636511984109155)
            ·
              refine ⟨23092982480454767976163733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15395321653636511984109155 23092982480454767976163733)
              ·
                refine ⟨1082483553771317248882675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23092982480454767976163733 1082483553771317248882675)
                ·
                  refine ⟨1623725330656975873324013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1082483553771317248882675 1623725330656975873324013)
                  ·
                    refine ⟨608896998996365952496505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1623725330656975873324013 608896998996365952496505)
                    ·
                      rfl

theorem cell22_1778734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_1778734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778734 prefixEnd_1778734 := by exact prefixLift 1778734
  have htrace : WordTrace (prefixWord ++ tailWord_1778734) baseStart_1778734 baseEnd_1778734 := by
    simpa [prefixWord, tailWord_1778734, baseEnd_1778734] using wordTrace_append hprefix tailTrace_1778734
  have hstable : (prefixWord ++ tailWord_1778734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778734).length < 2 ^ (prefixWord ++ tailWord_1778734).sum := by decide
  have hdescent : baseEnd_1778734 < baseStart_1778734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778745 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 2, 5]
def baseStart_1778745 : Nat := 118140960795 + 1778745 * 2 ^ 59
def prefixEnd_1778745 : Nat := 4983230072969 + 3 ^ 40 * 1778745 * 2
def baseEnd_1778745 : Nat := 608900764521165590471471

theorem tailTrace_1778745 : CollatzResearch.WordTrace tailWord_1778745 prefixEnd_1778745 608900764521165590471471 := by
  unfold tailWord_1778745
  simp only [CollatzResearch.WordTrace]
  refine ⟨64876159940918125305513689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43250773293945416870342459 64876159940918125305513689)
  ·
    refine ⟨48657119955688593979135267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64876159940918125305513689 48657119955688593979135267)
    ·
      refine ⟨72985679933532890968702901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48657119955688593979135267 72985679933532890968702901)
      ·
        refine ⟨6842407493768708528315897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72985679933532890968702901 6842407493768708528315897)
        ·
          refine ⟨5131805620326531396236923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6842407493768708528315897 5131805620326531396236923)
          ·
            refine ⟨7697708430489797094355385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5131805620326531396236923 7697708430489797094355385)
            ·
              refine ⟨5773281322867347820766539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7697708430489797094355385 5773281322867347820766539)
              ·
                refine ⟨8659921984301021731149809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5773281322867347820766539 8659921984301021731149809)
                ·
                  refine ⟨6494941488225766298362357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8659921984301021731149809 6494941488225766298362357)
                  ·
                    refine ⟨608900764521165590471471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6494941488225766298362357 608900764521165590471471)
                    ·
                      rfl

theorem cell22_1778745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_1778745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778745 prefixEnd_1778745 := by exact prefixLift 1778745
  have htrace : WordTrace (prefixWord ++ tailWord_1778745) baseStart_1778745 baseEnd_1778745 := by
    simpa [prefixWord, tailWord_1778745, baseEnd_1778745] using wordTrace_append hprefix tailTrace_1778745
  have hstable : (prefixWord ++ tailWord_1778745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778745).length < 2 ^ (prefixWord ++ tailWord_1778745).sum := by decide
  have hdescent : baseEnd_1778745 < baseStart_1778745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778807 : List Nat := [1, 1, 3, 1, 1, 4, 3, 3, 2, 3]
def baseStart_1778807 : Nat := 118140960795 + 1778807 * 2 ^ 59
def prefixEnd_1778807 : Nat := 4983230072969 + 3 ^ 40 * 1778807 * 2
def baseEnd_1778807 : Nat := 608921988388218095421281

theorem tailTrace_1778807 : CollatzResearch.WordTrace tailWord_1778807 prefixEnd_1778807 608921988388218095421281 := by
  unfold tailWord_1778807
  simp only [CollatzResearch.WordTrace]
  refine ⟨64878421266693509894270675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43252280844462339929513783 64878421266693509894270675)
  ·
    refine ⟨97317631900040264841406013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64878421266693509894270675 97317631900040264841406013)
    ·
      refine ⟨36494111962515099315527255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97317631900040264841406013 36494111962515099315527255)
      ·
        refine ⟨54741167943772648973290883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36494111962515099315527255 54741167943772648973290883)
        ·
          refine ⟨82111751915658973459936325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54741167943772648973290883 82111751915658973459936325)
          ·
            refine ⟨15395953484186057523738061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82111751915658973459936325 15395953484186057523738061)
            ·
              refine ⟨5773482556569771571401773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15395953484186057523738061 5773482556569771571401773)
              ·
                refine ⟨2165055958713664339275665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5773482556569771571401773 2165055958713664339275665)
                ·
                  refine ⟨1623791969035248254456749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2165055958713664339275665 1623791969035248254456749)
                  ·
                    refine ⟨608921988388218095421281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1623791969035248254456749 608921988388218095421281)
                    ·
                      rfl

theorem cell22_1778807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_1778807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778807 prefixEnd_1778807 := by exact prefixLift 1778807
  have htrace : WordTrace (prefixWord ++ tailWord_1778807) baseStart_1778807 baseEnd_1778807 := by
    simpa [prefixWord, tailWord_1778807, baseEnd_1778807] using wordTrace_append hprefix tailTrace_1778807
  have hstable : (prefixWord ++ tailWord_1778807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778807).length < 2 ^ (prefixWord ++ tailWord_1778807).sum := by decide
  have hdescent : baseEnd_1778807 < baseStart_1778807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778820 : List Nat := [2, 3, 2, 1, 2, 2, 2, 8]
def baseStart_1778820 : Nat := 118140960795 + 1778820 * 2 ^ 59
def prefixEnd_1778820 : Nat := 4983230072969 + 3 ^ 40 * 1778820 * 2
def baseEnd_1778820 : Nat := 67658493172654488316249

theorem tailTrace_1778820 : CollatzResearch.WordTrace tailWord_1778820 prefixEnd_1778820 67658493172654488316249 := by
  unfold tailWord_1778820
  simp only [CollatzResearch.WordTrace]
  refine ⟨32439447707823206557246957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43252596943764275409662609 32439447707823206557246957)
  ·
    refine ⟨12164792890433702458967609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32439447707823206557246957 12164792890433702458967609)
    ·
      refine ⟨9123594667825276844225707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12164792890433702458967609 9123594667825276844225707)
      ·
        refine ⟨13685392001737915266338561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9123594667825276844225707 13685392001737915266338561)
        ·
          refine ⟨10264044001303436449753921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13685392001737915266338561 10264044001303436449753921)
          ·
            refine ⟨7698033000977577337315441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10264044001303436449753921 7698033000977577337315441)
            ·
              refine ⟨5773524750733183002986581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7698033000977577337315441 5773524750733183002986581)
              ·
                refine ⟨67658493172654488316249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5773524750733183002986581 67658493172654488316249)
                ·
                  rfl

theorem cell22_1778820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 8].length) (baseStart_1778820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778820 prefixEnd_1778820 := by exact prefixLift 1778820
  have htrace : WordTrace (prefixWord ++ tailWord_1778820) baseStart_1778820 baseEnd_1778820 := by
    simpa [prefixWord, tailWord_1778820, baseEnd_1778820] using wordTrace_append hprefix tailTrace_1778820
  have hstable : (prefixWord ++ tailWord_1778820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778820).length < 2 ^ (prefixWord ++ tailWord_1778820).sum := by decide
  have hdescent : baseEnd_1778820 < baseStart_1778820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778895 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 5, 4]
def baseStart_1778895 : Nat := 118140960795 + 1778895 * 2 ^ 59
def prefixEnd_1778895 : Nat := 4983230072969 + 3 ^ 40 * 1778895 * 2
def baseEnd_1778895 : Nat := 608952112586615199221011

theorem tailTrace_1778895 : CollatzResearch.WordTrace tailWord_1778895 prefixEnd_1778895 608952112586615199221011 := by
  unfold tailWord_1778895
  simp only [CollatzResearch.WordTrace]
  refine ⟨64881630890374700923474139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43254420593583133948982759 64881630890374700923474139)
  ·
    refine ⟨97322446335562051385211209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64881630890374700923474139 97322446335562051385211209)
    ·
      refine ⟨72991834751671538538908407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97322446335562051385211209 72991834751671538538908407)
      ·
        refine ⟨109487752127507307808362611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72991834751671538538908407 109487752127507307808362611)
        ·
          refine ⟨164231628191260961712543917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109487752127507307808362611 164231628191260961712543917)
          ·
            refine ⟨61586860571722860642203969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164231628191260961712543917 61586860571722860642203969)
            ·
              refine ⟨46190145428792145481652977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61586860571722860642203969 46190145428792145481652977)
              ·
                refine ⟨34642609071594109111239733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46190145428792145481652977 34642609071594109111239733)
                ·
                  refine ⟨3247744600461947729178725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34642609071594109111239733 3247744600461947729178725)
                  ·
                    refine ⟨608952112586615199221011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3247744600461947729178725 608952112586615199221011)
                    ·
                      rfl

theorem cell22_1778895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_1778895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778895 prefixEnd_1778895 := by exact prefixLift 1778895
  have htrace : WordTrace (prefixWord ++ tailWord_1778895) baseStart_1778895 baseEnd_1778895 := by
    simpa [prefixWord, tailWord_1778895, baseEnd_1778895] using wordTrace_append hprefix tailTrace_1778895
  have hstable : (prefixWord ++ tailWord_1778895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778895).length < 2 ^ (prefixWord ++ tailWord_1778895).sum := by decide
  have hdescent : baseEnd_1778895 < baseStart_1778895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778955 : List Nat := [1, 1, 1, 1, 5, 3, 10]
def baseStart_1778955 : Nat := 118140960795 + 1778955 * 2 ^ 59
def prefixEnd_1778955 : Nat := 4983230072969 + 3 ^ 40 * 1778955 * 2
def baseEnd_1778955 : Nat := 22554542659733149730401

theorem tailTrace_1778955 : CollatzResearch.WordTrace tailWord_1778955 prefixEnd_1778955 22554542659733149730401 := by
  unfold tailWord_1778955
  simp only [CollatzResearch.WordTrace]
  refine ⟨64883819270157331170658319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43255879513438220780438879 64883819270157331170658319)
  ·
    refine ⟨97325728905235996755987479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64883819270157331170658319 97325728905235996755987479)
    ·
      refine ⟨145988593357853995133981219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97325728905235996755987479 145988593357853995133981219)
      ·
        refine ⟨218982890036780992700971829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145988593357853995133981219 218982890036780992700971829)
        ·
          refine ⟨20529645940948218065716109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218982890036780992700971829 20529645940948218065716109)
          ·
            refine ⟨7698617227855581774643541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20529645940948218065716109 7698617227855581774643541)
            ·
              refine ⟨22554542659733149730401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7698617227855581774643541 22554542659733149730401)
              ·
                rfl

theorem cell22_1778955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 10].length) (baseStart_1778955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778955 prefixEnd_1778955 := by exact prefixLift 1778955
  have htrace : WordTrace (prefixWord ++ tailWord_1778955) baseStart_1778955 baseEnd_1778955 := by
    simpa [prefixWord, tailWord_1778955, baseEnd_1778955] using wordTrace_append hprefix tailTrace_1778955
  have hstable : (prefixWord ++ tailWord_1778955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778955).length < 2 ^ (prefixWord ++ tailWord_1778955).sum := by decide
  have hdescent : baseEnd_1778955 < baseStart_1778955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778976 : List Nat := [2, 1, 1, 5, 3, 1, 1, 3, 2, 3]
def baseStart_1778976 : Nat := 118140960795 + 1778976 * 2 ^ 59
def prefixEnd_1778976 : Nat := 4983230072969 + 3 ^ 40 * 1778976 * 2
def baseEnd_1778976 : Nat := 608979840541957987945763

theorem tailTrace_1778976 : CollatzResearch.WordTrace tailWord_1778976 prefixEnd_1778976 608979840541957987945763 := by
  unfold tailWord_1778976
  simp only [CollatzResearch.WordTrace]
  refine ⟨32442292601540625878586391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43256390135387501171448521 32442292601540625878586391)
  ·
    refine ⟨48663438902310938817879587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32442292601540625878586391 48663438902310938817879587)
    ·
      refine ⟨72995158353466408226819381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48663438902310938817879587 72995158353466408226819381)
      ·
        refine ⟨6843296095637475771264317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72995158353466408226819381 6843296095637475771264317)
        ·
          refine ⟨2566236035864053414224119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6843296095637475771264317 2566236035864053414224119)
          ·
            refine ⟨3849354053796080121336179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566236035864053414224119 3849354053796080121336179)
            ·
              refine ⟨5774031080694120182004269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3849354053796080121336179 5774031080694120182004269)
              ·
                refine ⟨2165261655260295068251601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5774031080694120182004269 2165261655260295068251601)
                ·
                  refine ⟨1623946241445221301188701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2165261655260295068251601 1623946241445221301188701)
                  ·
                    refine ⟨608979840541957987945763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1623946241445221301188701 608979840541957987945763)
                    ·
                      rfl

theorem cell22_1778976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 2, 3].length) (baseStart_1778976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778976 prefixEnd_1778976 := by exact prefixLift 1778976
  have htrace : WordTrace (prefixWord ++ tailWord_1778976) baseStart_1778976 baseEnd_1778976 := by
    simpa [prefixWord, tailWord_1778976, baseEnd_1778976] using wordTrace_append hprefix tailTrace_1778976
  have hstable : (prefixWord ++ tailWord_1778976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778976).length < 2 ^ (prefixWord ++ tailWord_1778976).sum := by decide
  have hdescent : baseEnd_1778976 < baseStart_1778976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778989 : List Nat := [1, 5, 3, 1, 1, 1, 2, 8]
def baseStart_1778989 : Nat := 118140960795 + 1778989 * 2 ^ 59
def prefixEnd_1778989 : Nat := 4983230072969 + 3 ^ 40 * 1778989 * 2
def baseEnd_1778989 : Nat := 67664921189736698596747

theorem tailTrace_1778989 : CollatzResearch.WordTrace tailWord_1778989 prefixEnd_1778989 67664921189736698596747 := by
  unfold tailWord_1778989
  simp only [CollatzResearch.WordTrace]
  refine ⟨64885059352034154977396021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43256706234689436651597347 64885059352034154977396021)
  ·
    refine ⟨6082974314253202029130877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64885059352034154977396021 6082974314253202029130877)
    ·
      refine ⟨2281115367844950760924079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6082974314253202029130877 2281115367844950760924079)
      ·
        refine ⟨3421673051767426141386119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2281115367844950760924079 3421673051767426141386119)
        ·
          refine ⟨5132509577651139212079179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3421673051767426141386119 5132509577651139212079179)
          ·
            refine ⟨7698764366476708818118769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5132509577651139212079179 7698764366476708818118769)
            ·
              refine ⟨5774073274857531613589077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7698764366476708818118769 5774073274857531613589077)
              ·
                refine ⟨67664921189736698596747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5774073274857531613589077 67664921189736698596747)
                ·
                  rfl

theorem cell22_1778989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 8].length) (baseStart_1778989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1778989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1778989 prefixEnd_1778989 := by exact prefixLift 1778989
  have htrace : WordTrace (prefixWord ++ tailWord_1778989) baseStart_1778989 baseEnd_1778989 := by
    simpa [prefixWord, tailWord_1778989, baseEnd_1778989] using wordTrace_append hprefix tailTrace_1778989
  have hstable : (prefixWord ++ tailWord_1778989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778989).length < 2 ^ (prefixWord ++ tailWord_1778989).sum := by decide
  have hdescent : baseEnd_1778989 < baseStart_1778989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779017 : List Nat := [1, 2, 1, 1, 2, 3, 3, 4, 5]
def baseStart_1779017 : Nat := 118140960795 + 1779017 * 2 ^ 59
def prefixEnd_1779017 : Nat := 4983230072969 + 3 ^ 40 * 1779017 * 2
def baseEnd_1779017 : Nat := 202997958559949182556879

theorem tailTrace_1779017 : CollatzResearch.WordTrace tailWord_1779017 prefixEnd_1779017 202997958559949182556879 := by
  unfold tailWord_1779017
  simp only [CollatzResearch.WordTrace]
  refine ⟨64886080595932715759415305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43257387063955143839610203 64886080595932715759415305)
  ·
    refine ⟨48664560446949536819561479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64886080595932715759415305 48664560446949536819561479)
    ·
      refine ⟨72996840670424305229342219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48664560446949536819561479 72996840670424305229342219)
      ·
        refine ⟨109495261005636457844013329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72996840670424305229342219 109495261005636457844013329)
        ·
          refine ⟨82121445754227343383009997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109495261005636457844013329 82121445754227343383009997)
          ·
            refine ⟨30795542157835253768628749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82121445754227343383009997 30795542157835253768628749)
            ·
              refine ⟨11548328309188220163235781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30795542157835253768628749 11548328309188220163235781)
              ·
                refine ⟨2165311557972791280606709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11548328309188220163235781 2165311557972791280606709)
                ·
                  refine ⟨202997958559949182556879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2165311557972791280606709 202997958559949182556879)
                  ·
                    rfl

theorem cell22_1779017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 5].length) (baseStart_1779017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779017 prefixEnd_1779017 := by exact prefixLift 1779017
  have htrace : WordTrace (prefixWord ++ tailWord_1779017) baseStart_1779017 baseEnd_1779017 := by
    simpa [prefixWord, tailWord_1779017, baseEnd_1779017] using wordTrace_append hprefix tailTrace_1779017
  have hstable : (prefixWord ++ tailWord_1779017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779017).length < 2 ^ (prefixWord ++ tailWord_1779017).sum := by decide
  have hdescent : baseEnd_1779017 < baseStart_1779017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779032 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 2, 5]
def baseStart_1779032 : Nat := 118140960795 + 1779032 * 2 ^ 59
def prefixEnd_1779032 : Nat := 4983230072969 + 3 ^ 40 * 1779032 * 2
def baseEnd_1779032 : Nat := 608999010486392508545591

theorem tailTrace_1779032 : CollatzResearch.WordTrace tailWord_1779032 prefixEnd_1779032 608999010486392508545591 := by
  unfold tailWord_1779032
  simp only [CollatzResearch.WordTrace]
  refine ⟨32443313845439186660605675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43257751793918915547474233 32443313845439186660605675)
  ·
    refine ⟨48664970768158779990908513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32443313845439186660605675 48664970768158779990908513)
    ·
      refine ⟨36498728076119084993181385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48664970768158779990908513 36498728076119084993181385)
      ·
        refine ⟨27374046057089313744886039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36498728076119084993181385 27374046057089313744886039)
        ·
          refine ⟨41061069085633970617329059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27374046057089313744886039 41061069085633970617329059)
          ·
            refine ⟨61591603628450955925993589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41061069085633970617329059 61591603628450955925993589)
            ·
              refine ⟨5774212840167277118061899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61591603628450955925993589 5774212840167277118061899)
              ·
                refine ⟨8661319260250915677092849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5774212840167277118061899 8661319260250915677092849)
                ·
                  refine ⟨6495989445188186757819637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8661319260250915677092849 6495989445188186757819637)
                  ·
                    refine ⟨608999010486392508545591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6495989445188186757819637 608999010486392508545591)
                    ·
                      rfl

theorem cell22_1779032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_1779032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779032 prefixEnd_1779032 := by exact prefixLift 1779032
  have htrace : WordTrace (prefixWord ++ tailWord_1779032) baseStart_1779032 baseEnd_1779032 := by
    simpa [prefixWord, tailWord_1779032, baseEnd_1779032] using wordTrace_append hprefix tailTrace_1779032
  have hstable : (prefixWord ++ tailWord_1779032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779032).length < 2 ^ (prefixWord ++ tailWord_1779032).sum := by decide
  have hdescent : baseEnd_1779032 < baseStart_1779032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779077 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 3, 5]
def baseStart_1779077 : Nat := 118140960795 + 1779077 * 2 ^ 59
def prefixEnd_1779077 : Nat := 4983230072969 + 3 ^ 40 * 1779077 * 2
def baseEnd_1779077 : Nat := 609014414906027391170453

theorem tailTrace_1779077 : CollatzResearch.WordTrace tailWord_1779077 prefixEnd_1779077 609014414906027391170453 := by
  unfold tailWord_1779077
  simp only [CollatzResearch.WordTrace]
  refine ⟨64888268975715346006599485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43258845983810230671066323 64888268975715346006599485)
  ·
    refine ⟨24333100865893254752474807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64888268975715346006599485 24333100865893254752474807)
    ·
      refine ⟨36499651298839882128712211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24333100865893254752474807 36499651298839882128712211)
      ·
        refine ⟨54749476948259823193068317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36499651298839882128712211 54749476948259823193068317)
        ·
          refine ⟨20531053855597433697400619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54749476948259823193068317 20531053855597433697400619)
          ·
            refine ⟨30796580783396150546100929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20531053855597433697400619 30796580783396150546100929)
            ·
              refine ⟨23097435587547112909575697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30796580783396150546100929 23097435587547112909575697)
              ·
                refine ⟨17323076690660334682181773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23097435587547112909575697 17323076690660334682181773)
                ·
                  refine ⟨6496153758997625505818165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17323076690660334682181773 6496153758997625505818165)
                  ·
                    refine ⟨609014414906027391170453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6496153758997625505818165 609014414906027391170453)
                    ·
                      rfl

theorem cell22_1779077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_1779077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779077 prefixEnd_1779077 := by exact prefixLift 1779077
  have htrace : WordTrace (prefixWord ++ tailWord_1779077) baseStart_1779077 baseEnd_1779077 := by
    simpa [prefixWord, tailWord_1779077, baseEnd_1779077] using wordTrace_append hprefix tailTrace_1779077
  have hstable : (prefixWord ++ tailWord_1779077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779077).length < 2 ^ (prefixWord ++ tailWord_1779077).sum := by decide
  have hdescent : baseEnd_1779077 < baseStart_1779077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779079 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 6]
def baseStart_1779079 : Nat := 118140960795 + 1779079 * 2 ^ 59
def prefixEnd_1779079 : Nat := 4983230072969 + 3 ^ 40 * 1779079 * 2
def baseEnd_1779079 : Nat := 203005033182300017540149

theorem tailTrace_1779079 : CollatzResearch.WordTrace tailWord_1779079 prefixEnd_1779079 203005033182300017540149 := by
  unfold tailWord_1779079
  simp only [CollatzResearch.WordTrace]
  refine ⟨64888341921708100348172291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43258894614472066898781527 64888341921708100348172291)
  ·
    refine ⟨97332512882562150522258437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64888341921708100348172291 97332512882562150522258437)
    ·
      refine ⟨18249846165480403222923457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97332512882562150522258437 18249846165480403222923457)
      ·
        refine ⟨13687384624110302417192593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18249846165480403222923457 13687384624110302417192593)
        ·
          refine ⟨10265538468082726812894445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13687384624110302417192593 10265538468082726812894445)
          ·
            refine ⟨3849576925531022554835417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10265538468082726812894445 3849576925531022554835417)
            ·
              refine ⟨2887182694148266916126563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3849576925531022554835417 2887182694148266916126563)
              ·
                refine ⟨4330774041222400374189845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2887182694148266916126563 4330774041222400374189845)
                ·
                  refine ⟨203005033182300017540149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4330774041222400374189845 203005033182300017540149)
                  ·
                    rfl

theorem cell22_1779079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 6].length) (baseStart_1779079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779079 prefixEnd_1779079 := by exact prefixLift 1779079
  have htrace : WordTrace (prefixWord ++ tailWord_1779079) baseStart_1779079 baseEnd_1779079 := by
    simpa [prefixWord, tailWord_1779079, baseEnd_1779079] using wordTrace_append hprefix tailTrace_1779079
  have hstable : (prefixWord ++ tailWord_1779079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779079).length < 2 ^ (prefixWord ++ tailWord_1779079).sum := by decide
  have hdescent : baseEnd_1779079 < baseStart_1779079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779107 : List Nat := [1, 1, 1, 4, 1, 3, 3, 8]
def baseStart_1779107 : Nat := 118140960795 + 1779107 * 2 ^ 59
def prefixEnd_1779107 : Nat := 4983230072969 + 3 ^ 40 * 1779107 * 2
def baseEnd_1779107 : Nat := 67669409391013034768929

theorem tailTrace_1779107 : CollatzResearch.WordTrace tailWord_1779107 prefixEnd_1779107 67669409391013034768929 := by
  unfold tailWord_1779107
  simp only [CollatzResearch.WordTrace]
  refine ⟨64889363165606661130191575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43259575443737774086794383 64889363165606661130191575)
  ·
    refine ⟨97334044748409991695287363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64889363165606661130191575 97334044748409991695287363)
    ·
      refine ⟨146001067122614987542931045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97334044748409991695287363 146001067122614987542931045)
      ·
        refine ⟨27375200085490310164299571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146001067122614987542931045 27375200085490310164299571)
        ·
          refine ⟨41062800128235465246449357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27375200085490310164299571 41062800128235465246449357)
          ·
            refine ⟨15398550048088299467418509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41062800128235465246449357 15398550048088299467418509)
            ·
              refine ⟨5774456268033112300281941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15398550048088299467418509 5774456268033112300281941)
              ·
                refine ⟨67669409391013034768929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5774456268033112300281941 67669409391013034768929)
                ·
                  rfl

theorem cell22_1779107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 8].length) (baseStart_1779107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779107 prefixEnd_1779107 := by exact prefixLift 1779107
  have htrace : WordTrace (prefixWord ++ tailWord_1779107) baseStart_1779107 baseEnd_1779107 := by
    simpa [prefixWord, tailWord_1779107, baseEnd_1779107] using wordTrace_append hprefix tailTrace_1779107
  have hstable : (prefixWord ++ tailWord_1779107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779107).length < 2 ^ (prefixWord ++ tailWord_1779107).sum := by decide
  have hdescent : baseEnd_1779107 < baseStart_1779107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779186 : List Nat := [3, 2, 1, 4, 1, 1, 1, 4, 5]
def baseStart_1779186 : Nat := 118140960795 + 1779186 * 2 ^ 59
def prefixEnd_1779186 : Nat := 4983230072969 + 3 ^ 40 * 1779186 * 2
def baseEnd_1779186 : Nat := 203017242611195813398373

theorem tailTrace_1779186 : CollatzResearch.WordTrace tailWord_1779186 prefixEnd_1779186 203017242611195813398373 := by
  unfold tailWord_1779186
  simp only [CollatzResearch.WordTrace]
  refine ⟨16223061133080114405579353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43261496354880305081544941 16223061133080114405579353)
  ·
    refine ⟨12167295849810085804184515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16223061133080114405579353 12167295849810085804184515)
    ·
      refine ⟨18250943774715128706276773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12167295849810085804184515 18250943774715128706276773)
      ·
        refine ⟨3422051957759086632426895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18250943774715128706276773 3422051957759086632426895)
        ·
          refine ⟨5133077936638629948640343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3422051957759086632426895 5133077936638629948640343)
          ·
            refine ⟨7699616904957944922960515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5133077936638629948640343 7699616904957944922960515)
            ·
              refine ⟨11549425357436917384440773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7699616904957944922960515 11549425357436917384440773)
              ·
                refine ⟨2165517254519422009582645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11549425357436917384440773 2165517254519422009582645)
                ·
                  refine ⟨203017242611195813398373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2165517254519422009582645 203017242611195813398373)
                  ·
                    rfl

theorem cell22_1779186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_1779186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779186 prefixEnd_1779186 := by exact prefixLift 1779186
  have htrace : WordTrace (prefixWord ++ tailWord_1779186) baseStart_1779186 baseEnd_1779186 := by
    simpa [prefixWord, tailWord_1779186, baseEnd_1779186] using wordTrace_append hprefix tailTrace_1779186
  have hstable : (prefixWord ++ tailWord_1779186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779186).length < 2 ^ (prefixWord ++ tailWord_1779186).sum := by decide
  have hdescent : baseEnd_1779186 < baseStart_1779186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779190 : List Nat := [5, 1, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_1779190 : Nat := 118140960795 + 1779190 * 2 ^ 59
def prefixEnd_1779190 : Nat := 4983230072969 + 3 ^ 40 * 1779190 * 2
def baseEnd_1779190 : Nat := 609053097115332763095107

theorem tailTrace_1779190 : CollatzResearch.WordTrace tailWord_1779190 prefixEnd_1779190 609053097115332763095107 := by
  unfold tailWord_1779190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4055774401519122894091439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43261593616203977536975349 4055774401519122894091439)
  ·
    refine ⟨6083661602278684341137159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4055774401519122894091439 6083661602278684341137159)
    ·
      refine ⟨9125492403418026511705739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6083661602278684341137159 9125492403418026511705739)
      ·
        refine ⟨13688238605127039767558609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9125492403418026511705739 13688238605127039767558609)
        ·
          refine ⟨10266178953845279825668957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13688238605127039767558609 10266178953845279825668957)
          ·
            refine ⟨3849817107691979934625859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10266178953845279825668957 3849817107691979934625859)
            ·
              refine ⟨5774725661537969901938789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3849817107691979934625859 5774725661537969901938789)
              ·
                refine ⟨1082761061538369356613523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5774725661537969901938789 1082761061538369356613523)
                ·
                  refine ⟨1624141592307554034920285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1082761061538369356613523 1624141592307554034920285)
                  ·
                    refine ⟨609053097115332763095107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1624141592307554034920285 609053097115332763095107)
                    ·
                      rfl

theorem cell22_1779190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_1779190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779190 prefixEnd_1779190 := by exact prefixLift 1779190
  have htrace : WordTrace (prefixWord ++ tailWord_1779190) baseStart_1779190 baseEnd_1779190 := by
    simpa [prefixWord, tailWord_1779190, baseEnd_1779190] using wordTrace_append hprefix tailTrace_1779190
  have hstable : (prefixWord ++ tailWord_1779190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779190).length < 2 ^ (prefixWord ++ tailWord_1779190).sum := by decide
  have hdescent : baseEnd_1779190 < baseStart_1779190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779201 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 2, 5]
def baseStart_1779201 : Nat := 118140960795 + 1779201 * 2 ^ 59
def prefixEnd_1779201 : Nat := 4983230072969 + 3 ^ 40 * 1779201 * 2
def baseEnd_1779201 : Nat := 609056862640132401070073

theorem tailTrace_1779201 : CollatzResearch.WordTrace tailWord_1779201 prefixEnd_1779201 609056862640132401070073 := by
  unfold tailWord_1779201
  simp only [CollatzResearch.WordTrace]
  refine ⟨64892791627266115184113457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43261861084844076789408971 64892791627266115184113457)
  ·
    refine ⟨48669593720449586388085093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64892791627266115184113457 48669593720449586388085093)
    ·
      refine ⟨9125548822584297447765955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48669593720449586388085093 9125548822584297447765955)
      ·
        refine ⟨13688323233876446171648933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9125548822584297447765955 13688323233876446171648933)
        ·
          refine ⟨2566560606351833657184175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13688323233876446171648933 2566560606351833657184175)
          ·
            refine ⟨3849840909527750485776263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566560606351833657184175 3849840909527750485776263)
            ·
              refine ⟨5774761364291625728664395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3849840909527750485776263 5774761364291625728664395)
              ·
                refine ⟨8662142046437438592996593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5774761364291625728664395 8662142046437438592996593)
                ·
                  refine ⟨6496606534828078944747445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8662142046437438592996593 6496606534828078944747445)
                  ·
                    refine ⟨609056862640132401070073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6496606534828078944747445 609056862640132401070073)
                    ·
                      rfl

theorem cell22_1779201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_1779201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779201 prefixEnd_1779201 := by exact prefixLift 1779201
  have htrace : WordTrace (prefixWord ++ tailWord_1779201) baseStart_1779201 baseEnd_1779201 := by
    simpa [prefixWord, tailWord_1779201, baseEnd_1779201] using wordTrace_append hprefix tailTrace_1779201
  have hstable : (prefixWord ++ tailWord_1779201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779201).length < 2 ^ (prefixWord ++ tailWord_1779201).sum := by decide
  have hdescent : baseEnd_1779201 < baseStart_1779201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779231 : List Nat := [1, 1, 2, 4, 1, 1, 3, 5, 4]
def baseStart_1779231 : Nat := 118140960795 + 1779231 * 2 ^ 59
def prefixEnd_1779231 : Nat := 4983230072969 + 3 ^ 40 * 1779231 * 2
def baseEnd_1779231 : Nat := 203022377417740774273327

theorem tailTrace_1779231 : CollatzResearch.WordTrace tailWord_1779231 prefixEnd_1779231 203022377417740774273327 := by
  unfold tailWord_1779231
  simp only [CollatzResearch.WordTrace]
  refine ⟨64893885817157430307705547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43262590544771620205137031 64893885817157430307705547)
  ·
    refine ⟨97340828725736145461558321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64893885817157430307705547 97340828725736145461558321)
    ·
      refine ⟨73005621544302109096168741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97340828725736145461558321 73005621544302109096168741)
      ·
        refine ⟨13688554039556645455531639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73005621544302109096168741 13688554039556645455531639)
        ·
          refine ⟨20532831059334968183297459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13688554039556645455531639 20532831059334968183297459)
          ·
            refine ⟨30799246589002452274946189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20532831059334968183297459 30799246589002452274946189)
            ·
              refine ⟨11549717470875919603104821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30799246589002452274946189 11549717470875919603104821)
              ·
                refine ⟨1082786012894617462791077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11549717470875919603104821 1082786012894617462791077)
                ·
                  refine ⟨203022377417740774273327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1082786012894617462791077 203022377417740774273327)
                  ·
                    rfl

theorem cell22_1779231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 4].length) (baseStart_1779231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779231 prefixEnd_1779231 := by exact prefixLift 1779231
  have htrace : WordTrace (prefixWord ++ tailWord_1779231) baseStart_1779231 baseEnd_1779231 := by
    simpa [prefixWord, tailWord_1779231, baseEnd_1779231] using wordTrace_append hprefix tailTrace_1779231
  have hstable : (prefixWord ++ tailWord_1779231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779231).length < 2 ^ (prefixWord ++ tailWord_1779231).sum := by decide
  have hdescent : baseEnd_1779231 < baseStart_1779231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779233 : List Nat := [1, 2, 3, 2, 2, 2, 4, 1, 1, 4]
def baseStart_1779233 : Nat := 118140960795 + 1779233 * 2 ^ 59
def prefixEnd_1779233 : Nat := 4983230072969 + 3 ^ 40 * 1779233 * 2
def baseEnd_1779233 : Nat := 609067816894094984269975

theorem tailTrace_1779233 : CollatzResearch.WordTrace tailWord_1779233 prefixEnd_1779233 609067816894094984269975 := by
  unfold tailWord_1779233
  simp only [CollatzResearch.WordTrace]
  refine ⟨64893958763150184649278353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43262639175433456432852235 64893958763150184649278353)
  ·
    refine ⟨48670469072362638486958765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64893958763150184649278353 48670469072362638486958765)
    ·
      refine ⟨18251425902135989432609537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48670469072362638486958765 18251425902135989432609537)
      ·
        refine ⟨13688569426601992074457153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18251425902135989432609537 13688569426601992074457153)
        ·
          refine ⟨10266427069951494055842865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13688569426601992074457153 10266427069951494055842865)
          ·
            refine ⟨7699820302463620541882149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10266427069951494055842865 7699820302463620541882149)
            ·
              refine ⟨1443716306711928851602903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7699820302463620541882149 1443716306711928851602903)
              ·
                refine ⟨2165574460067893277404355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443716306711928851602903 2165574460067893277404355)
                ·
                  refine ⟨3248361690101839916106533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2165574460067893277404355 3248361690101839916106533)
                  ·
                    refine ⟨609067816894094984269975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3248361690101839916106533 609067816894094984269975)
                    ·
                      rfl

theorem cell22_1779233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_1779233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779233 prefixEnd_1779233 := by exact prefixLift 1779233
  have htrace : WordTrace (prefixWord ++ tailWord_1779233) baseStart_1779233 baseEnd_1779233 := by
    simpa [prefixWord, tailWord_1779233, baseEnd_1779233] using wordTrace_append hprefix tailTrace_1779233
  have hstable : (prefixWord ++ tailWord_1779233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779233).length < 2 ^ (prefixWord ++ tailWord_1779233).sum := by decide
  have hdescent : baseEnd_1779233 < baseStart_1779233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779274 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 2, 7]
def baseStart_1779274 : Nat := 118140960795 + 1779274 * 2 ^ 59
def prefixEnd_1779274 : Nat := 4983230072969 + 3 ^ 40 * 1779274 * 2
def baseEnd_1779274 : Nat := 609081852031984543994849

theorem tailTrace_1779274 : CollatzResearch.WordTrace tailWord_1779274 prefixEnd_1779274 609081852031984543994849 := by
  unfold tailWord_1779274
  simp only [CollatzResearch.WordTrace]
  refine ⟨16223863539000412162880219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43263636104001099101013917 16223863539000412162880219)
  ·
    refine ⟨24335795308500618244320329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16223863539000412162880219 24335795308500618244320329)
    ·
      refine ⟨18251846481375463683240247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24335795308500618244320329 18251846481375463683240247)
      ·
        refine ⟨27377769722063195524860371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18251846481375463683240247 27377769722063195524860371)
        ·
          refine ⟨41066654583094793287290557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27377769722063195524860371 41066654583094793287290557)
          ·
            refine ⟨15399995468660547482733959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41066654583094793287290557 15399995468660547482733959)
            ·
              refine ⟨23099993202990821224100939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15399995468660547482733959 23099993202990821224100939)
              ·
                refine ⟨34649989804486231836151409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23099993202990821224100939 34649989804486231836151409)
                ·
                  refine ⟨25987492353364673877113557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34649989804486231836151409 25987492353364673877113557)
                  ·
                    refine ⟨609081852031984543994849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25987492353364673877113557 609081852031984543994849)
                    ·
                      rfl

theorem cell22_1779274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_1779274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779274 prefixEnd_1779274 := by exact prefixLift 1779274
  have htrace : WordTrace (prefixWord ++ tailWord_1779274) baseStart_1779274 baseEnd_1779274 := by
    simpa [prefixWord, tailWord_1779274, baseEnd_1779274] using wordTrace_append hprefix tailTrace_1779274
  have hstable : (prefixWord ++ tailWord_1779274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779274).length < 2 ^ (prefixWord ++ tailWord_1779274).sum := by decide
  have hdescent : baseEnd_1779274 < baseStart_1779274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779276 : List Nat := [2, 2, 1, 3, 1, 3, 4, 6]
def baseStart_1779276 : Nat := 118140960795 + 1779276 * 2 ^ 59
def prefixEnd_1779276 : Nat := 4983230072969 + 3 ^ 40 * 1779276 * 2
def baseEnd_1779276 : Nat := 67675837408095245049427

theorem tailTrace_1779276 : CollatzResearch.WordTrace tailWord_1779276 prefixEnd_1779276 67675837408095245049427 := by
  unfold tailWord_1779276
  simp only [CollatzResearch.WordTrace]
  refine ⟨32447763550997201496546841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43263684734662935328729121 32447763550997201496546841)
  ·
    refine ⟨24335822663247901122410131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32447763550997201496546841 24335822663247901122410131)
    ·
      refine ⟨36503733994871851683615197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24335822663247901122410131 36503733994871851683615197)
      ·
        refine ⟨13688900248076944381355699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36503733994871851683615197 13688900248076944381355699)
        ·
          refine ⟨20533350372115416572033549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13688900248076944381355699 20533350372115416572033549)
          ·
            refine ⟨7700006389543281214512581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20533350372115416572033549 7700006389543281214512581)
            ·
              refine ⟨1443751198039365227721109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7700006389543281214512581 1443751198039365227721109)
              ·
                refine ⟨67675837408095245049427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1443751198039365227721109 67675837408095245049427)
                ·
                  rfl

theorem cell22_1779276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 6].length) (baseStart_1779276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779276 prefixEnd_1779276 := by exact prefixLift 1779276
  have htrace : WordTrace (prefixWord ++ tailWord_1779276) baseStart_1779276 baseEnd_1779276 := by
    simpa [prefixWord, tailWord_1779276, baseEnd_1779276] using wordTrace_append hprefix tailTrace_1779276
  have hstable : (prefixWord ++ tailWord_1779276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779276).length < 2 ^ (prefixWord ++ tailWord_1779276).sum := by decide
  have hdescent : baseEnd_1779276 < baseStart_1779276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779319 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 1, 7]
def baseStart_1779319 : Nat := 118140960795 + 1779319 * 2 ^ 59
def prefixEnd_1779319 : Nat := 4983230072969 + 3 ^ 40 * 1779319 * 2
def baseEnd_1779319 : Nat := 609097256451619426619711

theorem tailTrace_1779319 : CollatzResearch.WordTrace tailWord_1779319 prefixEnd_1779319 609097256451619426619711 := by
  unfold tailWord_1779319
  simp only [CollatzResearch.WordTrace]
  refine ⟨64897095440838621336909011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43264730293892414224606007 64897095440838621336909011)
  ·
    refine ⟨97345643161257932005363517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64897095440838621336909011 97345643161257932005363517)
    ·
      refine ⟨36504616185471724502011319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97345643161257932005363517 36504616185471724502011319)
      ·
        refine ⟨54756924278207586753016979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36504616185471724502011319 54756924278207586753016979)
        ·
          refine ⟨82135386417311380129525469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54756924278207586753016979 82135386417311380129525469)
          ·
            refine ⟨30800769906491767548572051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82135386417311380129525469 30800769906491767548572051)
            ·
              refine ⟨46201154859737651322858077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30800769906491767548572051 46201154859737651322858077)
              ·
                refine ⟨17325433072401619246071779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46201154859737651322858077 17325433072401619246071779)
                ·
                  refine ⟨25988149608602428869107669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17325433072401619246071779 25988149608602428869107669)
                  ·
                    refine ⟨609097256451619426619711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25988149608602428869107669 609097256451619426619711)
                    ·
                      rfl

theorem cell22_1779319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_1779319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779319 prefixEnd_1779319 := by exact prefixLift 1779319
  have htrace : WordTrace (prefixWord ++ tailWord_1779319) baseStart_1779319 baseEnd_1779319 := by
    simpa [prefixWord, tailWord_1779319, baseEnd_1779319] using wordTrace_append hprefix tailTrace_1779319
  have hstable : (prefixWord ++ tailWord_1779319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779319).length < 2 ^ (prefixWord ++ tailWord_1779319).sum := by decide
  have hdescent : baseEnd_1779319 < baseStart_1779319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779321 : List Nat := [1, 2, 1, 3, 3, 1, 3, 3, 5]
def baseStart_1779321 : Nat := 118140960795 + 1779321 * 2 ^ 59
def prefixEnd_1779321 : Nat := 4983230072969 + 3 ^ 40 * 1779321 * 2
def baseEnd_1779321 : Nat := 203032647030830696023235

theorem tailTrace_1779321 : CollatzResearch.WordTrace tailWord_1779321 prefixEnd_1779321 203032647030830696023235 := by
  unfold tailWord_1779321
  simp only [CollatzResearch.WordTrace]
  refine ⟨64897168386831375678481817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43264778924554250452321211 64897168386831375678481817)
  ·
    refine ⟨48672876290123531758861363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64897168386831375678481817 48672876290123531758861363)
    ·
      refine ⟨73009314435185297638292045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48672876290123531758861363 73009314435185297638292045)
      ·
        refine ⟨27378492913194486614359517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73009314435185297638292045 27378492913194486614359517)
        ·
          refine ⟨10266934842447932480384819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27378492913194486614359517 10266934842447932480384819)
          ·
            refine ⟨15400402263671898720577229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10266934842447932480384819 15400402263671898720577229)
            ·
              refine ⟨5775150848876962020216461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15400402263671898720577229 5775150848876962020216461)
              ·
                refine ⟨2165681568328860757581173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5775150848876962020216461 2165681568328860757581173)
                ·
                  refine ⟨203032647030830696023235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2165681568328860757581173 203032647030830696023235)
                  ·
                    rfl

theorem cell22_1779321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 5].length) (baseStart_1779321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779321 prefixEnd_1779321 := by exact prefixLift 1779321
  have htrace : WordTrace (prefixWord ++ tailWord_1779321) baseStart_1779321 baseEnd_1779321 := by
    simpa [prefixWord, tailWord_1779321, baseEnd_1779321] using wordTrace_append hprefix tailTrace_1779321
  have hstable : (prefixWord ++ tailWord_1779321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779321).length < 2 ^ (prefixWord ++ tailWord_1779321).sum := by decide
  have hdescent : baseEnd_1779321 < baseStart_1779321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779402 : List Nat := [3, 1, 2, 1, 5, 2, 2, 1, 1, 4]
def baseStart_1779402 : Nat := 118140960795 + 1779402 * 2 ^ 59
def prefixEnd_1779402 : Nat := 4983230072969 + 3 ^ 40 * 1779402 * 2
def baseEnd_1779402 : Nat := 609125669047834876794457

theorem tailTrace_1779402 : CollatzResearch.WordTrace tailWord_1779402 prefixEnd_1779402 609125669047834876794457 := by
  unfold tailWord_1779402
  simp only [CollatzResearch.WordTrace]
  refine ⟨16225030674884481628045115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43266748466358617674786973 16225030674884481628045115)
  ·
    refine ⟨24337546012326722442067673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16225030674884481628045115 24337546012326722442067673)
    ·
      refine ⟨18253159509245041831550755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24337546012326722442067673 18253159509245041831550755)
      ·
        refine ⟨27379739263867562747326133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18253159509245041831550755 27379739263867562747326133)
        ·
          refine ⟨2566850555987584007561825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27379739263867562747326133 2566850555987584007561825)
          ·
            refine ⟨1925137916990688005671369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2566850555987584007561825 1925137916990688005671369)
            ·
              refine ⟨1443853437743016004253527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1925137916990688005671369 1443853437743016004253527)
              ·
                refine ⟨2165780156614524006380291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443853437743016004253527 2165780156614524006380291)
                ·
                  refine ⟨3248670234921786009570437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2165780156614524006380291 3248670234921786009570437)
                  ·
                    refine ⟨609125669047834876794457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3248670234921786009570437 609125669047834876794457)
                    ·
                      rfl

theorem cell22_1779402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_1779402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779402 prefixEnd_1779402 := by exact prefixLift 1779402
  have htrace : WordTrace (prefixWord ++ tailWord_1779402) baseStart_1779402 baseEnd_1779402 := by
    simpa [prefixWord, tailWord_1779402, baseEnd_1779402] using wordTrace_append hprefix tailTrace_1779402
  have hstable : (prefixWord ++ tailWord_1779402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779402).length < 2 ^ (prefixWord ++ tailWord_1779402).sum := by decide
  have hdescent : baseEnd_1779402 < baseStart_1779402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779432 : List Nat := [2, 1, 4, 1, 3, 2, 3, 1, 2, 3]
def baseStart_1779432 : Nat := 118140960795 + 1779432 * 2 ^ 59
def prefixEnd_1779432 : Nat := 4983230072969 + 3 ^ 40 * 1779432 * 2
def baseEnd_1779432 : Nat := 609135938660924798544365

theorem tailTrace_1779432 : CollatzResearch.WordTrace tailWord_1779432 prefixEnd_1779432 609135938660924798544365 := by
  unfold tailWord_1779432
  simp only [CollatzResearch.WordTrace]
  refine ⟨32450608444714620817886275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43267477926286161090515033 32450608444714620817886275)
  ·
    refine ⟨48675912667071931226829413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32450608444714620817886275 48675912667071931226829413)
    ·
      refine ⟨9126733625075987105030515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48675912667071931226829413 9126733625075987105030515)
      ·
        refine ⟨13690100437613980657545773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9126733625075987105030515 13690100437613980657545773)
        ·
          refine ⟨5133787664105242746579665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13690100437613980657545773 5133787664105242746579665)
          ·
            refine ⟨3850340748078932059934749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5133787664105242746579665 3850340748078932059934749)
            ·
              refine ⟨1443877780529599522475531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3850340748078932059934749 1443877780529599522475531)
              ·
                refine ⟨2165816670794399283713297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443877780529599522475531 2165816670794399283713297)
                ·
                  refine ⟨1624362503095799462784973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2165816670794399283713297 1624362503095799462784973)
                  ·
                    refine ⟨609135938660924798544365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1624362503095799462784973 609135938660924798544365)
                    ·
                      rfl

theorem cell22_1779432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_1779432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779432 prefixEnd_1779432 := by exact prefixLift 1779432
  have htrace : WordTrace (prefixWord ++ tailWord_1779432) baseStart_1779432 baseEnd_1779432 := by
    simpa [prefixWord, tailWord_1779432, baseEnd_1779432] using wordTrace_append hprefix tailTrace_1779432
  have hstable : (prefixWord ++ tailWord_1779432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779432).length < 2 ^ (prefixWord ++ tailWord_1779432).sum := by decide
  have hdescent : baseEnd_1779432 < baseStart_1779432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779443 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 3, 3]
def baseStart_1779443 : Nat := 118140960795 + 1779443 * 2 ^ 59
def prefixEnd_1779443 : Nat := 4983230072969 + 3 ^ 40 * 1779443 * 2
def baseEnd_1779443 : Nat := 609139704185724436519331

theorem tailTrace_1779443 : CollatzResearch.WordTrace tailWord_1779443 prefixEnd_1779443 609139704185724436519331 := by
  unfold tailWord_1779443
  simp only [CollatzResearch.WordTrace]
  refine ⟨64901618092389390514422983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43267745394926260342948655 64901618092389390514422983)
  ·
    refine ⟨97352427138584085771634475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64901618092389390514422983 97352427138584085771634475)
    ·
      refine ⟨146028640707876128657451713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97352427138584085771634475 146028640707876128657451713)
      ·
        refine ⟨109521480530907096493088785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146028640707876128657451713 109521480530907096493088785)
        ·
          refine ⟨82141110398180322369816589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109521480530907096493088785 82141110398180322369816589)
          ·
            refine ⟨30802916399317620888681221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82141110398180322369816589 30802916399317620888681221)
            ·
              refine ⟨5775546824872053916627729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30802916399317620888681221 5775546824872053916627729)
              ·
                refine ⟨4331660118654040437470797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5775546824872053916627729 4331660118654040437470797)
                ·
                  refine ⟨1624372544495265164051549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4331660118654040437470797 1624372544495265164051549)
                  ·
                    refine ⟨609139704185724436519331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1624372544495265164051549 609139704185724436519331)
                    ·
                      rfl

theorem cell22_1779443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 3].length) (baseStart_1779443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779443 prefixEnd_1779443 := by exact prefixLift 1779443
  have htrace : WordTrace (prefixWord ++ tailWord_1779443) baseStart_1779443 baseEnd_1779443 := by
    simpa [prefixWord, tailWord_1779443, baseEnd_1779443] using wordTrace_append hprefix tailTrace_1779443
  have hstable : (prefixWord ++ tailWord_1779443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779443).length < 2 ^ (prefixWord ++ tailWord_1779443).sum := by decide
  have hdescent : baseEnd_1779443 < baseStart_1779443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779471 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 2, 5]
def baseStart_1779471 : Nat := 118140960795 + 1779471 * 2 ^ 59
def prefixEnd_1779471 : Nat := 4983230072969 + 3 ^ 40 * 1779471 * 2
def baseEnd_1779471 : Nat := 609149289157941696819245

theorem tailTrace_1779471 : CollatzResearch.WordTrace tailWord_1779471 prefixEnd_1779471 609149289157941696819245 := by
  unfold tailWord_1779471
  simp only [CollatzResearch.WordTrace]
  refine ⟨64902639336287951296442267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43268426224191967530961511 64902639336287951296442267)
  ·
    refine ⟨97353959004431926944663401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64902639336287951296442267 97353959004431926944663401)
    ·
      refine ⟨73015469253323945208497551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97353959004431926944663401 73015469253323945208497551)
      ·
        refine ⟨109523203879985917812746327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73015469253323945208497551 109523203879985917812746327)
        ·
          refine ⟨164284805819978876719119491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109523203879985917812746327 164284805819978876719119491)
          ·
            refine ⟨246427208729968315078679237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164284805819978876719119491 246427208729968315078679237)
            ·
              refine ⟨46205101636869059077252357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246427208729968315078679237 46205101636869059077252357)
              ·
                refine ⟨8663456556912948576984817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46205101636869059077252357 8663456556912948576984817)
                ·
                  refine ⟨6497592417684711432738613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8663456556912948576984817 6497592417684711432738613)
                  ·
                    refine ⟨609149289157941696819245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6497592417684711432738613 609149289157941696819245)
                    ·
                      rfl

theorem cell22_1779471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_1779471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779471 prefixEnd_1779471 := by exact prefixLift 1779471
  have htrace : WordTrace (prefixWord ++ tailWord_1779471) baseStart_1779471 baseEnd_1779471 := by
    simpa [prefixWord, tailWord_1779471, baseEnd_1779471] using wordTrace_append hprefix tailTrace_1779471
  have hstable : (prefixWord ++ tailWord_1779471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779471).length < 2 ^ (prefixWord ++ tailWord_1779471).sum := by decide
  have hdescent : baseEnd_1779471 < baseStart_1779471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779565 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_1779565 : Nat := 118140960795 + 1779565 * 2 ^ 59
def prefixEnd_1779565 : Nat := 4983230072969 + 3 ^ 40 * 1779565 * 2
def baseEnd_1779565 : Nat := 609181467278956784968957

theorem tailTrace_1779565 : CollatzResearch.WordTrace tailWord_1779565 prefixEnd_1779565 609181467278956784968957 := by
  unfold tailWord_1779565
  simp only [CollatzResearch.WordTrace]
  refine ⟨64906067797947405350364149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43270711865298270233576099 64906067797947405350364149)
  ·
    refine ⟨6084943856057569251596639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64906067797947405350364149 6084943856057569251596639)
    ·
      refine ⟨9127415784086353877394959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6084943856057569251596639 9127415784086353877394959)
      ·
        refine ⟨13691123676129530816092439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9127415784086353877394959 13691123676129530816092439)
        ·
          refine ⟨20536685514194296224138659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13691123676129530816092439 20536685514194296224138659)
          ·
            refine ⟨30805028271291444336207989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20536685514194296224138659 30805028271291444336207989)
            ·
              refine ⟨2887971400433572906519499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30805028271291444336207989 2887971400433572906519499)
              ·
                refine ⟨4331957100650359359779249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2887971400433572906519499 4331957100650359359779249)
                ·
                  refine ⟨3248967825487769519834437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4331957100650359359779249 3248967825487769519834437)
                  ·
                    refine ⟨609181467278956784968957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3248967825487769519834437 609181467278956784968957)
                    ·
                      rfl

theorem cell22_1779565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_1779565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779565 prefixEnd_1779565 := by exact prefixLift 1779565
  have htrace : WordTrace (prefixWord ++ tailWord_1779565) baseStart_1779565 baseEnd_1779565 := by
    simpa [prefixWord, tailWord_1779565, baseEnd_1779565] using wordTrace_append hprefix tailTrace_1779565
  have hstable : (prefixWord ++ tailWord_1779565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779565).length < 2 ^ (prefixWord ++ tailWord_1779565).sum := by decide
  have hdescent : baseEnd_1779565 < baseStart_1779565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779612 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 3, 3]
def baseStart_1779612 : Nat := 118140960795 + 1779612 * 2 ^ 59
def prefixEnd_1779612 : Nat := 4983230072969 + 3 ^ 40 * 1779612 * 2
def baseEnd_1779612 : Nat := 609197556339464329043813

theorem tailTrace_1779612 : CollatzResearch.WordTrace tailWord_1779612 prefixEnd_1779612 609197556339464329043813 := by
  unfold tailWord_1779612
  simp only [CollatzResearch.WordTrace]
  refine ⟨32453891014388566188662545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43271854685851421584883393 32453891014388566188662545)
  ·
    refine ⟨24340418260791424641496909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32453891014388566188662545 24340418260791424641496909)
    ·
      refine ⟨9127656847796784240561341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24340418260791424641496909 9127656847796784240561341)
      ·
        refine ⟨3422871317923794090210503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9127656847796784240561341 3422871317923794090210503)
        ·
          refine ⟨5134306976885691135315755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3422871317923794090210503 5134306976885691135315755)
          ·
            refine ⟨7701460465328536702973633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5134306976885691135315755 7701460465328536702973633)
            ·
              refine ⟨5776095348996402527230225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7701460465328536702973633 5776095348996402527230225)
              ·
                refine ⟨4332071511747301895422669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5776095348996402527230225 4332071511747301895422669)
                ·
                  refine ⟨1624526816905238210783501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4332071511747301895422669 1624526816905238210783501)
                  ·
                    refine ⟨609197556339464329043813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1624526816905238210783501 609197556339464329043813)
                    ·
                      rfl

theorem cell22_1779612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_1779612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779612 prefixEnd_1779612 := by exact prefixLift 1779612
  have htrace : WordTrace (prefixWord ++ tailWord_1779612) baseStart_1779612 baseEnd_1779612 := by
    simpa [prefixWord, tailWord_1779612, baseEnd_1779612] using wordTrace_append hprefix tailTrace_1779612
  have hstable : (prefixWord ++ tailWord_1779612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779612).length < 2 ^ (prefixWord ++ tailWord_1779612).sum := by decide
  have hdescent : baseEnd_1779612 < baseStart_1779612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779646 : List Nat := [4, 2, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_1779646 : Nat := 118140960795 + 1779646 * 2 ^ 59
def prefixEnd_1779646 : Nat := 4983230072969 + 3 ^ 40 * 1779646 * 2
def baseEnd_1779646 : Nat := 609209195234299573693709

theorem tailTrace_1779646 : CollatzResearch.WordTrace tailWord_1779646 prefixEnd_1779646 609209195234299573693709 := by
  unfold tailWord_1779646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8113627763831744523007849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43272681407102637456041861 8113627763831744523007849)
  ·
    refine ⟨6085220822873808392255887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8113627763831744523007849 6085220822873808392255887)
    ·
      refine ⟨9127831234310712588383831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6085220822873808392255887 9127831234310712588383831)
      ·
        refine ⟨13691746851466068882575747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9127831234310712588383831 13691746851466068882575747)
        ·
          refine ⟨20537620277199103323863621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13691746851466068882575747 20537620277199103323863621)
          ·
            refine ⟨3850803801974831873224429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20537620277199103323863621 3850803801974831873224429)
            ·
              refine ⟨1444051425740561952459161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3850803801974831873224429 1444051425740561952459161)
              ·
                refine ⟨1083038569305421464344371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1444051425740561952459161 1083038569305421464344371)
                ·
                  refine ⟨1624557853958132196516557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1083038569305421464344371 1624557853958132196516557)
                  ·
                    refine ⟨609209195234299573693709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1624557853958132196516557 609209195234299573693709)
                    ·
                      rfl

theorem cell22_1779646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_1779646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779646 prefixEnd_1779646 := by exact prefixLift 1779646
  have htrace : WordTrace (prefixWord ++ tailWord_1779646) baseStart_1779646 baseEnd_1779646 := by
    simpa [prefixWord, tailWord_1779646, baseEnd_1779646] using wordTrace_append hprefix tailTrace_1779646
  have hstable : (prefixWord ++ tailWord_1779646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779646).length < 2 ^ (prefixWord ++ tailWord_1779646).sum := by decide
  have hdescent : baseEnd_1779646 < baseStart_1779646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779653 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 6]
def baseStart_1779653 : Nat := 118140960795 + 1779653 * 2 ^ 59
def prefixEnd_1779653 : Nat := 4983230072969 + 3 ^ 40 * 1779653 * 2
def baseEnd_1779653 : Nat := 203070530492451296256229

theorem tailTrace_1779653 : CollatzResearch.WordTrace tailWord_1779653 prefixEnd_1779653 203070530492451296256229 := by
  unfold tailWord_1779653
  simp only [CollatzResearch.WordTrace]
  refine ⟨64909277421628596379567613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43272851614419064253045075 64909277421628596379567613)
  ·
    refine ⟨24340979033110723642337855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64909277421628596379567613 24340979033110723642337855)
    ·
      refine ⟨36511468549666085463506783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24340979033110723642337855 36511468549666085463506783)
      ·
        refine ⟨54767202824499128195260175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36511468549666085463506783 54767202824499128195260175)
        ·
          refine ⟨82150804236748692292890263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54767202824499128195260175 82150804236748692292890263)
          ·
            refine ⟨123226206355123038439335395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82150804236748692292890263 123226206355123038439335395)
            ·
              refine ⟨184839309532684557659003093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123226206355123038439335395 184839309532684557659003093)
              ·
                refine ⟨4332171317172294320132885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 184839309532684557659003093 4332171317172294320132885)
                ·
                  refine ⟨203070530492451296256229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4332171317172294320132885 203070530492451296256229)
                  ·
                    rfl

theorem cell22_1779653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_1779653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779653 prefixEnd_1779653 := by exact prefixLift 1779653
  have htrace : WordTrace (prefixWord ++ tailWord_1779653) baseStart_1779653 baseEnd_1779653 := by
    simpa [prefixWord, tailWord_1779653, baseEnd_1779653] using wordTrace_append hprefix tailTrace_1779653
  have hstable : (prefixWord ++ tailWord_1779653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779653).length < 2 ^ (prefixWord ++ tailWord_1779653).sum := by decide
  have hdescent : baseEnd_1779653 < baseStart_1779653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779698 : List Nat := [3, 2, 1, 16]
def baseStart_1779698 : Nat := 118140960795 + 1779698 * 2 ^ 59
def prefixEnd_1779698 : Nat := 4983230072969 + 3 ^ 40 * 1779698 * 2
def baseEnd_1779698 : Nat := 835702326333317930581

theorem tailTrace_1779698 : CollatzResearch.WordTrace tailWord_1779698 prefixEnd_1779698 835702326333317930581 := by
  unfold tailWord_1779698
  simp only [CollatzResearch.WordTrace]
  refine ⟨16227729676616392266238937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43273945804310379376637165 16227729676616392266238937)
  ·
    refine ⟨12170797257462294199679203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16227729676616392266238937 12170797257462294199679203)
    ·
      refine ⟨18256195886193441299518805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12170797257462294199679203 18256195886193441299518805)
      ·
        refine ⟨835702326333317930581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 18256195886193441299518805 835702326333317930581)
        ·
          rfl

theorem cell22_1779698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 16].length) (baseStart_1779698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779698 prefixEnd_1779698 := by exact prefixLift 1779698
  have htrace : WordTrace (prefixWord ++ tailWord_1779698) baseStart_1779698 baseEnd_1779698 := by
    simpa [prefixWord, tailWord_1779698, baseEnd_1779698] using wordTrace_append hprefix tailTrace_1779698
  have hstable : (prefixWord ++ tailWord_1779698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779698).length < 2 ^ (prefixWord ++ tailWord_1779698).sum := by decide
  have hdescent : baseEnd_1779698 < baseStart_1779698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779760 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 7]
def baseStart_1779760 : Nat := 118140960795 + 1779760 * 2 ^ 59
def prefixEnd_1779760 : Nat := 4983230072969 + 3 ^ 40 * 1779760 * 2
def baseEnd_1779760 : Nat := 203082739921347092114453

theorem tailTrace_1779760 : CollatzResearch.WordTrace tailWord_1779760 prefixEnd_1779760 203082739921347092114453 := by
  unfold tailWord_1779760
  simp only [CollatzResearch.WordTrace]
  refine ⟨32456590016120476826856367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43275453354827302435808489 32456590016120476826856367)
  ·
    refine ⟨48684885024180715240284551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32456590016120476826856367 48684885024180715240284551)
    ·
      refine ⟨73027327536271072860426827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48684885024180715240284551 73027327536271072860426827)
      ·
        refine ⟨109540991304406609290640241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73027327536271072860426827 109540991304406609290640241)
        ·
          refine ⟨82155743478304956967980181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109540991304406609290640241 82155743478304956967980181)
          ·
            refine ⟨3851050475545544857874071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82155743478304956967980181 3851050475545544857874071)
            ·
              refine ⟨5776575713318317286811107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851050475545544857874071 5776575713318317286811107)
              ·
                refine ⟨8664863569977475930216661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5776575713318317286811107 8664863569977475930216661)
                ·
                  refine ⟨203082739921347092114453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8664863569977475930216661 203082739921347092114453)
                  ·
                    rfl

theorem cell22_1779760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 7].length) (baseStart_1779760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779760 prefixEnd_1779760 := by exact prefixLift 1779760
  have htrace : WordTrace (prefixWord ++ tailWord_1779760) baseStart_1779760 baseEnd_1779760 := by
    simpa [prefixWord, tailWord_1779760, baseEnd_1779760] using wordTrace_append hprefix tailTrace_1779760
  have hstable : (prefixWord ++ tailWord_1779760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779760).length < 2 ^ (prefixWord ++ tailWord_1779760).sum := by decide
  have hdescent : baseEnd_1779760 < baseStart_1779760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779775 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 2, 5]
def baseStart_1779775 : Nat := 118140960795 + 1779775 * 2 ^ 59
def prefixEnd_1779775 : Nat := 4983230072969 + 3 ^ 40 * 1779775 * 2
def baseEnd_1779775 : Nat := 609253354570586237218313

theorem tailTrace_1779775 : CollatzResearch.WordTrace tailWord_1779775 prefixEnd_1779775 609253354570586237218313 := by
  unfold tailWord_1779775
  simp only [CollatzResearch.WordTrace]
  refine ⟨64913727127186611215508779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43275818084791074143672519 64913727127186611215508779)
  ·
    refine ⟨97370590690779916823263169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64913727127186611215508779 97370590690779916823263169)
    ·
      refine ⟨73027943018084937617447377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97370590690779916823263169 73027943018084937617447377)
      ·
        refine ⟨54770957263563703213085533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73027943018084937617447377 54770957263563703213085533)
        ·
          refine ⟨20539108973836388704907075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54770957263563703213085533 20539108973836388704907075)
          ·
            refine ⟨30808663460754583057360613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20539108973836388704907075 30808663460754583057360613)
            ·
              refine ⟨5776624398891484323255115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30808663460754583057360613 5776624398891484323255115)
              ·
                refine ⟨8664936598337226484882673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5776624398891484323255115 8664936598337226484882673)
                ·
                  refine ⟨6498702448752919863662005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8664936598337226484882673 6498702448752919863662005)
                  ·
                    refine ⟨609253354570586237218313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6498702448752919863662005 609253354570586237218313)
                    ·
                      rfl

theorem cell22_1779775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_1779775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779775 prefixEnd_1779775 := by exact prefixLift 1779775
  have htrace : WordTrace (prefixWord ++ tailWord_1779775) baseStart_1779775 baseEnd_1779775 := by
    simpa [prefixWord, tailWord_1779775, baseEnd_1779775] using wordTrace_append hprefix tailTrace_1779775
  have hstable : (prefixWord ++ tailWord_1779775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779775).length < 2 ^ (prefixWord ++ tailWord_1779775).sum := by decide
  have hdescent : baseEnd_1779775 < baseStart_1779775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779841 : List Nat := [1, 2, 4, 2, 3, 2, 1, 2, 1, 4]
def baseStart_1779841 : Nat := 118140960795 + 1779841 * 2 ^ 59
def prefixEnd_1779841 : Nat := 4983230072969 + 3 ^ 40 * 1779841 * 2
def baseEnd_1779841 : Nat := 609275947719384065068111

theorem tailTrace_1779841 : CollatzResearch.WordTrace tailWord_1779841 prefixEnd_1779841 609275947719384065068111 := by
  unfold tailWord_1779841
  simp only [CollatzResearch.WordTrace]
  refine ⟨64916134344947504487411377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43277422896631669658274251 64916134344947504487411377)
  ·
    refine ⟨48687100758710628365558533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64916134344947504487411377 48687100758710628365558533)
    ·
      refine ⟨9128831392258242818542225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48687100758710628365558533 9128831392258242818542225)
      ·
        refine ⟨6846623544193682113906669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9128831392258242818542225 6846623544193682113906669)
        ·
          refine ⟨2567483829072630792715001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6846623544193682113906669 2567483829072630792715001)
          ·
            refine ⟨1925612871804473094536251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2567483829072630792715001 1925612871804473094536251)
            ·
              refine ⟨2888419307706709641804377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925612871804473094536251 2888419307706709641804377)
              ·
                refine ⟨2166314480780032231353283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2888419307706709641804377 2166314480780032231353283)
                ·
                  refine ⟨3249471721170048347029925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2166314480780032231353283 3249471721170048347029925)
                  ·
                    refine ⟨609275947719384065068111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3249471721170048347029925 609275947719384065068111)
                    ·
                      rfl

theorem cell22_1779841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_1779841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779841 prefixEnd_1779841 := by exact prefixLift 1779841
  have htrace : WordTrace (prefixWord ++ tailWord_1779841) baseStart_1779841 baseEnd_1779841 := by
    simpa [prefixWord, tailWord_1779841, baseEnd_1779841] using wordTrace_append hprefix tailTrace_1779841
  have hstable : (prefixWord ++ tailWord_1779841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779841).length < 2 ^ (prefixWord ++ tailWord_1779841).sum := by decide
  have hdescent : baseEnd_1779841 < baseStart_1779841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779854 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_1779854 : Nat := 118140960795 + 1779854 * 2 ^ 59
def prefixEnd_1779854 : Nat := 4983230072969 + 3 ^ 40 * 1779854 * 2
def baseEnd_1779854 : Nat := 609280397885056364493071

theorem tailTrace_1779854 : CollatzResearch.WordTrace tailWord_1779854 prefixEnd_1779854 609280397885056364493071 := by
  unfold tailWord_1779854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8114576061737550963454327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43277738995933605138423077 8114576061737550963454327)
  ·
    refine ⟨12171864092606326445181491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8114576061737550963454327 12171864092606326445181491)
    ·
      refine ⟨18257796138909489667772237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12171864092606326445181491 18257796138909489667772237)
      ·
        refine ⟨6846673552091058625414589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18257796138909489667772237 6846673552091058625414589)
        ·
          refine ⟨2567502582034146984530471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6846673552091058625414589 2567502582034146984530471)
          ·
            refine ⟨3851253873051220476795707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567502582034146984530471 3851253873051220476795707)
            ·
              refine ⟨5776880809576830715193561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851253873051220476795707 5776880809576830715193561)
              ·
                refine ⟨4332660607182623036395171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5776880809576830715193561 4332660607182623036395171)
                ·
                  refine ⟨6498990910773934554592757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4332660607182623036395171 6498990910773934554592757)
                  ·
                    refine ⟨609280397885056364493071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6498990910773934554592757 609280397885056364493071)
                    ·
                      rfl

theorem cell22_1779854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_1779854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779854 prefixEnd_1779854 := by exact prefixLift 1779854
  have htrace : WordTrace (prefixWord ++ tailWord_1779854) baseStart_1779854 baseEnd_1779854 := by
    simpa [prefixWord, tailWord_1779854, baseEnd_1779854] using wordTrace_append hprefix tailTrace_1779854
  have hstable : (prefixWord ++ tailWord_1779854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779854).length < 2 ^ (prefixWord ++ tailWord_1779854).sum := by decide
  have hdescent : baseEnd_1779854 < baseStart_1779854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779871 : List Nat := [1, 1, 2, 6, 1, 2, 2, 2, 2, 3]
def baseStart_1779871 : Nat := 118140960795 + 1779871 * 2 ^ 59
def prefixEnd_1779871 : Nat := 4983230072969 + 3 ^ 40 * 1779871 * 2
def baseEnd_1779871 : Nat := 609286217332473986818019

theorem tailTrace_1779871 : CollatzResearch.WordTrace tailWord_1779871 prefixEnd_1779871 609286217332473986818019 := by
  unfold tailWord_1779871
  simp only [CollatzResearch.WordTrace]
  refine ⟨64917228534838819611003467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43278152356559213074002311 64917228534838819611003467)
  ·
    refine ⟨97375842802258229416505201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64917228534838819611003467 97375842802258229416505201)
    ·
      refine ⟨73031882101693672062378901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97375842802258229416505201 73031882101693672062378901)
      ·
        refine ⟨3423369473516890877924011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73031882101693672062378901 3423369473516890877924011)
        ·
          refine ⟨5135054210275336316886017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3423369473516890877924011 5135054210275336316886017)
          ·
            refine ⟨3851290657706502237664513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5135054210275336316886017 3851290657706502237664513)
            ·
              refine ⟨2888467993279876678248385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3851290657706502237664513 2888467993279876678248385)
              ·
                refine ⟨2166350994959907508686289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2888467993279876678248385 2166350994959907508686289)
                ·
                  refine ⟨1624763246219930631514717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2166350994959907508686289 1624763246219930631514717)
                  ·
                    refine ⟨609286217332473986818019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1624763246219930631514717 609286217332473986818019)
                    ·
                      rfl

theorem cell22_1779871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 3].length) (baseStart_1779871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779871 prefixEnd_1779871 := by exact prefixLift 1779871
  have htrace : WordTrace (prefixWord ++ tailWord_1779871) baseStart_1779871 baseEnd_1779871 := by
    simpa [prefixWord, tailWord_1779871, baseEnd_1779871] using wordTrace_append hprefix tailTrace_1779871
  have hstable : (prefixWord ++ tailWord_1779871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779871).length < 2 ^ (prefixWord ++ tailWord_1779871).sum := by decide
  have hdescent : baseEnd_1779871 < baseStart_1779871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779933 : List Nat := [1, 4, 3, 2, 1, 1, 2, 4, 1, 3]
def baseStart_1779933 : Nat := 118140960795 + 1779933 * 2 ^ 59
def prefixEnd_1779933 : Nat := 4983230072969 + 3 ^ 40 * 1779933 * 2
def baseEnd_1779933 : Nat := 609307441199526491767829

theorem tailTrace_1779933 : CollatzResearch.WordTrace tailWord_1779933 prefixEnd_1779933 609307441199526491767829 := by
  unfold tailWord_1779933
  simp only [CollatzResearch.WordTrace]
  refine ⟨64919489860614204199760453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43279659907076136133173635 64919489860614204199760453)
  ·
    refine ⟨12172404348865163287455085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64919489860614204199760453 12172404348865163287455085)
    ·
      refine ⟨4564651630824436232795657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12172404348865163287455085 4564651630824436232795657)
      ·
        refine ⟨3423488723118327174596743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4564651630824436232795657 3423488723118327174596743)
        ·
          refine ⟨5135233084677490761895115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3423488723118327174596743 5135233084677490761895115)
          ·
            refine ⟨7702849627016236142842673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5135233084677490761895115 7702849627016236142842673)
            ·
              refine ⟨5777137220262177107132005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7702849627016236142842673 5777137220262177107132005)
              ·
                refine ⟨1083213228799158207587251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5777137220262177107132005 1083213228799158207587251)
                ·
                  refine ⟨1624819843198737311380877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1083213228799158207587251 1624819843198737311380877)
                  ·
                    refine ⟨609307441199526491767829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1624819843198737311380877 609307441199526491767829)
                    ·
                      rfl

theorem cell22_1779933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_1779933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779933 prefixEnd_1779933 := by exact prefixLift 1779933
  have htrace : WordTrace (prefixWord ++ tailWord_1779933) baseStart_1779933 baseEnd_1779933 := by
    simpa [prefixWord, tailWord_1779933, baseEnd_1779933] using wordTrace_append hprefix tailTrace_1779933
  have hstable : (prefixWord ++ tailWord_1779933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779933).length < 2 ^ (prefixWord ++ tailWord_1779933).sum := by decide
  have hdescent : baseEnd_1779933 < baseStart_1779933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779989 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 4, 3]
def baseStart_1779989 : Nat := 118140960795 + 1779989 * 2 ^ 59
def prefixEnd_1779989 : Nat := 4983230072969 + 3 ^ 40 * 1779989 * 2
def baseEnd_1779989 : Nat := 609326611143961012367657

theorem tailTrace_1779989 : CollatzResearch.WordTrace tailWord_1779989 prefixEnd_1779989 609326611143961012367657 := by
  unfold tailWord_1779989
  simp only [CollatzResearch.WordTrace]
  refine ⟨64921532348411325763799021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43281021565607550509199347 64921532348411325763799021)
  ·
    refine ⟨24345574630654247161424633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64921532348411325763799021 24345574630654247161424633)
    ·
      refine ⟨18259180972990685371068475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24345574630654247161424633 18259180972990685371068475)
      ·
        refine ⟨27388771459486028056602713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18259180972990685371068475 27388771459486028056602713)
        ·
          refine ⟨20541578594614521042452035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27388771459486028056602713 20541578594614521042452035)
          ·
            refine ⟨30812367891921781563678053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20541578594614521042452035 30812367891921781563678053)
            ·
              refine ⟨5777318979735334043189635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30812367891921781563678053 5777318979735334043189635)
              ·
                refine ⟨8665978469603001064784453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5777318979735334043189635 8665978469603001064784453)
                ·
                  refine ⟨1624870963050562699647085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8665978469603001064784453 1624870963050562699647085)
                  ·
                    refine ⟨609326611143961012367657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1624870963050562699647085 609326611143961012367657)
                    ·
                      rfl

theorem cell22_1779989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_1779989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1779989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1779989 prefixEnd_1779989 := by exact prefixLift 1779989
  have htrace : WordTrace (prefixWord ++ tailWord_1779989) baseStart_1779989 baseEnd_1779989 := by
    simpa [prefixWord, tailWord_1779989, baseEnd_1779989] using wordTrace_append hprefix tailTrace_1779989
  have hstable : (prefixWord ++ tailWord_1779989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779989).length < 2 ^ (prefixWord ++ tailWord_1779989).sum := by decide
  have hdescent : baseEnd_1779989 < baseStart_1779989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780010 : List Nat := [3, 1, 4, 2, 3, 1, 1, 2, 1, 4]
def baseStart_1780010 : Nat := 118140960795 + 1780010 * 2 ^ 59
def prefixEnd_1780010 : Nat := 4983230072969 + 3 ^ 40 * 1780010 * 2
def baseEnd_1780010 : Nat := 609333799873123957592593

theorem tailTrace_1780010 : CollatzResearch.WordTrace tailWord_1780010 prefixEnd_1780010 609333799873123957592593 := by
  unfold tailWord_1780010
  simp only [CollatzResearch.WordTrace]
  refine ⟨16230574570333811587578371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43281532187556830900208989 16230574570333811587578371)
  ·
    refine ⟨24345861855500717381367557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16230574570333811587578371 24345861855500717381367557)
    ·
      refine ⟨4564849097906384509006417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24345861855500717381367557 4564849097906384509006417)
      ·
        refine ⟨3423636823429788381754813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4564849097906384509006417 3423636823429788381754813)
        ·
          refine ⟨1283863808786170643158055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3423636823429788381754813 1283863808786170643158055)
          ·
            refine ⟨1925795713179255964737083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283863808786170643158055 1925795713179255964737083)
            ·
              refine ⟨2888693569768883947105625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925795713179255964737083 2888693569768883947105625)
              ·
                refine ⟨2166520177326662960329219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2888693569768883947105625 2166520177326662960329219)
                ·
                  refine ⟨3249780265989994440493829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2166520177326662960329219 3249780265989994440493829)
                  ·
                    refine ⟨609333799873123957592593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3249780265989994440493829 609333799873123957592593)
                    ·
                      rfl

theorem cell22_1780010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_1780010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780010 prefixEnd_1780010 := by exact prefixLift 1780010
  have htrace : WordTrace (prefixWord ++ tailWord_1780010) baseStart_1780010 baseEnd_1780010 := by
    simpa [prefixWord, tailWord_1780010, baseEnd_1780010] using wordTrace_append hprefix tailTrace_1780010
  have hstable : (prefixWord ++ tailWord_1780010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780010).length < 2 ^ (prefixWord ++ tailWord_1780010).sum := by decide
  have hdescent : baseEnd_1780010 < baseStart_1780010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780036 : List Nat := [2, 3, 4, 1, 3, 9]
def baseStart_1780036 : Nat := 118140960795 + 1780036 * 2 ^ 59
def prefixEnd_1780036 : Nat := 4983230072969 + 3 ^ 40 * 1780036 * 2
def baseEnd_1780036 : Nat := 7522749385240352548673

theorem tailTrace_1780036 : CollatzResearch.WordTrace tailWord_1780036 prefixEnd_1780036 7522749385240352548673 := by
  unfold tailWord_1780036
  simp only [CollatzResearch.WordTrace]
  refine ⟨32461623289620526395379981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43282164386160701860506641 32461623289620526395379981)
  ·
    refine ⟨12173108733607697398267493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32461623289620526395379981 12173108733607697398267493)
    ·
      refine ⟨2282457887551443262175155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12173108733607697398267493 2282457887551443262175155)
      ·
        refine ⟨3423686831327164893262733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2282457887551443262175155 3423686831327164893262733)
        ·
          refine ⟨1283882561747686834973525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3423686831327164893262733 1283882561747686834973525)
          ·
            refine ⟨7522749385240352548673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1283882561747686834973525 7522749385240352548673)
            ·
              rfl

theorem cell22_1780036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 9].length) (baseStart_1780036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780036 prefixEnd_1780036 := by exact prefixLift 1780036
  have htrace : WordTrace (prefixWord ++ tailWord_1780036) baseStart_1780036 baseEnd_1780036 := by
    simpa [prefixWord, tailWord_1780036, baseEnd_1780036] using wordTrace_append hprefix tailTrace_1780036
  have hstable : (prefixWord ++ tailWord_1780036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780036).length < 2 ^ (prefixWord ++ tailWord_1780036).sum := by decide
  have hdescent : baseEnd_1780036 < baseStart_1780036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780085 : List Nat := [1, 3, 4, 1, 2, 2, 2, 3, 1, 3]
def baseStart_1780085 : Nat := 118140960795 + 1780085 * 2 ^ 59
def prefixEnd_1780085 : Nat := 4983230072969 + 3 ^ 40 * 1780085 * 2
def baseEnd_1780085 : Nat := 609359473905848761967363

theorem tailTrace_1780085 : CollatzResearch.WordTrace tailWord_1780085 prefixEnd_1780085 609359473905848761967363 := by
  unfold tailWord_1780085
  simp only [CollatzResearch.WordTrace]
  refine ⟨64925033756063534159293709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43283355837375689439529139 64925033756063534159293709)
  ·
    refine ⟨24346887658523825309735141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64925033756063534159293709 24346887658523825309735141)
    ·
      refine ⟨4565041435973217245575339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24346887658523825309735141 4565041435973217245575339)
      ·
        refine ⟨6847562153959825868363009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4565041435973217245575339 6847562153959825868363009)
        ·
          refine ⟨5135671615469869401272257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6847562153959825868363009 5135671615469869401272257)
          ·
            refine ⟨3851753711602402050954193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5135671615469869401272257 3851753711602402050954193)
            ·
              refine ⟨2888815283701801538215645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3851753711602402050954193 2888815283701801538215645)
              ·
                refine ⟨1083305731388175576830867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2888815283701801538215645 1083305731388175576830867)
                ·
                  refine ⟨1624958597082263365246301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1083305731388175576830867 1624958597082263365246301)
                  ·
                    refine ⟨609359473905848761967363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1624958597082263365246301 609359473905848761967363)
                    ·
                      rfl

theorem cell22_1780085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_1780085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780085 prefixEnd_1780085 := by exact prefixLift 1780085
  have htrace : WordTrace (prefixWord ++ tailWord_1780085) baseStart_1780085 baseEnd_1780085 := by
    simpa [prefixWord, tailWord_1780085, baseEnd_1780085] using wordTrace_append hprefix tailTrace_1780085
  have hstable : (prefixWord ++ tailWord_1780085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780085).length < 2 ^ (prefixWord ++ tailWord_1780085).sum := by decide
  have hdescent : baseEnd_1780085 < baseStart_1780085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780098 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1780098 : Nat := 118140960795 + 1780098 * 2 ^ 59
def prefixEnd_1780098 : Nat := 4983230072969 + 3 ^ 40 * 1780098 * 2
def baseEnd_1780098 : Nat := 203121308023840353797441

theorem tailTrace_1780098 : CollatzResearch.WordTrace tailWord_1780098 prefixEnd_1780098 203121308023840353797441 := by
  unfold tailWord_1780098
  simp only [CollatzResearch.WordTrace]
  refine ⟨16231376976254109344879237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43283671936677624919677965 16231376976254109344879237)
  ·
    refine ⟨3043383183047645502164857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16231376976254109344879237 3043383183047645502164857)
    ·
      refine ⟨2282537387285734126623643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3043383183047645502164857 2282537387285734126623643)
      ·
        refine ⟨3423806080928601189935465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2282537387285734126623643 3423806080928601189935465)
        ·
          refine ⟨2567854560696450892451599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3423806080928601189935465 2567854560696450892451599)
          ·
            refine ⟨3851781841044676338677399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567854560696450892451599 3851781841044676338677399)
            ·
              refine ⟨5777672761567014508016099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851781841044676338677399 5777672761567014508016099)
              ·
                refine ⟨8666509142350521762024149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5777672761567014508016099 8666509142350521762024149)
                ·
                  refine ⟨203121308023840353797441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8666509142350521762024149 203121308023840353797441)
                  ·
                    rfl

theorem cell22_1780098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1780098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780098 prefixEnd_1780098 := by exact prefixLift 1780098
  have htrace : WordTrace (prefixWord ++ tailWord_1780098) baseStart_1780098 baseEnd_1780098 := by
    simpa [prefixWord, tailWord_1780098, baseEnd_1780098] using wordTrace_append hprefix tailTrace_1780098
  have hstable : (prefixWord ++ tailWord_1780098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780098).length < 2 ^ (prefixWord ++ tailWord_1780098).sum := by decide
  have hdescent : baseEnd_1780098 < baseStart_1780098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780156 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 4, 4]
def baseStart_1780156 : Nat := 118140960795 + 1780156 * 2 ^ 59
def prefixEnd_1780156 : Nat := 4983230072969 + 3 ^ 40 * 1780156 * 2
def baseEnd_1780156 : Nat := 609383778656828243442145

theorem tailTrace_1780156 : CollatzResearch.WordTrace tailWord_1780156 prefixEnd_1780156 609383778656828243442145 := by
  unfold tailWord_1780156
  simp only [CollatzResearch.WordTrace]
  refine ⟨32463811669403156642564161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43285082225870875523418881 32463811669403156642564161)
  ·
    refine ⟨24347858752052367481923121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32463811669403156642564161 24347858752052367481923121)
    ·
      refine ⟨18260894064039275611442341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24347858752052367481923121 18260894064039275611442341)
      ·
        refine ⟨3423917637007364177145439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18260894064039275611442341 3423917637007364177145439)
        ·
          refine ⟨5135876455511046265718159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3423917637007364177145439 5135876455511046265718159)
          ·
            refine ⟨7703814683266569398577239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5135876455511046265718159 7703814683266569398577239)
            ·
              refine ⟨11555722024899854097865859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7703814683266569398577239 11555722024899854097865859)
              ·
                refine ⟨17333583037349781146798789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11555722024899854097865859 17333583037349781146798789)
                ·
                  refine ⟨3250046819503083965024773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17333583037349781146798789 3250046819503083965024773)
                  ·
                    refine ⟨609383778656828243442145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3250046819503083965024773 609383778656828243442145)
                    ·
                      rfl

theorem cell22_1780156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_1780156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780156 prefixEnd_1780156 := by exact prefixLift 1780156
  have htrace : WordTrace (prefixWord ++ tailWord_1780156) baseStart_1780156 baseEnd_1780156 := by
    simpa [prefixWord, tailWord_1780156, baseEnd_1780156] using wordTrace_append hprefix tailTrace_1780156
  have hstable : (prefixWord ++ tailWord_1780156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780156).length < 2 ^ (prefixWord ++ tailWord_1780156).sum := by decide
  have hdescent : baseEnd_1780156 < baseStart_1780156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780186 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 5, 3]
def baseStart_1780186 : Nat := 118140960795 + 1780186 * 2 ^ 59
def prefixEnd_1780186 : Nat := 4983230072969 + 3 ^ 40 * 1780186 * 2
def baseEnd_1780186 : Nat := 609394048269918165192053

theorem tailTrace_1780186 : CollatzResearch.WordTrace tailWord_1780186 prefixEnd_1780186 609394048269918165192053 := by
  unfold tailWord_1780186
  simp only [CollatzResearch.WordTrace]
  refine ⟨16232179382174407102180103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43285811685798418939146941 16232179382174407102180103)
  ·
    refine ⟨24348269073261610653270155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16232179382174407102180103 24348269073261610653270155)
    ·
      refine ⟨36522403609892415979905233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24348269073261610653270155 36522403609892415979905233)
      ·
        refine ⟨27391802707419311984928925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36522403609892415979905233 27391802707419311984928925)
        ·
          refine ⟨10271926015282241994348347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27391802707419311984928925 10271926015282241994348347)
          ·
            refine ⟨15407889022923362991522521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10271926015282241994348347 15407889022923362991522521)
            ·
              refine ⟨11555916767192522243641891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15407889022923362991522521 11555916767192522243641891)
              ·
                refine ⟨17333875150788783365462837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11555916767192522243641891 17333875150788783365462837)
                ·
                  refine ⟨1625050795386448440512141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17333875150788783365462837 1625050795386448440512141)
                  ·
                    refine ⟨609394048269918165192053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1625050795386448440512141 609394048269918165192053)
                    ·
                      rfl

theorem cell22_1780186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_1780186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780186 prefixEnd_1780186 := by exact prefixLift 1780186
  have htrace : WordTrace (prefixWord ++ tailWord_1780186) baseStart_1780186 baseEnd_1780186 := by
    simpa [prefixWord, tailWord_1780186, baseEnd_1780186] using wordTrace_append hprefix tailTrace_1780186
  have hstable : (prefixWord ++ tailWord_1780186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780186).length < 2 ^ (prefixWord ++ tailWord_1780186).sum := by decide
  have hdescent : baseEnd_1780186 < baseStart_1780186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780203 : List Nat := [1, 1, 1, 1, 2, 3, 4, 5, 1, 3]
def baseStart_1780203 : Nat := 118140960795 + 1780203 * 2 ^ 59
def prefixEnd_1780203 : Nat := 4983230072969 + 3 ^ 40 * 1780203 * 2
def baseEnd_1780203 : Nat := 609399867717335787517001

theorem tailTrace_1780203 : CollatzResearch.WordTrace tailWord_1780203 prefixEnd_1780203 609399867717335787517001 := by
  unfold tailWord_1780203
  simp only [CollatzResearch.WordTrace]
  refine ⟨64929337569636040312089263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43286225046424026874726175 64929337569636040312089263)
  ·
    refine ⟨97394006354454060468133895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64929337569636040312089263 97394006354454060468133895)
    ·
      refine ⟨146091009531681090702200843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97394006354454060468133895 146091009531681090702200843)
      ·
        refine ⟨219136514297521636053301265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146091009531681090702200843 219136514297521636053301265)
        ·
          refine ⟨164352385723141227039975949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219136514297521636053301265 164352385723141227039975949)
          ·
            refine ⟨61632144646177960139990981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164352385723141227039975949 61632144646177960139990981)
            ·
              refine ⟨11556027121158367526248309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61632144646177960139990981 11556027121158367526248309)
              ·
                refine ⟨1083377542608596955585779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11556027121158367526248309 1083377542608596955585779)
                ·
                  refine ⟨1625066313912895433378669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1083377542608596955585779 1625066313912895433378669)
                  ·
                    refine ⟨609399867717335787517001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1625066313912895433378669 609399867717335787517001)
                    ·
                      rfl

theorem cell22_1780203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 1, 3].length) (baseStart_1780203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780203 prefixEnd_1780203 := by exact prefixLift 1780203
  have htrace : WordTrace (prefixWord ++ tailWord_1780203) baseStart_1780203 baseEnd_1780203 := by
    simpa [prefixWord, tailWord_1780203, baseEnd_1780203] using wordTrace_append hprefix tailTrace_1780203
  have hstable : (prefixWord ++ tailWord_1780203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780203).length < 2 ^ (prefixWord ++ tailWord_1780203).sum := by decide
  have hdescent : baseEnd_1780203 < baseStart_1780203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780216 : List Nat := [2, 1, 2, 1, 1, 4, 4, 2, 5]
def baseStart_1780216 : Nat := 118140960795 + 1780216 * 2 ^ 59
def prefixEnd_1780216 : Nat := 4983230072969 + 3 ^ 40 * 1780216 * 2
def baseEnd_1780216 : Nat := 203134772627669362313987

theorem tailTrace_1780216 : CollatzResearch.WordTrace tailWord_1780216 prefixEnd_1780216 203134772627669362313987 := by
  unfold tailWord_1780216
  simp only [CollatzResearch.WordTrace]
  refine ⟨32464905859294471766156251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43286541145725962354875001 32464905859294471766156251)
  ·
    refine ⟨48697358788941707649234377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32464905859294471766156251 48697358788941707649234377)
    ·
      refine ⟨36523019091706280736925783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48697358788941707649234377 36523019091706280736925783)
      ·
        refine ⟨54784528637559421105388675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36523019091706280736925783 54784528637559421105388675)
        ·
          refine ⟨82176792956339131658083013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54784528637559421105388675 82176792956339131658083013)
          ·
            refine ⟨15408148679313587185890565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82176792956339131658083013 15408148679313587185890565)
            ·
              refine ⟨2889027877371297597354481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15408148679313587185890565 2889027877371297597354481)
              ·
                refine ⟨2166770908028473198015861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2889027877371297597354481 2166770908028473198015861)
                ·
                  refine ⟨203134772627669362313987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2166770908028473198015861 203134772627669362313987)
                  ·
                    rfl

theorem cell22_1780216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 5].length) (baseStart_1780216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780216 prefixEnd_1780216 := by exact prefixLift 1780216
  have htrace : WordTrace (prefixWord ++ tailWord_1780216) baseStart_1780216 baseEnd_1780216 := by
    simpa [prefixWord, tailWord_1780216, baseEnd_1780216] using wordTrace_append hprefix tailTrace_1780216
  have hstable : (prefixWord ++ tailWord_1780216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780216).length < 2 ^ (prefixWord ++ tailWord_1780216).sum := by decide
  have hdescent : baseEnd_1780216 < baseStart_1780216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780237 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1780237 : Nat := 118140960795 + 1780237 * 2 ^ 59
def prefixEnd_1780237 : Nat := 4983230072969 + 3 ^ 40 * 1780237 * 2
def baseEnd_1780237 : Nat := 609411506612171032166897

theorem tailTrace_1780237 : CollatzResearch.WordTrace tailWord_1780237 prefixEnd_1780237 609411506612171032166897 := by
  unfold tailWord_1780237
  simp only [CollatzResearch.WordTrace]
  refine ⟨64930577651512864118826965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43287051767675242745884643 64930577651512864118826965)
  ·
    refine ⟨1521810413707332752785007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 64930577651512864118826965 1521810413707332752785007)
    ·
      refine ⟨2282715620560999129177511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1521810413707332752785007 2282715620560999129177511)
      ·
        refine ⟨3424073430841498693766267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2282715620560999129177511 3424073430841498693766267)
        ·
          refine ⟨5136110146262248040649401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3424073430841498693766267 5136110146262248040649401)
          ·
            refine ⟨3852082609696686030487051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5136110146262248040649401 3852082609696686030487051)
            ·
              refine ⟨5778123914545029045730577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3852082609696686030487051 5778123914545029045730577)
              ·
                refine ⟨4333592935908771784297933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5778123914545029045730577 4333592935908771784297933)
                ·
                  refine ⟨1625097350965789419111725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4333592935908771784297933 1625097350965789419111725)
                  ·
                    refine ⟨609411506612171032166897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1625097350965789419111725 609411506612171032166897)
                    ·
                      rfl

theorem cell22_1780237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1780237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780237 prefixEnd_1780237 := by exact prefixLift 1780237
  have htrace : WordTrace (prefixWord ++ tailWord_1780237) baseStart_1780237 baseEnd_1780237 := by
    simpa [prefixWord, tailWord_1780237, baseEnd_1780237] using wordTrace_append hprefix tailTrace_1780237
  have hstable : (prefixWord ++ tailWord_1780237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780237).length < 2 ^ (prefixWord ++ tailWord_1780237).sum := by decide
  have hdescent : baseEnd_1780237 < baseStart_1780237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780278 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_1780278 : Nat := 118140960795 + 1780278 * 2 ^ 59
def prefixEnd_1780278 : Nat := 4983230072969 + 3 ^ 40 * 1780278 * 2
def baseEnd_1780278 : Nat := 203141847250020197297257

theorem tailTrace_1780278 : CollatzResearch.WordTrace tailWord_1780278 prefixEnd_1780278 203141847250020197297257 := by
  unfold tailWord_1780278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4058254565272770507566843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43288048696242885414046325 4058254565272770507566843)
  ·
    refine ⟨6087381847909155761350265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4058254565272770507566843 6087381847909155761350265)
    ·
      refine ⟨4565536385931866821012699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6087381847909155761350265 4565536385931866821012699)
      ·
        refine ⟨6848304578897800231519049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4565536385931866821012699 6848304578897800231519049)
        ·
          refine ⟨5136228434173350173639287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6848304578897800231519049 5136228434173350173639287)
          ·
            refine ⟨7704342651260025260458931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5136228434173350173639287 7704342651260025260458931)
            ·
              refine ⟨11556513976890037890688397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7704342651260025260458931 11556513976890037890688397)
              ·
                refine ⟨4333692741333764209008149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11556513976890037890688397 4333692741333764209008149)
                ·
                  refine ⟨203141847250020197297257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4333692741333764209008149 203141847250020197297257)
                  ·
                    rfl

theorem cell22_1780278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_1780278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780278 prefixEnd_1780278 := by exact prefixLift 1780278
  have htrace : WordTrace (prefixWord ++ tailWord_1780278) baseStart_1780278 baseEnd_1780278 := by
    simpa [prefixWord, tailWord_1780278, baseEnd_1780278] using wordTrace_append hprefix tailTrace_1780278
  have hstable : (prefixWord ++ tailWord_1780278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780278).length < 2 ^ (prefixWord ++ tailWord_1780278).sum := by decide
  have hdescent : baseEnd_1780278 < baseStart_1780278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780293 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 1, 5]
def baseStart_1780293 : Nat := 118140960795 + 1780293 * 2 ^ 59
def prefixEnd_1780293 : Nat := 4983230072969 + 3 ^ 40 * 1780293 * 2
def baseEnd_1780293 : Nat := 609430676556605552766725

theorem tailTrace_1780293 : CollatzResearch.WordTrace tailWord_1780293 prefixEnd_1780293 609430676556605552766725 := by
  unfold tailWord_1780293
  simp only [CollatzResearch.WordTrace]
  refine ⟨64932620139309985682865533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43288413426206657121910355 64932620139309985682865533)
  ·
    refine ⟨24349732552241244631074575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64932620139309985682865533 24349732552241244631074575)
    ·
      refine ⟨36524598828361866946611863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24349732552241244631074575 36524598828361866946611863)
      ·
        refine ⟨54786898242542800419917795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36524598828361866946611863 54786898242542800419917795)
        ·
          refine ⟨82180347363814200629876693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54786898242542800419917795 82180347363814200629876693)
          ·
            refine ⟨1926101891339395327262735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 82180347363814200629876693 1926101891339395327262735)
            ·
              refine ⟨2889152837009092990894103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1926101891339395327262735 2889152837009092990894103)
              ·
                refine ⟨4333729255513639486341155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2889152837009092990894103 4333729255513639486341155)
                ·
                  refine ⟨6500593883270459229511733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4333729255513639486341155 6500593883270459229511733)
                  ·
                    refine ⟨609430676556605552766725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6500593883270459229511733 609430676556605552766725)
                    ·
                      rfl

theorem cell22_1780293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_1780293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780293 prefixEnd_1780293 := by exact prefixLift 1780293
  have htrace : WordTrace (prefixWord ++ tailWord_1780293) baseStart_1780293 baseEnd_1780293 := by
    simpa [prefixWord, tailWord_1780293, baseEnd_1780293] using wordTrace_append hprefix tailTrace_1780293
  have hstable : (prefixWord ++ tailWord_1780293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780293).length < 2 ^ (prefixWord ++ tailWord_1780293).sum := by decide
  have hdescent : baseEnd_1780293 < baseStart_1780293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780306 : List Nat := [3, 2, 2, 1, 2, 1, 3, 8]
def baseStart_1780306 : Nat := 118140960795 + 1780306 * 2 ^ 59
def prefixEnd_1780306 : Nat := 4983230072969 + 3 ^ 40 * 1780306 * 2
def baseEnd_1780306 : Nat := 67715014080253094687965

theorem tailTrace_1780306 : CollatzResearch.WordTrace tailWord_1780306 prefixEnd_1780306 67715014080253094687965 := by
  unfold tailWord_1780306
  simp only [CollatzResearch.WordTrace]
  refine ⟨16233273572065722225772193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43288729525508592602059181 16233273572065722225772193)
  ·
    refine ⟨12174955179049291669329145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16233273572065722225772193 12174955179049291669329145)
    ·
      refine ⟨9131216384286968751996859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12174955179049291669329145 9131216384286968751996859)
      ·
        refine ⟨13696824576430453127995289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9131216384286968751996859 13696824576430453127995289)
        ·
          refine ⟨10272618432322839845996467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13696824576430453127995289 10272618432322839845996467)
          ·
            refine ⟨15408927648484259768994701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10272618432322839845996467 15408927648484259768994701)
            ·
              refine ⟨5778347868181597413373013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15408927648484259768994701 5778347868181597413373013)
              ·
                refine ⟨67715014080253094687965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5778347868181597413373013 67715014080253094687965)
                ·
                  rfl

theorem cell22_1780306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 8].length) (baseStart_1780306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780306 prefixEnd_1780306 := by exact prefixLift 1780306
  have htrace : WordTrace (prefixWord ++ tailWord_1780306) baseStart_1780306 baseEnd_1780306 := by
    simpa [prefixWord, tailWord_1780306, baseEnd_1780306] using wordTrace_append hprefix tailTrace_1780306
  have hstable : (prefixWord ++ tailWord_1780306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780306).length < 2 ^ (prefixWord ++ tailWord_1780306).sum := by decide
  have hdescent : baseEnd_1780306 < baseStart_1780306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780385 : List Nat := [1, 2, 3, 3, 3, 1, 2, 2, 5]
def baseStart_1780385 : Nat := 118140960795 + 1780385 * 2 ^ 59
def prefixEnd_1780385 : Nat := 4983230072969 + 3 ^ 40 * 1780385 * 2
def baseEnd_1780385 : Nat := 203154056678915993155481

theorem tailTrace_1780385 : CollatzResearch.WordTrace tailWord_1780385 prefixEnd_1780385 203154056678915993155481 := by
  unfold tailWord_1780385
  simp only [CollatzResearch.WordTrace]
  refine ⟨64935975654976685395214609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43290650436651123596809739 64935975654976685395214609)
  ·
    refine ⟨48701981741232514046410957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64935975654976685395214609 48701981741232514046410957)
    ·
      refine ⟨18263243152962192767404109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48701981741232514046410957 18263243152962192767404109)
      ·
        refine ⟨6848716182360822287776541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18263243152962192767404109 6848716182360822287776541)
        ·
          refine ⟨2568268568385308357916203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6848716182360822287776541 2568268568385308357916203)
          ·
            refine ⟨3852402852577962536874305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2568268568385308357916203 3852402852577962536874305)
            ·
              refine ⟨2889302139433471902655729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3852402852577962536874305 2889302139433471902655729)
              ·
                refine ⟨2166976604575103926991797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2889302139433471902655729 2166976604575103926991797)
                ·
                  refine ⟨203154056678915993155481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2166976604575103926991797 203154056678915993155481)
                  ·
                    rfl

theorem cell22_1780385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 5].length) (baseStart_1780385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780385 prefixEnd_1780385 := by exact prefixLift 1780385
  have htrace : WordTrace (prefixWord ++ tailWord_1780385) baseStart_1780385 baseEnd_1780385 := by
    simpa [prefixWord, tailWord_1780385, baseEnd_1780385] using wordTrace_append hprefix tailTrace_1780385
  have hstable : (prefixWord ++ tailWord_1780385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780385).length < 2 ^ (prefixWord ++ tailWord_1780385).sum := by decide
  have hdescent : baseEnd_1780385 < baseStart_1780385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780413 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 6]
def baseStart_1780413 : Nat := 118140960795 + 1780413 * 2 ^ 59
def prefixEnd_1780413 : Nat := 4983230072969 + 3 ^ 40 * 1780413 * 2
def baseEnd_1780413 : Nat := 203157251669655079922119

theorem tailTrace_1780413 : CollatzResearch.WordTrace tailWord_1780413 prefixEnd_1780413 203157251669655079922119 := by
  unfold tailWord_1780413
  simp only [CollatzResearch.WordTrace]
  refine ⟨64936996898875246177233893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43291331265916830784822595 64936996898875246177233893)
  ·
    refine ⟨12175686918539108658231355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64936996898875246177233893 12175686918539108658231355)
    ·
      refine ⟨18263530377808662987347033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12175686918539108658231355 18263530377808662987347033)
      ·
        refine ⟨13697647783356497240510275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18263530377808662987347033 13697647783356497240510275)
        ·
          refine ⟨20546471675034745860765413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13697647783356497240510275 20546471675034745860765413)
          ·
            refine ⟨3852463439069014848893515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20546471675034745860765413 3852463439069014848893515)
            ·
              refine ⟨5778695158603522273340273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3852463439069014848893515 5778695158603522273340273)
              ·
                refine ⟨4334021368952641705005205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5778695158603522273340273 4334021368952641705005205)
                ·
                  refine ⟨203157251669655079922119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4334021368952641705005205 203157251669655079922119)
                  ·
                    rfl

theorem cell22_1780413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_1780413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780413 prefixEnd_1780413 := by exact prefixLift 1780413
  have htrace : WordTrace (prefixWord ++ tailWord_1780413) baseStart_1780413 baseEnd_1780413 := by
    simpa [prefixWord, tailWord_1780413, baseEnd_1780413] using wordTrace_append hprefix tailTrace_1780413
  have hstable : (prefixWord ++ tailWord_1780413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780413).length < 2 ^ (prefixWord ++ tailWord_1780413).sum := by decide
  have hdescent : baseEnd_1780413 < baseStart_1780413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780430 : List Nat := [4, 1, 1, 1, 3, 2, 1, 5, 4]
def baseStart_1780430 : Nat := 118140960795 + 1780430 * 2 ^ 59
def prefixEnd_1780430 : Nat := 4983230072969 + 3 ^ 40 * 1780430 * 2
def baseEnd_1780430 : Nat := 203159191485460954030435

theorem tailTrace_1780430 : CollatzResearch.WordTrace tailWord_1780430 prefixEnd_1780430 203159191485460954030435 := by
  unfold tailWord_1780430
  simp only [CollatzResearch.WordTrace]
  refine ⟨8117202117476707260075343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43291744626542438720401829 8117202117476707260075343)
  ·
    refine ⟨12175803176215060890113015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8117202117476707260075343 12175803176215060890113015)
    ·
      refine ⟨18263704764322591335169523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12175803176215060890113015 18263704764322591335169523)
      ·
        refine ⟨27395557146483887002754285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18263704764322591335169523 27395557146483887002754285)
        ·
          refine ⟨10273333929931457626032857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27395557146483887002754285 10273333929931457626032857)
          ·
            refine ⟨7705000447448593219524643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10273333929931457626032857 7705000447448593219524643)
            ·
              refine ⟨11557500671172889829286965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7705000447448593219524643 11557500671172889829286965)
              ·
                refine ⟨1083515687922458421495653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11557500671172889829286965 1083515687922458421495653)
                ·
                  refine ⟨203159191485460954030435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1083515687922458421495653 203159191485460954030435)
                  ·
                    rfl

theorem cell22_1780430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_1780430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780430 prefixEnd_1780430 := by exact prefixLift 1780430
  have htrace : WordTrace (prefixWord ++ tailWord_1780430) baseStart_1780430 baseEnd_1780430 := by
    simpa [prefixWord, tailWord_1780430, baseEnd_1780430] using wordTrace_append hprefix tailTrace_1780430
  have hstable : (prefixWord ++ tailWord_1780430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780430).length < 2 ^ (prefixWord ++ tailWord_1780430).sum := by decide
  have hdescent : baseEnd_1780430 < baseStart_1780430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780441 : List Nat := [1, 2, 1, 2, 3, 2, 11]
def baseStart_1780441 : Nat := 118140960795 + 1780441 * 2 ^ 59
def prefixEnd_1780441 : Nat := 4983230072969 + 3 ^ 40 * 1780441 * 2
def baseEnd_1780441 : Nat := 22573382962266018520973

theorem tailTrace_1780441 : CollatzResearch.WordTrace tailWord_1780441 prefixEnd_1780441 22573382962266018520973 := by
  unfold tailWord_1780441
  simp only [CollatzResearch.WordTrace]
  refine ⟨64938018142773806959253177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43292012095182537972835451 64938018142773806959253177)
  ·
    refine ⟨48703513607080355219439883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64938018142773806959253177 48703513607080355219439883)
    ·
      refine ⟨73055270410620532829159825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48703513607080355219439883 73055270410620532829159825)
      ·
        refine ⟨54791452807965399621869869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73055270410620532829159825 54791452807965399621869869)
        ·
          refine ⟨20546794802987024858201201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54791452807965399621869869 20546794802987024858201201)
          ·
            refine ⟨15410096102240268643650901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20546794802987024858201201 15410096102240268643650901)
            ·
              refine ⟨22573382962266018520973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15410096102240268643650901 22573382962266018520973)
              ·
                rfl

theorem cell22_1780441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 11].length) (baseStart_1780441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780441 prefixEnd_1780441 := by exact prefixLift 1780441
  have htrace : WordTrace (prefixWord ++ tailWord_1780441) baseStart_1780441 baseEnd_1780441 := by
    simpa [prefixWord, tailWord_1780441, baseEnd_1780441] using wordTrace_append hprefix tailTrace_1780441
  have hstable : (prefixWord ++ tailWord_1780441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780441).length < 2 ^ (prefixWord ++ tailWord_1780441).sum := by decide
  have hdescent : baseEnd_1780441 < baseStart_1780441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780520 : List Nat := [2, 1, 5, 1, 1, 1, 3, 3, 5]
def baseStart_1780520 : Nat := 118140960795 + 1780520 * 2 ^ 59
def prefixEnd_1780520 : Nat := 4983230072969 + 3 ^ 40 * 1780520 * 2
def baseEnd_1780520 : Nat := 203169461098550875780343

theorem tailTrace_1780520 : CollatzResearch.WordTrace tailWord_1780520 prefixEnd_1780520 203169461098550875780343 := by
  unfold tailWord_1780520
  simp only [CollatzResearch.WordTrace]
  refine ⟨32470449754743801725689507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43293933006325068967586009 32470449754743801725689507)
  ·
    refine ⟨48705674632115702588534261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32470449754743801725689507 48705674632115702588534261)
    ·
      refine ⟨4566156996760847117675087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48705674632115702588534261 4566156996760847117675087)
      ·
        refine ⟨6849235495141270676512631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4566156996760847117675087 6849235495141270676512631)
        ·
          refine ⟨10273853242711906014768947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6849235495141270676512631 10273853242711906014768947)
          ·
            refine ⟨15410779864067859022153421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10273853242711906014768947 15410779864067859022153421)
            ·
              refine ⟨5779042449025447133307533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15410779864067859022153421 5779042449025447133307533)
              ·
                refine ⟨2167140918384542674990325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5779042449025447133307533 2167140918384542674990325)
                ·
                  refine ⟨203169461098550875780343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2167140918384542674990325 203169461098550875780343)
                  ·
                    rfl

theorem cell22_1780520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 5].length) (baseStart_1780520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780520 prefixEnd_1780520 := by exact prefixLift 1780520
  have htrace : WordTrace (prefixWord ++ tailWord_1780520) baseStart_1780520 baseEnd_1780520 := by
    simpa [prefixWord, tailWord_1780520, baseEnd_1780520] using wordTrace_append hprefix tailTrace_1780520
  have hstable : (prefixWord ++ tailWord_1780520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780520).length < 2 ^ (prefixWord ++ tailWord_1780520).sum := by decide
  have hdescent : baseEnd_1780520 < baseStart_1780520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780580 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_1780580 : Nat := 118140960795 + 1780580 * 2 ^ 59
def prefixEnd_1780580 : Nat := 4983230072969 + 3 ^ 40 * 1780580 * 2
def baseEnd_1780580 : Nat := 609528922521832470840845

theorem tailTrace_1780580 : CollatzResearch.WordTrace tailWord_1780580 prefixEnd_1780580 609528922521832470840845 := by
  unfold tailWord_1780580
  simp only [CollatzResearch.WordTrace]
  refine ⟨32471543944635116849281597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43295391926180155799042129 32471543944635116849281597)
  ·
    refine ⟨12176828979238168818480599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32471543944635116849281597 12176828979238168818480599)
    ·
      refine ⟨18265243468857253227720899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12176828979238168818480599 18265243468857253227720899)
      ·
        refine ⟨27397865203285879841581349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18265243468857253227720899 27397865203285879841581349)
        ·
          refine ⟨5137099725616102470296503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27397865203285879841581349 5137099725616102470296503)
          ·
            refine ⟨7705649588424153705444755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5137099725616102470296503 7705649588424153705444755)
            ·
              refine ⟨11558474382636230558167133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7705649588424153705444755 11558474382636230558167133)
              ·
                refine ⟨4334427893488586459312675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11558474382636230558167133 4334427893488586459312675)
                ·
                  refine ⟨6501641840232879688969013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4334427893488586459312675 6501641840232879688969013)
                  ·
                    refine ⟨609528922521832470840845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6501641840232879688969013 609528922521832470840845)
                    ·
                      rfl

theorem cell22_1780580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_1780580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780580 prefixEnd_1780580 := by exact prefixLift 1780580
  have htrace : WordTrace (prefixWord ++ tailWord_1780580) baseStart_1780580 baseEnd_1780580 := by
    simpa [prefixWord, tailWord_1780580, baseEnd_1780580] using wordTrace_append hprefix tailTrace_1780580
  have hstable : (prefixWord ++ tailWord_1780580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780580).length < 2 ^ (prefixWord ++ tailWord_1780580).sum := by decide
  have hdescent : baseEnd_1780580 < baseStart_1780580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780595 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 2, 4]
def baseStart_1780595 : Nat := 118140960795 + 1780595 * 2 ^ 59
def prefixEnd_1780595 : Nat := 4983230072969 + 3 ^ 40 * 1780595 * 2
def baseEnd_1780595 : Nat := 609534057328377431715799

theorem tailTrace_1780595 : CollatzResearch.WordTrace tailWord_1780595 prefixEnd_1780595 609534057328377431715799 := by
  unfold tailWord_1780595
  simp only [CollatzResearch.WordTrace]
  refine ⟨64943634984215891260359239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43295756656143927506906159 64943634984215891260359239)
  ·
    refine ⟨97415452476323836890538859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64943634984215891260359239 97415452476323836890538859)
    ·
      refine ⟨146123178714485755335808289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97415452476323836890538859 146123178714485755335808289)
      ·
        refine ⟨109592384035864316501856217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146123178714485755335808289 109592384035864316501856217)
        ·
          refine ⟨82194288026898237376392163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109592384035864316501856217 82194288026898237376392163)
          ·
            refine ⟨123291432040347356064588245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82194288026898237376392163 123291432040347356064588245)
            ·
              refine ⟨2889642938445641157763787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 123291432040347356064588245 2889642938445641157763787)
              ·
                refine ⟨4334464407668461736645681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2889642938445641157763787 4334464407668461736645681)
                ·
                  refine ⟨3250848305751346302484261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4334464407668461736645681 3250848305751346302484261)
                  ·
                    refine ⟨609534057328377431715799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3250848305751346302484261 609534057328377431715799)
                    ·
                      rfl

theorem cell22_1780595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 4].length) (baseStart_1780595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780595 prefixEnd_1780595 := by exact prefixLift 1780595
  have htrace : WordTrace (prefixWord ++ tailWord_1780595) baseStart_1780595 baseEnd_1780595 := by
    simpa [prefixWord, tailWord_1780595, baseEnd_1780595] using wordTrace_append hprefix tailTrace_1780595
  have hstable : (prefixWord ++ tailWord_1780595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780595).length < 2 ^ (prefixWord ++ tailWord_1780595).sum := by decide
  have hdescent : baseEnd_1780595 < baseStart_1780595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780678 : List Nat := [6, 1, 3, 1, 1, 1, 2, 7]
def baseStart_1780678 : Nat := 118140960795 + 1780678 * 2 ^ 59
def prefixEnd_1780678 : Nat := 4983230072969 + 3 ^ 40 * 1780678 * 2
def baseEnd_1780678 : Nat := 67729163324954764654505

theorem tailTrace_1780678 : CollatzResearch.WordTrace tailWord_1780678 prefixEnd_1780678 67729163324954764654505 := by
  unfold tailWord_1780678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2029583195091099888613459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43297774828610130957087125 2029583195091099888613459)
  ·
    refine ⟨3044374792636649832920189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2029583195091099888613459 3044374792636649832920189)
    ·
      refine ⟨1141640547238743687345071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3044374792636649832920189 1141640547238743687345071)
      ·
        refine ⟨1712460820858115531017607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1141640547238743687345071 1712460820858115531017607)
        ·
          refine ⟨2568691231287173296526411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1712460820858115531017607 2568691231287173296526411)
          ·
            refine ⟨3853036846930759944789617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2568691231287173296526411 3853036846930759944789617)
            ·
              refine ⟨2889777635198069958592213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3853036846930759944789617 2889777635198069958592213)
              ·
                refine ⟨67729163324954764654505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2889777635198069958592213 67729163324954764654505)
                ·
                  rfl

theorem cell22_1780678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_1780678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780678 prefixEnd_1780678 := by exact prefixLift 1780678
  have htrace : WordTrace (prefixWord ++ tailWord_1780678) baseStart_1780678 baseEnd_1780678 := by
    simpa [prefixWord, tailWord_1780678, baseEnd_1780678] using wordTrace_append hprefix tailTrace_1780678
  have hstable : (prefixWord ++ tailWord_1780678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780678).length < 2 ^ (prefixWord ++ tailWord_1780678).sum := by decide
  have hdescent : baseEnd_1780678 < baseStart_1780678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780719 : List Nat := [1, 1, 2, 1, 4, 4, 3, 1, 1, 4]
def baseStart_1780719 : Nat := 118140960795 + 1780719 * 2 ^ 59
def prefixEnd_1780719 : Nat := 4983230072969 + 3 ^ 40 * 1780719 * 2
def baseEnd_1780719 : Nat := 609576505062482441615419

theorem tailTrace_1780719 : CollatzResearch.WordTrace tailWord_1780719 prefixEnd_1780719 609576505062482441615419 := by
  unfold tailWord_1780719
  simp only [CollatzResearch.WordTrace]
  refine ⟨64948157635766660437873211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43298771757177773625248807 64948157635766660437873211)
  ·
    refine ⟨97422236453649990656809817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64948157635766660437873211 97422236453649990656809817)
    ·
      refine ⟨73066677340237492992607363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97422236453649990656809817 73066677340237492992607363)
      ·
        refine ⟨109600016010356239488911045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73066677340237492992607363 109600016010356239488911045)
        ·
          refine ⟨20550003001941794904170821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109600016010356239488911045 20550003001941794904170821)
          ·
            refine ⟨3853125562864086544532029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20550003001941794904170821 3853125562864086544532029)
            ·
              refine ⟨1444922086074032454199511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3853125562864086544532029 1444922086074032454199511)
              ·
                refine ⟨2167383129111048681299267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444922086074032454199511 2167383129111048681299267)
                ·
                  refine ⟨3251074693666573021948901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167383129111048681299267 3251074693666573021948901)
                  ·
                    refine ⟨609576505062482441615419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3251074693666573021948901 609576505062482441615419)
                    ·
                      rfl

theorem cell22_1780719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 1, 4].length) (baseStart_1780719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780719 prefixEnd_1780719 := by exact prefixLift 1780719
  have htrace : WordTrace (prefixWord ++ tailWord_1780719) baseStart_1780719 baseEnd_1780719 := by
    simpa [prefixWord, tailWord_1780719, baseEnd_1780719] using wordTrace_append hprefix tailTrace_1780719
  have hstable : (prefixWord ++ tailWord_1780719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780719).length < 2 ^ (prefixWord ++ tailWord_1780719).sum := by decide
  have hdescent : baseEnd_1780719 < baseStart_1780719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780762 : List Nat := [3, 1, 1, 3, 1, 2, 5, 6]
def baseStart_1780762 : Nat := 118140960795 + 1780762 * 2 ^ 59
def prefixEnd_1780762 : Nat := 4983230072969 + 3 ^ 40 * 1780762 * 2
def baseEnd_1780762 : Nat := 67732358315693851421143

theorem tailTrace_1780762 : CollatzResearch.WordTrace tailWord_1780762 prefixEnd_1780762 67732358315693851421143 := by
  unfold tailWord_1780762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16237431493652719695422135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43299817316407252521125693 16237431493652719695422135)
  ·
    refine ⟨24356147240479079543133203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16237431493652719695422135 24356147240479079543133203)
    ·
      refine ⟨36534220860718619314699805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24356147240479079543133203 36534220860718619314699805)
      ·
        refine ⟨13700332822769482243012427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36534220860718619314699805 13700332822769482243012427)
        ·
          refine ⟨20550499234154223364518641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13700332822769482243012427 20550499234154223364518641)
          ·
            refine ⟨15412874425615667523388981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20550499234154223364518641 15412874425615667523388981)
            ·
              refine ⟨1444956977401468830317717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15412874425615667523388981 1444956977401468830317717)
              ·
                refine ⟨67732358315693851421143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1444956977401468830317717 67732358315693851421143)
                ·
                  rfl

theorem cell22_1780762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 6].length) (baseStart_1780762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780762 prefixEnd_1780762 := by exact prefixLift 1780762
  have htrace : WordTrace (prefixWord ++ tailWord_1780762) baseStart_1780762 baseEnd_1780762 := by
    simpa [prefixWord, tailWord_1780762, baseEnd_1780762] using wordTrace_append hprefix tailTrace_1780762
  have hstable : (prefixWord ++ tailWord_1780762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780762).length < 2 ^ (prefixWord ++ tailWord_1780762).sum := by decide
  have hdescent : baseEnd_1780762 < baseStart_1780762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780854 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_1780854 : Nat := 118140960795 + 1780854 * 2 ^ 59
def prefixEnd_1780854 : Nat := 4983230072969 + 3 ^ 40 * 1780854 * 2
def baseEnd_1780854 : Nat := 609622718321387089490005

theorem tailTrace_1780854 : CollatzResearch.WordTrace tailWord_1780854 prefixEnd_1780854 609622718321387089490005 := by
  unfold tailWord_1780854
  simp only [CollatzResearch.WordTrace]
  refine ⟨4059567593142348655877351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43302054326851718996025077 4059567593142348655877351)
  ·
    refine ⟨6089351389713522983816027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4059567593142348655877351 6089351389713522983816027)
    ·
      refine ⟨9134027084570284475724041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6089351389713522983816027 9134027084570284475724041)
      ·
        refine ⟨6850520313427713356793031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9134027084570284475724041 6850520313427713356793031)
        ·
          refine ⟨10275780470141570035189547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6850520313427713356793031 10275780470141570035189547)
          ·
            refine ⟨15413670705212355052784321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10275780470141570035189547 15413670705212355052784321)
            ·
              refine ⟨11560253028909266289588241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15413670705212355052784321 11560253028909266289588241)
              ·
                refine ⟨8670189771681949717191181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11560253028909266289588241 8670189771681949717191181)
                ·
                  refine ⟨3251321164380731143946693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8670189771681949717191181 3251321164380731143946693)
                  ·
                    refine ⟨609622718321387089490005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3251321164380731143946693 609622718321387089490005)
                    ·
                      rfl

theorem cell22_1780854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_1780854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780854 prefixEnd_1780854 := by exact prefixLift 1780854
  have htrace : WordTrace (prefixWord ++ tailWord_1780854) baseStart_1780854 baseEnd_1780854 := by
    simpa [prefixWord, tailWord_1780854, baseEnd_1780854] using wordTrace_append hprefix tailTrace_1780854
  have hstable : (prefixWord ++ tailWord_1780854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780854).length < 2 ^ (prefixWord ++ tailWord_1780854).sum := by decide
  have hdescent : baseEnd_1780854 < baseStart_1780854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780867 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 1, 5]
def baseStart_1780867 : Nat := 118140960795 + 1780867 * 2 ^ 59
def prefixEnd_1780867 : Nat := 4983230072969 + 3 ^ 40 * 1780867 * 2
def baseEnd_1780867 : Nat := 609627168487059388914965

theorem tailTrace_1780867 : CollatzResearch.WordTrace tailWord_1780867 prefixEnd_1780867 609627168487059388914965 := by
  unfold tailWord_1780867
  simp only [CollatzResearch.WordTrace]
  refine ⟨64953555639230481714260855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43302370426153654476173903 64953555639230481714260855)
  ·
    refine ⟨97430333458845722571391283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64953555639230481714260855 97430333458845722571391283)
    ·
      refine ⟨146145500188268583857086925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97430333458845722571391283 146145500188268583857086925)
      ·
        refine ⟨54804562570600718946407597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146145500188268583857086925 54804562570600718946407597)
        ·
          refine ⟨20551710963975269604902849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54804562570600718946407597 20551710963975269604902849)
          ·
            refine ⟨15413783222981452203677137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20551710963975269604902849 15413783222981452203677137)
            ·
              refine ⟨11560337417236089152757853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15413783222981452203677137 11560337417236089152757853)
              ·
                refine ⟨4335126531463533432284195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11560337417236089152757853 4335126531463533432284195)
                ·
                  refine ⟨6502689797195300148426293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4335126531463533432284195 6502689797195300148426293)
                  ·
                    refine ⟨609627168487059388914965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6502689797195300148426293 609627168487059388914965)
                    ·
                      rfl

theorem cell22_1780867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 5].length) (baseStart_1780867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780867 prefixEnd_1780867 := by exact prefixLift 1780867
  have htrace : WordTrace (prefixWord ++ tailWord_1780867) baseStart_1780867 baseEnd_1780867 := by
    simpa [prefixWord, tailWord_1780867, baseEnd_1780867] using wordTrace_append hprefix tailTrace_1780867
  have hstable : (prefixWord ++ tailWord_1780867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780867).length < 2 ^ (prefixWord ++ tailWord_1780867).sum := by decide
  have hdescent : baseEnd_1780867 < baseStart_1780867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780901 : List Nat := [1, 3, 1, 2, 1, 5, 2, 2, 2, 3]
def baseStart_1780901 : Nat := 118140960795 + 1780901 * 2 ^ 59
def prefixEnd_1780901 : Nat := 4983230072969 + 3 ^ 40 * 1780901 * 2
def baseEnd_1780901 : Nat := 609638807381894633564861

theorem tailTrace_1780901 : CollatzResearch.WordTrace tailWord_1780901 prefixEnd_1780901 609638807381894633564861 := by
  unfold tailWord_1780901
  simp only [CollatzResearch.WordTrace]
  refine ⟨64954795721107305520998557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43303197147404870347332371 64954795721107305520998557)
  ·
    refine ⟨24358048395415239570374459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64954795721107305520998557 24358048395415239570374459)
    ·
      refine ⟨36537072593122859355561689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24358048395415239570374459 36537072593122859355561689)
      ·
        refine ⟨27402804444842144516671267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36537072593122859355561689 27402804444842144516671267)
        ·
          refine ⟨41104206667263216775006901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27402804444842144516671267 41104206667263216775006901)
          ·
            refine ⟨3853519375055926572656897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41104206667263216775006901 3853519375055926572656897)
            ·
              refine ⟨2890139531291944929492673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3853519375055926572656897 2890139531291944929492673)
              ·
                refine ⟨2167604648468958697119505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2890139531291944929492673 2167604648468958697119505)
                ·
                  refine ⟨1625703486351719022839629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2167604648468958697119505 1625703486351719022839629)
                  ·
                    refine ⟨609638807381894633564861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1625703486351719022839629 609638807381894633564861)
                    ·
                      rfl

theorem cell22_1780901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_1780901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780901 prefixEnd_1780901 := by exact prefixLift 1780901
  have htrace : WordTrace (prefixWord ++ tailWord_1780901) baseStart_1780901 baseEnd_1780901 := by
    simpa [prefixWord, tailWord_1780901, baseEnd_1780901] using wordTrace_append hprefix tailTrace_1780901
  have hstable : (prefixWord ++ tailWord_1780901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780901).length < 2 ^ (prefixWord ++ tailWord_1780901).sum := by decide
  have hdescent : baseEnd_1780901 < baseStart_1780901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780903 : List Nat := [1, 1, 6, 2, 1, 1, 4, 2, 4]
def baseStart_1780903 : Nat := 118140960795 + 1780903 * 2 ^ 59
def prefixEnd_1780903 : Nat := 4983230072969 + 3 ^ 40 * 1780903 * 2
def baseEnd_1780903 : Nat := 203213164007589098338285

theorem tailTrace_1780903 : CollatzResearch.WordTrace tailWord_1780903 prefixEnd_1780903 203213164007589098338285 := by
  unfold tailWord_1780903
  simp only [CollatzResearch.WordTrace]
  refine ⟨64954868667100059862571363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43303245778066706575047575 64954868667100059862571363)
  ·
    refine ⟨97432303000650089793857045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64954868667100059862571363 97432303000650089793857045)
    ·
      refine ⟨4567139203155472959087049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97432303000650089793857045 4567139203155472959087049)
      ·
        refine ⟨3425354402366604719315287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4567139203155472959087049 3425354402366604719315287)
        ·
          refine ⟨5138031603549907078972931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3425354402366604719315287 5138031603549907078972931)
          ·
            refine ⟨7707047405324860618459397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5138031603549907078972931 7707047405324860618459397)
            ·
              refine ⟨1445071388498411365961137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7707047405324860618459397 1445071388498411365961137)
              ·
                refine ⟨1083803541373808524470853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1445071388498411365961137 1083803541373808524470853)
                ·
                  refine ⟨203213164007589098338285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1083803541373808524470853 203213164007589098338285)
                  ·
                    rfl

theorem cell22_1780903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 4].length) (baseStart_1780903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780903 prefixEnd_1780903 := by exact prefixLift 1780903
  have htrace : WordTrace (prefixWord ++ tailWord_1780903) baseStart_1780903 baseEnd_1780903 := by
    simpa [prefixWord, tailWord_1780903, baseEnd_1780903] using wordTrace_append hprefix tailTrace_1780903
  have hstable : (prefixWord ++ tailWord_1780903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780903).length < 2 ^ (prefixWord ++ tailWord_1780903).sum := by decide
  have hdescent : baseEnd_1780903 < baseStart_1780903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780914 : List Nat := [3, 2, 1, 1, 1, 6, 1, 7]
def baseStart_1780914 : Nat := 118140960795 + 1780914 * 2 ^ 59
def prefixEnd_1780914 : Nat := 4983230072969 + 3 ^ 40 * 1780914 * 2
def baseEnd_1780914 : Nat := 67738139727507436998869

theorem tailTrace_1780914 : CollatzResearch.WordTrace tailWord_1780914 prefixEnd_1780914 67738139727507436998869 := by
  unfold tailWord_1780914
  simp only [CollatzResearch.WordTrace]
  refine ⟨16238817467515052185305449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43303513246706805827481197 16238817467515052185305449)
  ·
    refine ⟨12179113100636289138979087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16238817467515052185305449 12179113100636289138979087)
    ·
      refine ⟨18268669650954433708468631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12179113100636289138979087 18268669650954433708468631)
      ·
        refine ⟨27403004476431650562702947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18268669650954433708468631 27403004476431650562702947)
        ·
          refine ⟨41104506714647475844054421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27403004476431650562702947 41104506714647475844054421)
          ·
            refine ⟨1926773752249100430190051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41104506714647475844054421 1926773752249100430190051)
            ·
              refine ⟨2890160628373650645285077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1926773752249100430190051 2890160628373650645285077)
              ·
                refine ⟨67738139727507436998869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2890160628373650645285077 67738139727507436998869)
                ·
                  rfl

theorem cell22_1780914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 7].length) (baseStart_1780914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780914 prefixEnd_1780914 := by exact prefixLift 1780914
  have htrace : WordTrace (prefixWord ++ tailWord_1780914) baseStart_1780914 baseEnd_1780914 := by
    simpa [prefixWord, tailWord_1780914, baseEnd_1780914] using wordTrace_append hprefix tailTrace_1780914
  have hstable : (prefixWord ++ tailWord_1780914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780914).length < 2 ^ (prefixWord ++ tailWord_1780914).sum := by decide
  have hdescent : baseEnd_1780914 < baseStart_1780914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780959 : List Nat := [1, 1, 2, 3, 2, 1, 5, 2, 5]
def baseStart_1780959 : Nat := 118140960795 + 1780959 * 2 ^ 59
def prefixEnd_1780959 : Nat := 4983230072969 + 3 ^ 40 * 1780959 * 2
def baseEnd_1780959 : Nat := 203219553989067271871561

theorem tailTrace_1780959 : CollatzResearch.WordTrace tailWord_1780959 prefixEnd_1780959 203219553989067271871561 := by
  unfold tailWord_1780959
  simp only [CollatzResearch.WordTrace]
  refine ⟨64956911154897181426609931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43304607436598120951073287 64956911154897181426609931)
  ·
    refine ⟨97435366732345772139914897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64956911154897181426609931 97435366732345772139914897)
    ·
      refine ⟨73076525049259329104936173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97435366732345772139914897 73076525049259329104936173)
      ·
        refine ⟨27403696893472248414351065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73076525049259329104936173 27403696893472248414351065)
        ·
          refine ⟨20552772670104186310763299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27403696893472248414351065 20552772670104186310763299)
          ·
            refine ⟨30829159005156279466144949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20552772670104186310763299 30829159005156279466144949)
            ·
              refine ⟨2890233656733401199951089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30829159005156279466144949 2890233656733401199951089)
              ·
                refine ⟨2167675242550050899963317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2890233656733401199951089 2167675242550050899963317)
                ·
                  refine ⟨203219553989067271871561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2167675242550050899963317 203219553989067271871561)
                  ·
                    rfl

theorem cell22_1780959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 5].length) (baseStart_1780959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780959 prefixEnd_1780959 := by exact prefixLift 1780959
  have htrace : WordTrace (prefixWord ++ tailWord_1780959) baseStart_1780959 baseEnd_1780959 := by
    simpa [prefixWord, tailWord_1780959, baseEnd_1780959] using wordTrace_append hprefix tailTrace_1780959
  have hstable : (prefixWord ++ tailWord_1780959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780959).length < 2 ^ (prefixWord ++ tailWord_1780959).sum := by decide
  have hdescent : baseEnd_1780959 < baseStart_1780959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780974 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1780974 : Nat := 118140960795 + 1780974 * 2 ^ 59
def prefixEnd_1780974 : Nat := 4983230072969 + 3 ^ 40 * 1780974 * 2
def baseEnd_1780974 : Nat := 609663796773746776489637

theorem tailTrace_1780974 : CollatzResearch.WordTrace tailWord_1780974 prefixEnd_1780974 609663796773746776489637 := by
  unfold tailWord_1780974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8119682281230354873550747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43304972166561892658937317 8119682281230354873550747)
  ·
    refine ⟨12179523421845532310326121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8119682281230354873550747 12179523421845532310326121)
    ·
      refine ⟨9134642566384149232744591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12179523421845532310326121 9134642566384149232744591)
      ·
        refine ⟨13701963849576223849116887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9134642566384149232744591 13701963849576223849116887)
        ·
          refine ⟨20552945774364335773675331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13701963849576223849116887 20552945774364335773675331)
          ·
            refine ⟨30829418661546503660512997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20552945774364335773675331 30829418661546503660512997)
            ·
              refine ⟨5780515999039969436346187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30829418661546503660512997 5780515999039969436346187)
              ·
                refine ⟨8670773998559954154519281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5780515999039969436346187 8670773998559954154519281)
                ·
                  refine ⟨6503080498919965615889461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8670773998559954154519281 6503080498919965615889461)
                  ·
                    refine ⟨609663796773746776489637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6503080498919965615889461 609663796773746776489637)
                    ·
                      rfl

theorem cell22_1780974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1780974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1780974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1780974 prefixEnd_1780974 := by exact prefixLift 1780974
  have htrace : WordTrace (prefixWord ++ tailWord_1780974) baseStart_1780974 baseEnd_1780974 := by
    simpa [prefixWord, tailWord_1780974, baseEnd_1780974] using wordTrace_append hprefix tailTrace_1780974
  have hstable : (prefixWord ++ tailWord_1780974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780974).length < 2 ^ (prefixWord ++ tailWord_1780974).sum := by decide
  have hdescent : baseEnd_1780974 < baseStart_1780974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781006 : List Nat := [4, 1, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_1781006 : Nat := 118140960795 + 1781006 * 2 ^ 59
def prefixEnd_1781006 : Nat := 4983230072969 + 3 ^ 40 * 1781006 * 2
def baseEnd_1781006 : Nat := 609674751027709359689539

theorem tailTrace_1781006 : CollatzResearch.WordTrace tailWord_1781006 prefixEnd_1781006 609674751027709359689539 := by
  unfold tailWord_1781006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8119828173215863556696359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43305750257151272302380581 8119828173215863556696359)
  ·
    refine ⟨12179742259823795335044539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8119828173215863556696359 12179742259823795335044539)
    ·
      refine ⟨18269613389735693002566809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12179742259823795335044539 18269613389735693002566809)
      ·
        refine ⟨13702210042301769751925107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18269613389735693002566809 13702210042301769751925107)
        ·
          refine ⟨20553315063452654627887661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13702210042301769751925107 20553315063452654627887661)
          ·
            refine ⟨7707493148794745485457873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20553315063452654627887661 7707493148794745485457873)
            ·
              refine ⟨5780619861596059114093405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7707493148794745485457873 5780619861596059114093405)
              ·
                refine ⟨2167732448098522167785027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5780619861596059114093405 2167732448098522167785027)
                ·
                  refine ⟨3251598672147783251677541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167732448098522167785027 3251598672147783251677541)
                  ·
                    refine ⟨609674751027709359689539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3251598672147783251677541 609674751027709359689539)
                    ·
                      rfl

theorem cell22_1781006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_1781006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781006 prefixEnd_1781006 := by exact prefixLift 1781006
  have htrace : WordTrace (prefixWord ++ tailWord_1781006) baseStart_1781006 baseEnd_1781006 := by
    simpa [prefixWord, tailWord_1781006, baseEnd_1781006] using wordTrace_append hprefix tailTrace_1781006
  have hstable : (prefixWord ++ tailWord_1781006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781006).length < 2 ^ (prefixWord ++ tailWord_1781006).sum := by decide
  have hdescent : baseEnd_1781006 < baseStart_1781006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781017 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 2, 10]
def baseStart_1781017 : Nat := 118140960795 + 1781017 * 2 ^ 59
def prefixEnd_1781017 : Nat := 4983230072969 + 3 ^ 40 * 1781017 * 2
def baseEnd_1781017 : Nat := 609678516552508997664505

theorem tailTrace_1781017 : CollatzResearch.WordTrace tailWord_1781017 prefixEnd_1781017 609678516552508997664505 := by
  unfold tailWord_1781017
  simp only [CollatzResearch.WordTrace]
  refine ⟨64959026588687057332221305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43306017725791371554814203 64959026588687057332221305)
  ·
    refine ⟨48719269941515292999165979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64959026588687057332221305 48719269941515292999165979)
    ·
      refine ⟨73078904912272939498748969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48719269941515292999165979 73078904912272939498748969)
      ·
        refine ⟨54809178684204704624061727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73078904912272939498748969 54809178684204704624061727)
        ·
          refine ⟨82213768026307056936092591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54809178684204704624061727 82213768026307056936092591)
          ·
            refine ⟨123320652039460585404138887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82213768026307056936092591 123320652039460585404138887)
            ·
              refine ⟨184980978059190878106208331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123320652039460585404138887 184980978059190878106208331)
              ·
                refine ⟨277471467088786317159312497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184980978059190878106208331 277471467088786317159312497)
                ·
                  refine ⟨208103600316589737869484373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277471467088786317159312497 208103600316589737869484373)
                  ·
                    refine ⟨609678516552508997664505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 208103600316589737869484373 609678516552508997664505)
                    ·
                      rfl

theorem cell22_1781017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_1781017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781017 prefixEnd_1781017 := by exact prefixLift 1781017
  have htrace : WordTrace (prefixWord ++ tailWord_1781017) baseStart_1781017 baseEnd_1781017 := by
    simpa [prefixWord, tailWord_1781017, baseEnd_1781017] using wordTrace_append hprefix tailTrace_1781017
  have hstable : (prefixWord ++ tailWord_1781017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781017).length < 2 ^ (prefixWord ++ tailWord_1781017).sum := by decide
  have hdescent : baseEnd_1781017 < baseStart_1781017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781021 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 6]
def baseStart_1781021 : Nat := 118140960795 + 1781021 * 2 ^ 59
def prefixEnd_1781021 : Nat := 4983230072969 + 3 ^ 40 * 1781021 * 2
def baseEnd_1781021 : Nat := 203226628611418106854831

theorem tailTrace_1781021 : CollatzResearch.WordTrace tailWord_1781021 prefixEnd_1781021 203226628611418106854831 := by
  unfold tailWord_1781021
  simp only [CollatzResearch.WordTrace]
  refine ⟨64959172480672566015366917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43306114987115044010244611 64959172480672566015366917)
  ·
    refine ⟨12179844840126106127881297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64959172480672566015366917 12179844840126106127881297)
    ·
      refine ⟨9134883630094579595910973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12179844840126106127881297 9134883630094579595910973)
      ·
        refine ⟨3425581361285467348466615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9134883630094579595910973 3425581361285467348466615)
        ·
          refine ⟨5138372041928201022699923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3425581361285467348466615 5138372041928201022699923)
          ·
            refine ⟨7707558062892301534049885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5138372041928201022699923 7707558062892301534049885)
            ·
              refine ⟨2890334273584613075268707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7707558062892301534049885 2890334273584613075268707)
              ·
                refine ⟨4335501410376919612903061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2890334273584613075268707 4335501410376919612903061)
                ·
                  refine ⟨203226628611418106854831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4335501410376919612903061 203226628611418106854831)
                  ·
                    rfl

theorem cell22_1781021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_1781021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781021 prefixEnd_1781021 := by exact prefixLift 1781021
  have htrace : WordTrace (prefixWord ++ tailWord_1781021) baseStart_1781021 baseEnd_1781021 := by
    simpa [prefixWord, tailWord_1781021, baseEnd_1781021] using wordTrace_append hprefix tailTrace_1781021
  have hstable : (prefixWord ++ tailWord_1781021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781021).length < 2 ^ (prefixWord ++ tailWord_1781021).sum := by decide
  have hdescent : baseEnd_1781021 < baseStart_1781021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781053 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 1, 5]
def baseStart_1781053 : Nat := 118140960795 + 1781053 * 2 ^ 59
def prefixEnd_1781053 : Nat := 4983230072969 + 3 ^ 40 * 1781053 * 2
def baseEnd_1781053 : Nat := 609690840088216903764395

theorem tailTrace_1781053 : CollatzResearch.WordTrace tailWord_1781053 prefixEnd_1781053 609690840088216903764395 := by
  unfold tailWord_1781053
  simp only [CollatzResearch.WordTrace]
  refine ⟨64960339616556635480531813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43306893077704423653687875 64960339616556635480531813)
  ·
    refine ⟨12180063678104369152599715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64960339616556635480531813 12180063678104369152599715)
    ·
      refine ⟨18270095517156553728899573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12180063678104369152599715 18270095517156553728899573)
      ·
        refine ⟨1712821454733426912084335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18270095517156553728899573 1712821454733426912084335)
        ·
          refine ⟨2569232182100140368126503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1712821454733426912084335 2569232182100140368126503)
          ·
            refine ⟨3853848273150210552189755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2569232182100140368126503 3853848273150210552189755)
            ·
              refine ⟨5780772409725315828284633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3853848273150210552189755 5780772409725315828284633)
              ·
                refine ⟨4335579307293986871213475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5780772409725315828284633 4335579307293986871213475)
                ·
                  refine ⟨6503368960940980306820213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4335579307293986871213475 6503368960940980306820213)
                  ·
                    refine ⟨609690840088216903764395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6503368960940980306820213 609690840088216903764395)
                    ·
                      rfl

theorem cell22_1781053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_1781053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781053 prefixEnd_1781053 := by exact prefixLift 1781053
  have htrace : WordTrace (prefixWord ++ tailWord_1781053) baseStart_1781053 baseEnd_1781053 := by
    simpa [prefixWord, tailWord_1781053, baseEnd_1781053] using wordTrace_append hprefix tailTrace_1781053
  have hstable : (prefixWord ++ tailWord_1781053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781053).length < 2 ^ (prefixWord ++ tailWord_1781053).sum := by decide
  have hdescent : baseEnd_1781053 < baseStart_1781053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781079 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 2, 6]
def baseStart_1781079 : Nat := 118140960795 + 1781079 * 2 ^ 59
def prefixEnd_1781079 : Nat := 4983230072969 + 3 ^ 40 * 1781079 * 2
def baseEnd_1781079 : Nat := 609699740419561502614315

theorem tailTrace_1781079 : CollatzResearch.WordTrace tailWord_1781079 prefixEnd_1781079 609699740419561502614315 := by
  unfold tailWord_1781079
  simp only [CollatzResearch.WordTrace]
  refine ⟨64961287914462441920978291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43307525276308294613985527 64961287914462441920978291)
  ·
    refine ⟨97441931871693662881467437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64961287914462441920978291 97441931871693662881467437)
    ·
      refine ⟨36540724451885123580550289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97441931871693662881467437 36540724451885123580550289)
      ·
        refine ⟨27405543338913842685412717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36540724451885123580550289 27405543338913842685412717)
        ·
          refine ⟨10277078752092691007029769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27405543338913842685412717 10277078752092691007029769)
          ·
            refine ⟨7707809064069518255272327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10277078752092691007029769 7707809064069518255272327)
            ·
              refine ⟨11561713596104277382908491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7707809064069518255272327 11561713596104277382908491)
              ·
                refine ⟨17342570394156416074362737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11561713596104277382908491 17342570394156416074362737)
                ·
                  refine ⟨13006927795617312055772053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17342570394156416074362737 13006927795617312055772053)
                  ·
                    refine ⟨609699740419561502614315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13006927795617312055772053 609699740419561502614315)
                    ·
                      rfl

theorem cell22_1781079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_1781079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781079 prefixEnd_1781079 := by exact prefixLift 1781079
  have htrace : WordTrace (prefixWord ++ tailWord_1781079) baseStart_1781079 baseEnd_1781079 := by
    simpa [prefixWord, tailWord_1781079, baseEnd_1781079] using wordTrace_append hprefix tailTrace_1781079
  have hstable : (prefixWord ++ tailWord_1781079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781079).length < 2 ^ (prefixWord ++ tailWord_1781079).sum := by decide
  have hdescent : baseEnd_1781079 < baseStart_1781079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781102 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 2, 4]
def baseStart_1781102 : Nat := 118140960795 + 1781102 * 2 ^ 59
def prefixEnd_1781102 : Nat := 4983230072969 + 3 ^ 40 * 1781102 * 2
def baseEnd_1781102 : Nat := 609707613789597109289245

theorem tailTrace_1781102 : CollatzResearch.WordTrace tailWord_1781102 prefixEnd_1781102 609707613789597109289245 := by
  unfold tailWord_1781102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8120265849172389606133195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43308084528919411232710373 8120265849172389606133195)
  ·
    refine ⟨12180398773758584409199793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8120265849172389606133195 12180398773758584409199793)
    ·
      refine ⟨9135299080318938306899845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12180398773758584409199793 9135299080318938306899845)
      ·
        refine ⟨1712868577559800932543721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9135299080318938306899845 1712868577559800932543721)
        ·
          refine ⟨1284651433169850699407791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1712868577559800932543721 1284651433169850699407791)
          ·
            refine ⟨1926977149754776049111687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284651433169850699407791 1926977149754776049111687)
            ·
              refine ⟨2890465724632164073667531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1926977149754776049111687 2890465724632164073667531)
              ·
                refine ⟨4335698586948246110501297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2890465724632164073667531 4335698586948246110501297)
                ·
                  refine ⟨3251773940211184582875973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4335698586948246110501297 3251773940211184582875973)
                  ·
                    refine ⟨609707613789597109289245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3251773940211184582875973 609707613789597109289245)
                    ·
                      rfl

theorem cell22_1781102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_1781102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781102 prefixEnd_1781102 := by exact prefixLift 1781102
  have htrace : WordTrace (prefixWord ++ tailWord_1781102) baseStart_1781102 baseEnd_1781102 := by
    simpa [prefixWord, tailWord_1781102, baseEnd_1781102] using wordTrace_append hprefix tailTrace_1781102
  have hstable : (prefixWord ++ tailWord_1781102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781102).length < 2 ^ (prefixWord ++ tailWord_1781102).sum := by decide
  have hdescent : baseEnd_1781102 < baseStart_1781102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781128 : List Nat := [2, 1, 3, 3, 1, 4, 1, 2, 5]
def baseStart_1781128 : Nat := 118140960795 + 1781128 * 2 ^ 59
def prefixEnd_1781128 : Nat := 4983230072969 + 3 ^ 40 * 1781128 * 2
def baseEnd_1781128 : Nat := 203238838040313902713055

theorem tailTrace_1781128 : CollatzResearch.WordTrace tailWord_1781128 prefixEnd_1781128 203238838040313902713055 := by
  unfold tailWord_1781128
  simp only [CollatzResearch.WordTrace]
  refine ⟨32481537545642461644756019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43308716727523282193008025 32481537545642461644756019)
  ·
    refine ⟨48722306318463692467134029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32481537545642461644756019 48722306318463692467134029)
    ·
      refine ⟨18270864869423884675175261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48722306318463692467134029 18270864869423884675175261)
      ·
        refine ⟨6851574326033956753190723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18270864869423884675175261 6851574326033956753190723)
        ·
          refine ⟨10277361489050935129786085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6851574326033956753190723 10277361489050935129786085)
          ·
            refine ⟨1927005279197050336834891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10277361489050935129786085 1927005279197050336834891)
            ·
              refine ⟨2890507918795575505252337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927005279197050336834891 2890507918795575505252337)
              ·
                refine ⟨2167880939096681628939253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2890507918795575505252337 2167880939096681628939253)
                ·
                  refine ⟨203238838040313902713055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2167880939096681628939253 203238838040313902713055)
                  ·
                    rfl

theorem cell22_1781128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 5].length) (baseStart_1781128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781128 prefixEnd_1781128 := by exact prefixLift 1781128
  have htrace : WordTrace (prefixWord ++ tailWord_1781128) baseStart_1781128 baseEnd_1781128 := by
    simpa [prefixWord, tailWord_1781128, baseEnd_1781128] using wordTrace_append hprefix tailTrace_1781128
  have hstable : (prefixWord ++ tailWord_1781128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781128).length < 2 ^ (prefixWord ++ tailWord_1781128).sum := by decide
  have hdescent : baseEnd_1781128 < baseStart_1781128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781184 : List Nat := [2, 1, 1, 2, 3, 1, 12]
def baseStart_1781184 : Nat := 118140960795 + 1781184 * 2 ^ 59
def prefixEnd_1781184 : Nat := 4983230072969 + 3 ^ 40 * 1781184 * 2
def baseEnd_1781184 : Nat := 22582803113532452916259

theorem tailTrace_1781184 : CollatzResearch.WordTrace tailWord_1781184 prefixEnd_1781184 22582803113532452916259 := by
  unfold tailWord_1781184
  simp only [CollatzResearch.WordTrace]
  refine ⟨32482558789541022426775303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43310078386054696569033737 32482558789541022426775303)
  ·
    refine ⟨48723838184311533640162955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32482558789541022426775303 48723838184311533640162955)
    ·
      refine ⟨73085757276467300460244433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48723838184311533640162955 73085757276467300460244433)
      ·
        refine ⟨54814317957350475345183325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73085757276467300460244433 54814317957350475345183325)
        ·
          refine ⟨20555369234006428254443747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54814317957350475345183325 20555369234006428254443747)
          ·
            refine ⟨30833053851009642381665621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20555369234006428254443747 30833053851009642381665621)
            ·
              refine ⟨22582803113532452916259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 30833053851009642381665621 22582803113532452916259)
              ·
                rfl

theorem cell22_1781184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 12].length) (baseStart_1781184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781184 prefixEnd_1781184 := by exact prefixLift 1781184
  have htrace : WordTrace (prefixWord ++ tailWord_1781184) baseStart_1781184 baseEnd_1781184 := by
    simpa [prefixWord, tailWord_1781184, baseEnd_1781184] using wordTrace_append hprefix tailTrace_1781184
  have hstable : (prefixWord ++ tailWord_1781184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781184).length < 2 ^ (prefixWord ++ tailWord_1781184).sum := by decide
  have hdescent : baseEnd_1781184 < baseStart_1781184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781340 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1781340 : Nat := 118140960795 + 1781340 * 2 ^ 59
def prefixEnd_1781340 : Nat := 4983230072969 + 3 ^ 40 * 1781340 * 2
def baseEnd_1781340 : Nat := 609789086053443821838515

theorem tailTrace_1781340 : CollatzResearch.WordTrace tailWord_1781340 prefixEnd_1781340 609789086053443821838515 := by
  unfold tailWord_1781340
  simp only [CollatzResearch.WordTrace]
  refine ⟨32485403683258441748114737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43313871577677922330819649 32485403683258441748114737)
  ·
    refine ⟨24364052762443831311086053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32485403683258441748114737 24364052762443831311086053)
    ·
      refine ⟨4568259892958218370828635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24364052762443831311086053 4568259892958218370828635)
      ·
        refine ⟨6852389839437327556242953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4568259892958218370828635 6852389839437327556242953)
        ·
          refine ⟨5139292379577995667182215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6852389839437327556242953 5139292379577995667182215)
          ·
            refine ⟨7708938569366993500773323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5139292379577995667182215 7708938569366993500773323)
            ·
              refine ⟨11563407854050490251159985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7708938569366993500773323 11563407854050490251159985)
              ·
                refine ⟨8672555890537867688369989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11563407854050490251159985 8672555890537867688369989)
                ·
                  refine ⟨1626104229475850191569373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8672555890537867688369989 1626104229475850191569373)
                  ·
                    refine ⟨609789086053443821838515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1626104229475850191569373 609789086053443821838515)
                    ·
                      rfl

theorem cell22_1781340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1781340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781340 prefixEnd_1781340 := by exact prefixLift 1781340
  have htrace : WordTrace (prefixWord ++ tailWord_1781340) baseStart_1781340 baseEnd_1781340 := by
    simpa [prefixWord, tailWord_1781340, baseEnd_1781340] using wordTrace_append hprefix tailTrace_1781340
  have hstable : (prefixWord ++ tailWord_1781340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781340).length < 2 ^ (prefixWord ++ tailWord_1781340).sum := by decide
  have hdescent : baseEnd_1781340 < baseStart_1781340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781505 : List Nat := [1, 2, 4, 1, 1, 1, 6, 6]
def baseStart_1781505 : Nat := 118140960795 + 1781505 * 2 ^ 59
def prefixEnd_1781505 : Nat := 4983230072969 + 3 ^ 40 * 1781505 * 2
def baseEnd_1781505 : Nat := 67760618769493154607001

theorem tailTrace_1781505 : CollatzResearch.WordTrace tailWord_1781505 prefixEnd_1781505 67760618769493154607001 := by
  unfold tailWord_1781505
  simp only [CollatzResearch.WordTrace]
  refine ⟨64976825410919116675985969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43317883607279411117323979 64976825410919116675985969)
  ·
    refine ⟨48732619058189337506989477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64976825410919116675985969 48732619058189337506989477)
    ·
      refine ⟨9137366073410500782560527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48732619058189337506989477 9137366073410500782560527)
      ·
        refine ⟨13706049110115751173840791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9137366073410500782560527 13706049110115751173840791)
        ·
          refine ⟨20559073665173626760761187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13706049110115751173840791 20559073665173626760761187)
          ·
            refine ⟨30838610497760440141141781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20559073665173626760761187 30838610497760440141141781)
            ·
              refine ⟨1445559867082520631616021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30838610497760440141141781 1445559867082520631616021)
              ·
                refine ⟨67760618769493154607001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1445559867082520631616021 67760618769493154607001)
                ·
                  rfl

theorem cell22_1781505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 6].length) (baseStart_1781505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781505 prefixEnd_1781505 := by exact prefixLift 1781505
  have htrace : WordTrace (prefixWord ++ tailWord_1781505) baseStart_1781505 baseEnd_1781505 := by
    simpa [prefixWord, tailWord_1781505, baseEnd_1781505] using wordTrace_append hprefix tailTrace_1781505
  have hstable : (prefixWord ++ tailWord_1781505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781505).length < 2 ^ (prefixWord ++ tailWord_1781505).sum := by decide
  have hdescent : baseEnd_1781505 < baseStart_1781505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781511 : List Nat := [1, 1, 4, 4, 3, 1, 1, 3, 4]
def baseStart_1781511 : Nat := 118140960795 + 1781511 * 2 ^ 59
def prefixEnd_1781511 : Nat := 4983230072969 + 3 ^ 40 * 1781511 * 2
def baseEnd_1781511 : Nat := 203282540949352125270997

theorem tailTrace_1781511 : CollatzResearch.WordTrace tailWord_1781511 prefixEnd_1781511 203282540949352125270997 := by
  unfold tailWord_1781511
  simp only [CollatzResearch.WordTrace]
  refine ⟨64977044248897379700704387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43318029499264919800469591 64977044248897379700704387)
  ·
    refine ⟨97465566373346069551056581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64977044248897379700704387 97465566373346069551056581)
    ·
      refine ⟨18274793695002388040823109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97465566373346069551056581 18274793695002388040823109)
      ·
        refine ⟨3426523817812947757654333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18274793695002388040823109 3426523817812947757654333)
        ·
          refine ⟨1284946431679855409120375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3426523817812947757654333 1284946431679855409120375)
          ·
            refine ⟨1927419647519783113680563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284946431679855409120375 1927419647519783113680563)
            ·
              refine ⟨2891129471279674670520845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927419647519783113680563 2891129471279674670520845)
              ·
                refine ⟨1084173551729878001445317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2891129471279674670520845 1084173551729878001445317)
                ·
                  refine ⟨203282540949352125270997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1084173551729878001445317 203282540949352125270997)
                  ·
                    rfl

theorem cell22_1781511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 4].length) (baseStart_1781511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781511 prefixEnd_1781511 := by exact prefixLift 1781511
  have htrace : WordTrace (prefixWord ++ tailWord_1781511) baseStart_1781511 baseEnd_1781511 := by
    simpa [prefixWord, tailWord_1781511, baseEnd_1781511] using wordTrace_append hprefix tailTrace_1781511
  have hstable : (prefixWord ++ tailWord_1781511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781511).length < 2 ^ (prefixWord ++ tailWord_1781511).sum := by decide
  have hdescent : baseEnd_1781511 < baseStart_1781511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781522 : List Nat := [3, 2, 4, 1, 1, 3, 8]
def baseStart_1781522 : Nat := 118140960795 + 1781522 * 2 ^ 59
def prefixEnd_1781522 : Nat := 4983230072969 + 3 ^ 40 * 1781522 * 2
def baseEnd_1781522 : Nat := 22587088458253926436591

theorem tailTrace_1781522 : CollatzResearch.WordTrace tailWord_1781522 prefixEnd_1781522 22587088458253926436591 := by
  unfold tailWord_1781522
  simp only [CollatzResearch.WordTrace]
  refine ⟨16244361362964382144838705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43318296967905019052903213 16244361362964382144838705)
  ·
    refine ⟨12183271022223286608629029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16244361362964382144838705 12183271022223286608629029)
    ·
      refine ⟨2284363316666866239117943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12183271022223286608629029 2284363316666866239117943)
      ·
        refine ⟨3426544975000299358676915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2284363316666866239117943 3426544975000299358676915)
        ·
          refine ⟨5139817462500449038015373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3426544975000299358676915 5139817462500449038015373)
          ·
            refine ⟨1927431548437668389255765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5139817462500449038015373 1927431548437668389255765)
            ·
              refine ⟨22587088458253926436591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1927431548437668389255765 22587088458253926436591)
              ·
                rfl

theorem cell22_1781522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 8].length) (baseStart_1781522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781522 prefixEnd_1781522 := by exact prefixLift 1781522
  have htrace : WordTrace (prefixWord ++ tailWord_1781522) baseStart_1781522 baseEnd_1781522 := by
    simpa [prefixWord, tailWord_1781522, baseEnd_1781522] using wordTrace_append hprefix tailTrace_1781522
  have hstable : (prefixWord ++ tailWord_1781522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781522).length < 2 ^ (prefixWord ++ tailWord_1781522).sum := by decide
  have hdescent : baseEnd_1781522 < baseStart_1781522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781537 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 3, 3]
def baseStart_1781537 : Nat := 118140960795 + 1781537 * 2 ^ 59
def prefixEnd_1781537 : Nat := 4983230072969 + 3 ^ 40 * 1781537 * 2
def baseEnd_1781537 : Nat := 609856523179400974662911

theorem tailTrace_1781537 : CollatzResearch.WordTrace tailWord_1781537 prefixEnd_1781537 609856523179400974662911 := by
  unfold tailWord_1781537
  simp only [CollatzResearch.WordTrace]
  refine ⟨64977992546803186141150865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43318661697868790760767243 64977992546803186141150865)
  ·
    refine ⟨48733494410102389605863149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64977992546803186141150865 48733494410102389605863149)
    ·
      refine ⟨18275060403788396102198681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48733494410102389605863149 18275060403788396102198681)
      ·
        refine ⟨13706295302841297076649011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18275060403788396102198681 13706295302841297076649011)
        ·
          refine ⟨20559442954261945614973517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13706295302841297076649011 20559442954261945614973517)
          ·
            refine ⟨7709791107848229605615069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20559442954261945614973517 7709791107848229605615069)
            ·
              refine ⟨2891171665443086102105651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7709791107848229605615069 2891171665443086102105651)
              ·
                refine ⟨4336757498164629153158477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2891171665443086102105651 4336757498164629153158477)
                ·
                  refine ⟨1626284061811735932434429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4336757498164629153158477 1626284061811735932434429)
                  ·
                    refine ⟨609856523179400974662911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1626284061811735932434429 609856523179400974662911)
                    ·
                      rfl

theorem cell22_1781537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_1781537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781537 prefixEnd_1781537 := by exact prefixLift 1781537
  have htrace : WordTrace (prefixWord ++ tailWord_1781537) baseStart_1781537 baseEnd_1781537 := by
    simpa [prefixWord, tailWord_1781537, baseEnd_1781537] using wordTrace_append hprefix tailTrace_1781537
  have hstable : (prefixWord ++ tailWord_1781537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781537).length < 2 ^ (prefixWord ++ tailWord_1781537).sum := by decide
  have hdescent : baseEnd_1781537 < baseStart_1781537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781588 : List Nat := [2, 4, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_1781588 : Nat := 118140960795 + 1781588 * 2 ^ 59
def prefixEnd_1781588 : Nat := 4983230072969 + 3 ^ 40 * 1781588 * 2
def baseEnd_1781588 : Nat := 609873981521653841637755

theorem tailTrace_1781588 : CollatzResearch.WordTrace tailWord_1781588 prefixEnd_1781588 609873981521653841637755 := by
  unfold tailWord_1781588
  simp only [CollatzResearch.WordTrace]
  refine ⟨32489926334809210925628709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43319901779745614567504945 32489926334809210925628709)
  ·
    refine ⟨6091861187776727048555383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32489926334809210925628709 6091861187776727048555383)
    ·
      refine ⟨9137791781665090572833075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6091861187776727048555383 9137791781665090572833075)
      ·
        refine ⟨13706687672497635859249613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9137791781665090572833075 13706687672497635859249613)
        ·
          refine ⟨5140007877186613447218605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13706687672497635859249613 5140007877186613447218605)
          ·
            refine ⟨1927502953944980042706977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5140007877186613447218605 1927502953944980042706977)
            ·
              refine ⟨1445627215458735032030233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1927502953944980042706977 1445627215458735032030233)
              ·
                refine ⟨1084220411594051274022675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1445627215458735032030233 1084220411594051274022675)
                ·
                  refine ⟨1626330617391076911034013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1084220411594051274022675 1626330617391076911034013)
                  ·
                    refine ⟨609873981521653841637755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1626330617391076911034013 609873981521653841637755)
                    ·
                      rfl

theorem cell22_1781588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_1781588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781588 prefixEnd_1781588 := by exact prefixLift 1781588
  have htrace : WordTrace (prefixWord ++ tailWord_1781588) baseStart_1781588 baseEnd_1781588 := by
    simpa [prefixWord, tailWord_1781588, baseEnd_1781588] using wordTrace_append hprefix tailTrace_1781588
  have hstable : (prefixWord ++ tailWord_1781588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781588).length < 2 ^ (prefixWord ++ tailWord_1781588).sum := by decide
  have hdescent : baseEnd_1781588 < baseStart_1781588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781625 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 1, 6]
def baseStart_1781625 : Nat := 118140960795 + 1781625 * 2 ^ 59
def prefixEnd_1781625 : Nat := 4983230072969 + 3 ^ 40 * 1781625 * 2
def baseEnd_1781625 : Nat := 609886647377798078462641

theorem tailTrace_1781625 : CollatzResearch.WordTrace tailWord_1781625 prefixEnd_1781625 609886647377798078462641 := by
  unfold tailWord_1781625
  simp only [CollatzResearch.WordTrace]
  refine ⟨64981202170484377170354329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43320801446989584780236219 64981202170484377170354329)
  ·
    refine ⟨48735901627863282877765747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64981202170484377170354329 48735901627863282877765747)
    ·
      refine ⟨73103852441794924316648621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48735901627863282877765747 73103852441794924316648621)
      ·
        refine ⟨27413944665673096618743233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73103852441794924316648621 27413944665673096618743233)
        ·
          refine ⟨20560458499254822464057425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27413944665673096618743233 20560458499254822464057425)
          ·
            refine ⟨15420343874441116848043069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20560458499254822464057425 15420343874441116848043069)
            ·
              refine ⟨5782628952915418818016151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15420343874441116848043069 5782628952915418818016151)
              ·
                refine ⟨8673943429373128227024227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5782628952915418818016151 8673943429373128227024227)
                ·
                  refine ⟨13010915144059692340536341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8673943429373128227024227 13010915144059692340536341)
                  ·
                    refine ⟨609886647377798078462641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13010915144059692340536341 609886647377798078462641)
                    ·
                      rfl

theorem cell22_1781625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_1781625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781625 prefixEnd_1781625 := by exact prefixLift 1781625
  have htrace : WordTrace (prefixWord ++ tailWord_1781625) baseStart_1781625 baseEnd_1781625 := by
    simpa [prefixWord, tailWord_1781625, baseEnd_1781625] using wordTrace_append hprefix tailTrace_1781625
  have hstable : (prefixWord ++ tailWord_1781625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781625).length < 2 ^ (prefixWord ++ tailWord_1781625).sum := by decide
  have hdescent : baseEnd_1781625 < baseStart_1781625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781661 : List Nat := [1, 4, 2, 1, 2, 3, 3, 1, 2, 3]
def baseStart_1781661 : Nat := 118140960795 + 1781661 * 2 ^ 59
def prefixEnd_1781661 : Nat := 4983230072969 + 3 ^ 40 * 1781661 * 2
def baseEnd_1781661 : Nat := 609898970913505984562531

theorem tailTrace_1781661 : CollatzResearch.WordTrace tailWord_1781661 prefixEnd_1781661 609898970913505984562531 := by
  unfold tailWord_1781661
  simp only [CollatzResearch.WordTrace]
  refine ⟨64982515198353955318664837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43321676798902636879109891 64982515198353955318664837)
  ·
    refine ⟨12184221599691366622249657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64982515198353955318664837 12184221599691366622249657)
    ·
      refine ⟨9138166199768524966687243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12184221599691366622249657 9138166199768524966687243)
      ·
        refine ⟨13707249299652787450030865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9138166199768524966687243 13707249299652787450030865)
        ·
          refine ⟨10280436974739590587523149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13707249299652787450030865 10280436974739590587523149)
          ·
            refine ⟨3855163865527346470321181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10280436974739590587523149 3855163865527346470321181)
            ·
              refine ⟨1445686449572754926370443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3855163865527346470321181 1445686449572754926370443)
              ·
                refine ⟨2168529674359132389555665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1445686449572754926370443 2168529674359132389555665)
                ·
                  refine ⟨1626397255769349292166749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2168529674359132389555665 1626397255769349292166749)
                  ·
                    refine ⟨609898970913505984562531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1626397255769349292166749 609898970913505984562531)
                    ·
                      rfl

theorem cell22_1781661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_1781661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781661 prefixEnd_1781661 := by exact prefixLift 1781661
  have htrace : WordTrace (prefixWord ++ tailWord_1781661) baseStart_1781661 baseEnd_1781661 := by
    simpa [prefixWord, tailWord_1781661, baseEnd_1781661] using wordTrace_append hprefix tailTrace_1781661
  have hstable : (prefixWord ++ tailWord_1781661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781661).length < 2 ^ (prefixWord ++ tailWord_1781661).sum := by decide
  have hdescent : baseEnd_1781661 < baseStart_1781661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781732 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_1781732 : Nat := 118140960795 + 1781732 * 2 ^ 59
def prefixEnd_1781732 : Nat := 4983230072969 + 3 ^ 40 * 1781732 * 2
def baseEnd_1781732 : Nat := 609923275664485466037313

theorem tailTrace_1781732 : CollatzResearch.WordTrace tailWord_1781732 prefixEnd_1781732 609923275664485466037313 := by
  unfold tailWord_1781732
  simp only [CollatzResearch.WordTrace]
  refine ⟨32492552390548367222249725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43323403187397822962999633 32492552390548367222249725)
  ·
    refine ⟨12184707146455637708343647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32492552390548367222249725 12184707146455637708343647)
    ·
      refine ⟨18277060719683456562515471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12184707146455637708343647 18277060719683456562515471)
      ·
        refine ⟨27415591079525184843773207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18277060719683456562515471 27415591079525184843773207)
        ·
          refine ⟨41123386619287777265659811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27415591079525184843773207 41123386619287777265659811)
          ·
            refine ⟨61685079928931665898489717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41123386619287777265659811 61685079928931665898489717)
            ·
              refine ⟨5782976243337343677983411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61685079928931665898489717 5782976243337343677983411)
              ·
                refine ⟨8674464365006015516975117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5782976243337343677983411 8674464365006015516975117)
                ·
                  refine ⟨3252924136877255818865669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8674464365006015516975117 3252924136877255818865669)
                  ·
                    refine ⟨609923275664485466037313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3252924136877255818865669 609923275664485466037313)
                    ·
                      rfl

theorem cell22_1781732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_1781732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781732 prefixEnd_1781732 := by exact prefixLift 1781732
  have htrace : WordTrace (prefixWord ++ tailWord_1781732) baseStart_1781732 baseEnd_1781732 := by
    simpa [prefixWord, tailWord_1781732, baseEnd_1781732] using wordTrace_append hprefix tailTrace_1781732
  have hstable : (prefixWord ++ tailWord_1781732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781732).length < 2 ^ (prefixWord ++ tailWord_1781732).sum := by decide
  have hdescent : baseEnd_1781732 < baseStart_1781732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781779 : List Nat := [1, 1, 1, 2, 1, 4, 4, 3, 2, 3]
def baseStart_1781779 : Nat := 118140960795 + 1781779 * 2 ^ 59
def prefixEnd_1781779 : Nat := 4983230072969 + 3 ^ 40 * 1781779 * 2
def baseEnd_1781779 : Nat := 609939364724993010112169

theorem tailTrace_1781779 : CollatzResearch.WordTrace tailWord_1781779 prefixEnd_1781779 609939364724993010112169 := by
  unfold tailWord_1781779
  simp only [CollatzResearch.WordTrace]
  refine ⟨64986819011926461471460391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43324546007950974314306927 64986819011926461471460391)
  ·
    refine ⟨97480228517889692207190587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64986819011926461471460391 97480228517889692207190587)
    ·
      refine ⟨146220342776834538310785881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97480228517889692207190587 146220342776834538310785881)
      ·
        refine ⟨109665257082625903733089411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146220342776834538310785881 109665257082625903733089411)
        ·
          refine ⟨164497885623938855599634117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109665257082625903733089411 164497885623938855599634117)
          ·
            refine ⟨30843353554488535424931397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164497885623938855599634117 30843353554488535424931397)
            ·
              refine ⟨5783128791466600392174637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30843353554488535424931397 5783128791466600392174637)
              ·
                refine ⟨2168673296799975147065489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5783128791466600392174637 2168673296799975147065489)
                ·
                  refine ⟨1626504972599981360299117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2168673296799975147065489 1626504972599981360299117)
                  ·
                    refine ⟨609939364724993010112169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1626504972599981360299117 609939364724993010112169)
                    ·
                      rfl

theorem cell22_1781779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 3].length) (baseStart_1781779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781779 prefixEnd_1781779 := by exact prefixLift 1781779
  have htrace : WordTrace (prefixWord ++ tailWord_1781779) baseStart_1781779 baseEnd_1781779 := by
    simpa [prefixWord, tailWord_1781779, baseEnd_1781779] using wordTrace_append hprefix tailTrace_1781779
  have hstable : (prefixWord ++ tailWord_1781779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781779).length < 2 ^ (prefixWord ++ tailWord_1781779).sum := by decide
  have hdescent : baseEnd_1781779 < baseStart_1781779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781800 : List Nat := [2, 1, 5, 3, 1, 2, 2, 1, 1, 4]
def baseStart_1781800 : Nat := 118140960795 + 1781800 * 2 ^ 59
def prefixEnd_1781800 : Nat := 4983230072969 + 3 ^ 40 * 1781800 * 2
def baseEnd_1781800 : Nat := 609946553454155955337105

theorem tailTrace_1781800 : CollatzResearch.WordTrace tailWord_1781800 prefixEnd_1781800 609946553454155955337105 := by
  unfold tailWord_1781800
  simp only [CollatzResearch.WordTrace]
  refine ⟨32493792472425191028987427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43325056629900254705316569 32493792472425191028987427)
  ·
    refine ⟨48740688708637786543481141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32493792472425191028987427 48740688708637786543481141)
    ·
      refine ⟨4569439566434792488451357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48740688708637786543481141 4569439566434792488451357)
      ·
        refine ⟨1713539837413047183169259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4569439566434792488451357 1713539837413047183169259)
        ·
          refine ⟨2570309756119570774753889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1713539837413047183169259 2570309756119570774753889)
          ·
            refine ⟨1927732317089678081065417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2570309756119570774753889 1927732317089678081065417)
            ·
              refine ⟨1445799237817258560799063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1927732317089678081065417 1445799237817258560799063)
              ·
                refine ⟨2168698856725887841198595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1445799237817258560799063 2168698856725887841198595)
                ·
                  refine ⟨3253048285088831761797893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2168698856725887841198595 3253048285088831761797893)
                  ·
                    refine ⟨609946553454155955337105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3253048285088831761797893 609946553454155955337105)
                    ·
                      rfl

theorem cell22_1781800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_1781800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781800 prefixEnd_1781800 := by exact prefixLift 1781800
  have htrace : WordTrace (prefixWord ++ tailWord_1781800) baseStart_1781800 baseEnd_1781800 := by
    simpa [prefixWord, tailWord_1781800, baseEnd_1781800] using wordTrace_append hprefix tailTrace_1781800
  have hstable : (prefixWord ++ tailWord_1781800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781800).length < 2 ^ (prefixWord ++ tailWord_1781800).sum := by decide
  have hdescent : baseEnd_1781800 < baseStart_1781800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781824 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 3, 3]
def baseStart_1781824 : Nat := 118140960795 + 1781824 * 2 ^ 59
def prefixEnd_1781824 : Nat := 4983230072969 + 3 ^ 40 * 1781824 * 2
def baseEnd_1781824 : Nat := 609954769144627892737031

theorem tailTrace_1781824 : CollatzResearch.WordTrace tailWord_1781824 prefixEnd_1781824 609954769144627892737031 := by
  unfold tailWord_1781824
  simp only [CollatzResearch.WordTrace]
  refine ⟨32494230148381717078424263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43325640197842289437899017 32494230148381717078424263)
  ·
    refine ⟨48741345222572575617636395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32494230148381717078424263 48741345222572575617636395)
    ·
      refine ⟨73112017833858863426454593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48741345222572575617636395 73112017833858863426454593)
      ·
        refine ⟨54834013375394147569840945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73112017833858863426454593 54834013375394147569840945)
        ·
          refine ⟨41125510031545610677380709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54834013375394147569840945 41125510031545610677380709)
          ·
            refine ⟨7711033130914802002008883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41125510031545610677380709 7711033130914802002008883)
            ·
              refine ⟨11566549696372203003013325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7711033130914802002008883 11566549696372203003013325)
              ·
                refine ⟨4337456136139576126129997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11566549696372203003013325 4337456136139576126129997)
                ·
                  refine ⟨1626546051052341047298749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4337456136139576126129997 1626546051052341047298749)
                  ·
                    refine ⟨609954769144627892737031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1626546051052341047298749 609954769144627892737031)
                    ·
                      rfl

theorem cell22_1781824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 3, 3].length) (baseStart_1781824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781824 prefixEnd_1781824 := by exact prefixLift 1781824
  have htrace : WordTrace (prefixWord ++ tailWord_1781824) baseStart_1781824 baseEnd_1781824 := by
    simpa [prefixWord, tailWord_1781824, baseEnd_1781824] using wordTrace_append hprefix tailTrace_1781824
  have hstable : (prefixWord ++ tailWord_1781824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781824).length < 2 ^ (prefixWord ++ tailWord_1781824).sum := by decide
  have hdescent : baseEnd_1781824 < baseStart_1781824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781830 : List Nat := [6, 1, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_1781830 : Nat := 118140960795 + 1781830 * 2 ^ 59
def prefixEnd_1781830 : Nat := 4983230072969 + 3 ^ 40 * 1781830 * 2
def baseEnd_1781830 : Nat := 609956823067245877087013

theorem tailTrace_1781830 : CollatzResearch.WordTrace tailWord_1781830 prefixEnd_1781830 609956823067245877087013 := by
  unfold tailWord_1781830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030896222960678036923967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43325786089827798121044629 2030896222960678036923967)
  ·
    refine ⟨3046344334441017055385951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2030896222960678036923967 3046344334441017055385951)
    ·
      refine ⟨4569516501661525583078927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3046344334441017055385951 4569516501661525583078927)
      ·
        refine ⟨6854274752492288374618391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4569516501661525583078927 6854274752492288374618391)
        ·
          refine ⟨10281412128738432561927587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6854274752492288374618391 10281412128738432561927587)
          ·
            refine ⟨15422118193107648842891381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10281412128738432561927587 15422118193107648842891381)
            ·
              refine ⟨1445823580603842079021067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15422118193107648842891381 1445823580603842079021067)
              ·
                refine ⟨2168735370905763118531601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1445823580603842079021067 2168735370905763118531601)
                ·
                  refine ⟨1626551528179322338898701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2168735370905763118531601 1626551528179322338898701)
                  ·
                    refine ⟨609956823067245877087013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1626551528179322338898701 609956823067245877087013)
                    ·
                      rfl

theorem cell22_1781830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_1781830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781830 prefixEnd_1781830 := by exact prefixLift 1781830
  have htrace : WordTrace (prefixWord ++ tailWord_1781830) baseStart_1781830 baseEnd_1781830 := by
    simpa [prefixWord, tailWord_1781830, baseEnd_1781830] using wordTrace_append hprefix tailTrace_1781830
  have hstable : (prefixWord ++ tailWord_1781830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781830).length < 2 ^ (prefixWord ++ tailWord_1781830).sum := by decide
  have hdescent : baseEnd_1781830 < baseStart_1781830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781916 : List Nat := [2, 2, 3, 2, 1, 1, 2, 5, 4]
def baseStart_1781916 : Nat := 118140960795 + 1781916 * 2 ^ 59
def prefixEnd_1781916 : Nat := 4983230072969 + 3 ^ 40 * 1781916 * 2
def baseEnd_1781916 : Nat := 203328754208256773145583

theorem tailTrace_1781916 : CollatzResearch.WordTrace tailWord_1781916 prefixEnd_1781916 203328754208256773145583 := by
  unfold tailWord_1781916
  simp only [CollatzResearch.WordTrace]
  refine ⟨32495907906215066934598801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43327877208286755912798401 32495907906215066934598801)
  ·
    refine ⟨24371930929661300200949101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32495907906215066934598801 24371930929661300200949101)
    ·
      refine ⟨9139474098622987575355913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24371930929661300200949101 9139474098622987575355913)
      ·
        refine ⟨6854605573967240681516935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9139474098622987575355913 6854605573967240681516935)
        ·
          refine ⟨10281908360950861022275403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6854605573967240681516935 10281908360950861022275403)
          ·
            refine ⟨15422862541426291533413105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10281908360950861022275403 15422862541426291533413105)
            ·
              refine ⟨11567146906069718650059829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15422862541426291533413105 11567146906069718650059829)
              ·
                refine ⟨1084420022444036123443109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11567146906069718650059829 1084420022444036123443109)
                ·
                  refine ⟨203328754208256773145583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1084420022444036123443109 203328754208256773145583)
                  ·
                    rfl

theorem cell22_1781916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_1781916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781916 prefixEnd_1781916 := by exact prefixLift 1781916
  have htrace : WordTrace (prefixWord ++ tailWord_1781916) baseStart_1781916 baseEnd_1781916 := by
    simpa [prefixWord, tailWord_1781916, baseEnd_1781916] using wordTrace_append hprefix tailTrace_1781916
  have hstable : (prefixWord ++ tailWord_1781916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781916).length < 2 ^ (prefixWord ++ tailWord_1781916).sum := by decide
  have hdescent : baseEnd_1781916 < baseStart_1781916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781933 : List Nat := [1, 5, 2, 1, 2, 2, 1, 4, 4]
def baseStart_1781933 : Nat := 118140960795 + 1781933 * 2 ^ 59
def prefixEnd_1781933 : Nat := 4983230072969 + 3 ^ 40 * 1781933 * 2
def baseEnd_1781933 : Nat := 203330694024062647253899

theorem tailTrace_1781933 : CollatzResearch.WordTrace tailWord_1781933 prefixEnd_1781933 203330694024062647253899 := by
  unfold tailWord_1781933
  simp only [CollatzResearch.WordTrace]
  refine ⟨64992435853368545772566453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43328290568912363848377635 64992435853368545772566453)
  ·
    refine ⟨6093040861253301166178105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64992435853368545772566453 6093040861253301166178105)
    ·
      refine ⟨4569780645939975874633579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6093040861253301166178105 4569780645939975874633579)
      ·
        refine ⟨6854670968909963811950369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4569780645939975874633579 6854670968909963811950369)
        ·
          refine ⟨5141003226682472858962777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6854670968909963811950369 5141003226682472858962777)
          ·
            refine ⟨3855752420011854644222083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5141003226682472858962777 3855752420011854644222083)
            ·
              refine ⟨5783628630017781966333125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3855752420011854644222083 5783628630017781966333125)
              ·
                refine ⟨1084430368128334118687461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5783628630017781966333125 1084430368128334118687461)
                ·
                  refine ⟨203330694024062647253899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1084430368128334118687461 203330694024062647253899)
                  ·
                    rfl

theorem cell22_1781933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_1781933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1781933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1781933 prefixEnd_1781933 := by exact prefixLift 1781933
  have htrace : WordTrace (prefixWord ++ tailWord_1781933) baseStart_1781933 baseEnd_1781933 := by
    simpa [prefixWord, tailWord_1781933, baseEnd_1781933] using wordTrace_append hprefix tailTrace_1781933
  have hstable : (prefixWord ++ tailWord_1781933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781933).length < 2 ^ (prefixWord ++ tailWord_1781933).sum := by decide
  have hdescent : baseEnd_1781933 < baseStart_1781933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782006 : List Nat := [5, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_1782006 : Nat := 118140960795 + 1782006 * 2 ^ 59
def prefixEnd_1782006 : Nat := 4983230072969 + 3 ^ 40 * 1782006 * 2
def baseEnd_1782006 : Nat := 203339023821346694895491

theorem tailTrace_1782006 : CollatzResearch.WordTrace tailWord_1782006 prefixEnd_1782006 203339023821346694895491 := by
  unfold tailWord_1782006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4062193648881504952498367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43330065588069386159982581 4062193648881504952498367)
  ·
    refine ⟨6093290473322257428747551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4062193648881504952498367 6093290473322257428747551)
    ·
      refine ⟨9139935709983386143121327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6093290473322257428747551 9139935709983386143121327)
      ·
        refine ⟨13709903564975079214681991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9139935709983386143121327 13709903564975079214681991)
        ·
          refine ⟨20564855347462618822022987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13709903564975079214681991 20564855347462618822022987)
          ·
            refine ⟨30847283021193928233034481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20564855347462618822022987 30847283021193928233034481)
            ·
              refine ⟨23135462265895446174775861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30847283021193928233034481 23135462265895446174775861)
              ·
                refine ⟨2168949587427698078885237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23135462265895446174775861 2168949587427698078885237)
                ·
                  refine ⟨203339023821346694895491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2168949587427698078885237 203339023821346694895491)
                  ·
                    rfl

theorem cell22_1782006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_1782006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782006 prefixEnd_1782006 := by exact prefixLift 1782006
  have htrace : WordTrace (prefixWord ++ tailWord_1782006) baseStart_1782006 baseEnd_1782006 := by
    simpa [prefixWord, tailWord_1782006, baseEnd_1782006] using wordTrace_append hprefix tailTrace_1782006
  have hstable : (prefixWord ++ tailWord_1782006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782006).length < 2 ^ (prefixWord ++ tailWord_1782006).sum := by decide
  have hdescent : baseEnd_1782006 < baseStart_1782006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782064 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 1, 6]
def baseStart_1782064 : Nat := 118140960795 + 1782064 * 2 ^ 59
def prefixEnd_1782064 : Nat := 4983230072969 + 3 ^ 40 * 1782064 * 2
def baseEnd_1782064 : Nat := 610036926049347266736295

theorem tailTrace_1782064 : CollatzResearch.WordTrace tailWord_1782064 prefixEnd_1782064 610036926049347266736295 := by
  unfold tailWord_1782064
  simp only [CollatzResearch.WordTrace]
  refine ⟨32498606907946977572792623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43331475877262636763723497 32498606907946977572792623)
  ·
    refine ⟨48747910361920466359188935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32498606907946977572792623 48747910361920466359188935)
    ·
      refine ⟨73121865542880699538783403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48747910361920466359188935 73121865542880699538783403)
      ·
        refine ⟨109682798314321049308175105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73121865542880699538783403 109682798314321049308175105)
        ·
          refine ⟨82262098735740786981131329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109682798314321049308175105 82262098735740786981131329)
          ·
            refine ⟨61696574051805590235848497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82262098735740786981131329 61696574051805590235848497)
            ·
              refine ⟨46272430538854192676886373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61696574051805590235848497 46272430538854192676886373)
              ·
                refine ⟨8676080726035161126916195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46272430538854192676886373 8676080726035161126916195)
                ·
                  refine ⟨13014121089052741690374293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8676080726035161126916195 13014121089052741690374293)
                  ·
                    refine ⟨610036926049347266736295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13014121089052741690374293 610036926049347266736295)
                    ·
                      rfl

theorem cell22_1782064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_1782064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782064 prefixEnd_1782064 := by exact prefixLift 1782064
  have htrace : WordTrace (prefixWord ++ tailWord_1782064) baseStart_1782064 baseEnd_1782064 := by
    simpa [prefixWord, tailWord_1782064, baseEnd_1782064] using wordTrace_append hprefix tailTrace_1782064
  have hstable : (prefixWord ++ tailWord_1782064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782064).length < 2 ^ (prefixWord ++ tailWord_1782064).sum := by decide
  have hdescent : baseEnd_1782064 < baseStart_1782064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782079 : List Nat := [1, 1, 2, 2, 4, 1, 1, 10]
def baseStart_1782079 : Nat := 118140960795 + 1782079 * 2 ^ 59
def prefixEnd_1782079 : Nat := 4983230072969 + 3 ^ 40 * 1782079 * 2
def baseEnd_1782079 : Nat := 67782451206210247512361

theorem tailTrace_1782079 : CollatzResearch.WordTrace tailWord_1782079 prefixEnd_1782079 67782451206210247512361 := by
  unfold tailWord_1782079
  simp only [CollatzResearch.WordTrace]
  refine ⟨64997760910839612707381291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43331840607226408471587527 64997760910839612707381291)
  ·
    refine ⟨97496641366259419061071937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64997760910839612707381291 97496641366259419061071937)
    ·
      refine ⟨73122481024694564295803953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97496641366259419061071937 73122481024694564295803953)
      ·
        refine ⟨54841860768520923221852965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73122481024694564295803953 54841860768520923221852965)
        ·
          refine ⟨10282848894097673104097431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54841860768520923221852965 10282848894097673104097431)
          ·
            refine ⟨15424273341146509656146147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10282848894097673104097431 15424273341146509656146147)
            ·
              refine ⟨23136410011719764484219221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15424273341146509656146147 23136410011719764484219221)
              ·
                refine ⟨67782451206210247512361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23136410011719764484219221 67782451206210247512361)
                ·
                  rfl

theorem cell22_1782079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 10].length) (baseStart_1782079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782079 prefixEnd_1782079 := by exact prefixLift 1782079
  have htrace : WordTrace (prefixWord ++ tailWord_1782079) baseStart_1782079 baseEnd_1782079 := by
    simpa [prefixWord, tailWord_1782079, baseEnd_1782079] using wordTrace_append hprefix tailTrace_1782079
  have hstable : (prefixWord ++ tailWord_1782079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782079).length < 2 ^ (prefixWord ++ tailWord_1782079).sum := by decide
  have hdescent : baseEnd_1782079 < baseStart_1782079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782100 : List Nat := [2, 4, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_1782100 : Nat := 118140960795 + 1782100 * 2 ^ 59
def prefixEnd_1782100 : Nat := 4983230072969 + 3 ^ 40 * 1782100 * 2
def baseEnd_1782100 : Nat := 610049249585055172836185

theorem tailTrace_1782100 : CollatzResearch.WordTrace tailWord_1782100 prefixEnd_1782100 610049249585055172836185 := by
  unfold tailWord_1782100
  simp only [CollatzResearch.WordTrace]
  refine ⟨32499263421881766646947877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43332351229175688862597169 32499263421881766646947877)
  ·
    refine ⟨6093611891602831246302727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32499263421881766646947877 6093611891602831246302727)
    ·
      refine ⟨9140417837404246869454091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6093611891602831246302727 9140417837404246869454091)
      ·
        refine ⟨13710626756106370304181137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9140417837404246869454091 13710626756106370304181137)
        ·
          refine ⟨10282970067079777728135853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13710626756106370304181137 10282970067079777728135853)
          ·
            refine ⟨3856113775154916648050945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10282970067079777728135853 3856113775154916648050945)
            ·
              refine ⟨2892085331366187486038209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3856113775154916648050945 2892085331366187486038209)
              ·
                refine ⟨2169063998524640614528657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2892085331366187486038209 2169063998524640614528657)
                ·
                  refine ⟨1626797998893480460896493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2169063998524640614528657 1626797998893480460896493)
                  ·
                    refine ⟨610049249585055172836185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1626797998893480460896493 610049249585055172836185)
                    ·
                      rfl

theorem cell22_1782100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_1782100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782100 prefixEnd_1782100 := by exact prefixLift 1782100
  have htrace : WordTrace (prefixWord ++ tailWord_1782100) baseStart_1782100 baseEnd_1782100 := by
    simpa [prefixWord, tailWord_1782100, baseEnd_1782100] using wordTrace_append hprefix tailTrace_1782100
  have hstable : (prefixWord ++ tailWord_1782100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782100).length < 2 ^ (prefixWord ++ tailWord_1782100).sum := by decide
  have hdescent : baseEnd_1782100 < baseStart_1782100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782128 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 3, 3]
def baseStart_1782128 : Nat := 118140960795 + 1782128 * 2 ^ 59
def prefixEnd_1782128 : Nat := 4983230072969 + 3 ^ 40 * 1782128 * 2
def baseEnd_1782128 : Nat := 610058834557272433136099

theorem tailTrace_1782128 : CollatzResearch.WordTrace tailWord_1782128 prefixEnd_1782128 610058834557272433136099 := by
  unfold tailWord_1782128
  simp only [CollatzResearch.WordTrace]
  refine ⟨32499774043831047037957519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43333032058441396050610025 32499774043831047037957519)
  ·
    refine ⟨48749661065746570556936279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32499774043831047037957519 48749661065746570556936279)
    ·
      refine ⟨73124491598619855835404419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48749661065746570556936279 73124491598619855835404419)
      ·
        refine ⟨109686737397929783753106629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73124491598619855835404419 109686737397929783753106629)
        ·
          refine ⟨20566263262111834453707493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109686737397929783753106629 20566263262111834453707493)
          ·
            refine ⟨3856174361645968960070155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20566263262111834453707493 3856174361645968960070155)
            ·
              refine ⟨5784261542468953440105233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3856174361645968960070155 5784261542468953440105233)
              ·
                refine ⟨4338196156851715080078925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5784261542468953440105233 4338196156851715080078925)
                ·
                  refine ⟨1626823558819393155029597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4338196156851715080078925 1626823558819393155029597)
                  ·
                    refine ⟨610058834557272433136099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1626823558819393155029597 610058834557272433136099)
                    ·
                      rfl

theorem cell22_1782128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 3, 3].length) (baseStart_1782128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782128 prefixEnd_1782128 := by exact prefixLift 1782128
  have htrace : WordTrace (prefixWord ++ tailWord_1782128) baseStart_1782128 baseEnd_1782128 := by
    simpa [prefixWord, tailWord_1782128, baseEnd_1782128] using wordTrace_append hprefix tailTrace_1782128
  have hstable : (prefixWord ++ tailWord_1782128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782128).length < 2 ^ (prefixWord ++ tailWord_1782128).sum := by decide
  have hdescent : baseEnd_1782128 < baseStart_1782128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782156 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 2, 5]
def baseStart_1782156 : Nat := 118140960795 + 1782156 * 2 ^ 59
def prefixEnd_1782156 : Nat := 4983230072969 + 3 ^ 40 * 1782156 * 2
def baseEnd_1782156 : Nat := 610068419529489693436013

theorem tailTrace_1782156 : CollatzResearch.WordTrace tailWord_1782156 prefixEnd_1782156 610068419529489693436013 := by
  unfold tailWord_1782156
  simp only [CollatzResearch.WordTrace]
  refine ⟨32500284665780327428967161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43333712887707103238622881 32500284665780327428967161)
  ·
    refine ⟨24375213499335245571725371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32500284665780327428967161 24375213499335245571725371)
    ·
      refine ⟨36562820249002868357588057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24375213499335245571725371 36562820249002868357588057)
      ·
        refine ⟨27422115186752151268191043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36562820249002868357588057 27422115186752151268191043)
        ·
          refine ⟨41133172780128226902286565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27422115186752151268191043 41133172780128226902286565)
          ·
            refine ⟨7712469896274042544178731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41133172780128226902286565 7712469896274042544178731)
            ·
              refine ⟨11568704844411063816268097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7712469896274042544178731 11568704844411063816268097)
              ·
                refine ⟨8676528633308297862201073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11568704844411063816268097 8676528633308297862201073)
                ·
                  refine ⟨6507396474981223396650805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8676528633308297862201073 6507396474981223396650805)
                  ·
                    refine ⟨610068419529489693436013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6507396474981223396650805 610068419529489693436013)
                    ·
                      rfl

theorem cell22_1782156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_1782156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782156 prefixEnd_1782156 := by exact prefixLift 1782156
  have htrace : WordTrace (prefixWord ++ tailWord_1782156) baseStart_1782156 baseEnd_1782156 := by
    simpa [prefixWord, tailWord_1782156, baseEnd_1782156] using wordTrace_append hprefix tailTrace_1782156
  have hstable : (prefixWord ++ tailWord_1782156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782156).length < 2 ^ (prefixWord ++ tailWord_1782156).sum := by decide
  have hdescent : baseEnd_1782156 < baseStart_1782156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782158 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 7]
def baseStart_1782158 : Nat := 118140960795 + 1782158 * 2 ^ 59
def prefixEnd_1782158 : Nat := 4983230072969 + 3 ^ 40 * 1782158 * 2
def baseEnd_1782158 : Nat := 203356368056787451628669

theorem tailTrace_1782158 : CollatzResearch.WordTrace tailWord_1782158 prefixEnd_1782158 203356368056787451628669 := by
  unfold tailWord_1782158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8125080284694176149938391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43333761518368939466338085 8125080284694176149938391)
  ·
    refine ⟨12187620427041264224907587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8125080284694176149938391 12187620427041264224907587)
    ·
      refine ⟨18281430640561896337361381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12187620427041264224907587 18281430640561896337361381)
      ·
        refine ⟨3427768245105355563255259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18281430640561896337361381 3427768245105355563255259)
        ·
          refine ⟨5141652367658033344882889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3427768245105355563255259 5141652367658033344882889)
          ·
            refine ⟨3856239275743525008662167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5141652367658033344882889 3856239275743525008662167)
            ·
              refine ⟨5784358913615287512993251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3856239275743525008662167 5784358913615287512993251)
              ·
                refine ⟨8676538370422931269489877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5784358913615287512993251 8676538370422931269489877)
                ·
                  refine ⟨203356368056787451628669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8676538370422931269489877 203356368056787451628669)
                  ·
                    rfl

theorem cell22_1782158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_1782158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782158 prefixEnd_1782158 := by exact prefixLift 1782158
  have htrace : WordTrace (prefixWord ++ tailWord_1782158) baseStart_1782158 baseEnd_1782158 := by
    simpa [prefixWord, tailWord_1782158, baseEnd_1782158] using wordTrace_append hprefix tailTrace_1782158
  have hstable : (prefixWord ++ tailWord_1782158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782158).length < 2 ^ (prefixWord ++ tailWord_1782158).sum := by decide
  have hdescent : baseEnd_1782158 < baseStart_1782158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782218 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 4, 3]
def baseStart_1782218 : Nat := 118140960795 + 1782218 * 2 ^ 59
def prefixEnd_1782218 : Nat := 4983230072969 + 3 ^ 40 * 1782218 * 2
def baseEnd_1782218 : Nat := 610089643396542198385823

theorem tailTrace_1782218 : CollatzResearch.WordTrace tailWord_1782218 prefixEnd_1782218 610089643396542198385823 := by
  unfold tailWord_1782218
  simp only [CollatzResearch.WordTrace]
  refine ⟨16250707664334009861672827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43335220438224026297794205 16250707664334009861672827)
  ·
    refine ⟨24376061496501014792509241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16250707664334009861672827 24376061496501014792509241)
    ·
      refine ⟨18282046122375761094381931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24376061496501014792509241 18282046122375761094381931)
      ·
        refine ⟨27423069183563641641572897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18282046122375761094381931 27423069183563641641572897)
        ·
          refine ⟨20567301887672731231179673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27423069183563641641572897 20567301887672731231179673)
          ·
            refine ⟨15425476415754548423384755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20567301887672731231179673 15425476415754548423384755)
            ·
              refine ⟨23138214623631822635077133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15425476415754548423384755 23138214623631822635077133)
              ·
                refine ⟨8676830483861933488153925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23138214623631822635077133 8676830483861933488153925)
                ·
                  refine ⟨1626905715724112529028861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8676830483861933488153925 1626905715724112529028861)
                  ·
                    refine ⟨610089643396542198385823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1626905715724112529028861 610089643396542198385823)
                    ·
                      rfl

theorem cell22_1782218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_1782218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782218 prefixEnd_1782218 := by exact prefixLift 1782218
  have htrace : WordTrace (prefixWord ++ tailWord_1782218) baseStart_1782218 baseEnd_1782218 := by
    simpa [prefixWord, tailWord_1782218, baseEnd_1782218] using wordTrace_append hprefix tailTrace_1782218
  have hstable : (prefixWord ++ tailWord_1782218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782218).length < 2 ^ (prefixWord ++ tailWord_1782218).sum := by decide
  have hdescent : baseEnd_1782218 < baseStart_1782218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782220 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 6]
def baseStart_1782220 : Nat := 118140960795 + 1782220 * 2 ^ 59
def prefixEnd_1782220 : Nat := 4983230072969 + 3 ^ 40 * 1782220 * 2
def baseEnd_1782220 : Nat := 203363442679138286611939

theorem tailTrace_1782220 : CollatzResearch.WordTrace tailWord_1782220 prefixEnd_1782220 203363442679138286611939 := by
  unfold tailWord_1782220
  simp only [CollatzResearch.WordTrace]
  refine ⟨32501451801664396894132057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43335269068885862525509409 32501451801664396894132057)
  ·
    refine ⟨24376088851248297670599043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32501451801664396894132057 24376088851248297670599043)
    ·
      refine ⟨36564133276872446505898565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24376088851248297670599043 36564133276872446505898565)
      ·
        refine ⟨6855774989413583719855981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36564133276872446505898565 6855774989413583719855981)
        ·
          refine ⟨2570915621030093894945993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6855774989413583719855981 2570915621030093894945993)
          ·
            refine ⟨1928186715772570421209495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2570915621030093894945993 1928186715772570421209495)
            ·
              refine ⟨2892280073658855631814243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1928186715772570421209495 2892280073658855631814243)
              ·
                refine ⟨4338420110488283447721365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2892280073658855631814243 4338420110488283447721365)
                ·
                  refine ⟨203363442679138286611939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4338420110488283447721365 203363442679138286611939)
                  ·
                    rfl

theorem cell22_1782220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_1782220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782220 prefixEnd_1782220 := by exact prefixLift 1782220
  have htrace : WordTrace (prefixWord ++ tailWord_1782220) baseStart_1782220 baseEnd_1782220 := by
    simpa [prefixWord, tailWord_1782220, baseEnd_1782220] using wordTrace_append hprefix tailTrace_1782220
  have hstable : (prefixWord ++ tailWord_1782220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782220).length < 2 ^ (prefixWord ++ tailWord_1782220).sum := by decide
  have hdescent : baseEnd_1782220 < baseStart_1782220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782250 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 2, 4]
def baseStart_1782250 : Nat := 118140960795 + 1782250 * 2 ^ 59
def prefixEnd_1782250 : Nat := 4983230072969 + 3 ^ 40 * 1782250 * 2
def baseEnd_1782250 : Nat := 610100597650504781585725

theorem tailTrace_1782250 : CollatzResearch.WordTrace tailWord_1782250 prefixEnd_1782250 610100597650504781585725 := by
  unfold tailWord_1782250
  simp only [CollatzResearch.WordTrace]
  refine ⟨16250999448305027227964051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43335998528813405941237469 16250999448305027227964051)
  ·
    refine ⟨24376499172457540841946077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16250999448305027227964051 24376499172457540841946077)
    ·
      refine ⟨9141187189671577815729779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24376499172457540841946077 9141187189671577815729779)
      ·
        refine ⟨13711780784507366723594669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9141187189671577815729779 13711780784507366723594669)
        ·
          refine ⟨5141917794190262521348001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13711780784507366723594669 5141917794190262521348001)
          ·
            refine ⟨3856438345642696891011001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5141917794190262521348001 3856438345642696891011001)
            ·
              refine ⟨2892328759232022668258251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3856438345642696891011001 2892328759232022668258251)
              ·
                refine ⟨4338493138848034002387377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2892328759232022668258251 4338493138848034002387377)
                ·
                  refine ⟨3253869854136025501790533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4338493138848034002387377 3253869854136025501790533)
                  ·
                    refine ⟨610100597650504781585725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3253869854136025501790533 610100597650504781585725)
                    ·
                      rfl

theorem cell22_1782250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_1782250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782250 prefixEnd_1782250 := by exact prefixLift 1782250
  have htrace : WordTrace (prefixWord ++ tailWord_1782250) baseStart_1782250 baseEnd_1782250 := by
    simpa [prefixWord, tailWord_1782250, baseEnd_1782250] using wordTrace_append hprefix tailTrace_1782250
  have hstable : (prefixWord ++ tailWord_1782250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782250).length < 2 ^ (prefixWord ++ tailWord_1782250).sum := by decide
  have hdescent : baseEnd_1782250 < baseStart_1782250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782293 : List Nat := [1, 3, 2, 1, 3, 1, 1, 5, 5]
def baseStart_1782293 : Nat := 118140960795 + 1782293 * 2 ^ 59
def prefixEnd_1782293 : Nat := 4983230072969 + 3 ^ 40 * 1782293 * 2
def baseEnd_1782293 : Nat := 203371772476422334253531

theorem tailTrace_1782293 : CollatzResearch.WordTrace tailWord_1782293 prefixEnd_1782293 203371772476422334253531 := by
  unfold tailWord_1782293
  simp only [CollatzResearch.WordTrace]
  refine ⟨65005566132064327255671533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43337044088042884837114355 65005566132064327255671533)
  ·
    refine ⟨24377087299524122720876825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65005566132064327255671533 24377087299524122720876825)
    ·
      refine ⟨18282815474643092040657619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24377087299524122720876825 18282815474643092040657619)
      ·
        refine ⟨27424223211964638060986429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18282815474643092040657619 27424223211964638060986429)
        ·
          refine ⟨10284083704486739272869911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27424223211964638060986429 10284083704486739272869911)
          ·
            refine ⟨15426125556730108909304867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10284083704486739272869911 15426125556730108909304867)
            ·
              refine ⟨23139188335095163363957301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15426125556730108909304867 23139188335095163363957301)
              ·
                refine ⟨2169298906415171565370997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23139188335095163363957301 2169298906415171565370997)
                ·
                  refine ⟨203371772476422334253531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2169298906415171565370997 203371772476422334253531)
                  ·
                    rfl

theorem cell22_1782293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_1782293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782293 prefixEnd_1782293 := by exact prefixLift 1782293
  have htrace : WordTrace (prefixWord ++ tailWord_1782293) baseStart_1782293 baseEnd_1782293 := by
    simpa [prefixWord, tailWord_1782293, baseEnd_1782293] using wordTrace_append hprefix tailTrace_1782293
  have hstable : (prefixWord ++ tailWord_1782293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782293).length < 2 ^ (prefixWord ++ tailWord_1782293).sum := by decide
  have hdescent : baseEnd_1782293 < baseStart_1782293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782314 : List Nat := [3, 1, 4, 1, 1, 3, 2, 3, 1, 3]
def baseStart_1782314 : Nat := 118140960795 + 1782314 * 2 ^ 59
def prefixEnd_1782314 : Nat := 4983230072969 + 3 ^ 40 * 1782314 * 2
def baseEnd_1782314 : Nat := 610122506158429947985529

theorem tailTrace_1782314 : CollatzResearch.WordTrace tailWord_1782314 prefixEnd_1782314 610122506158429947985529 := by
  unfold tailWord_1782314
  simp only [CollatzResearch.WordTrace]
  refine ⟨16251583016247061960546499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43337554709992165228123997 16251583016247061960546499)
  ·
    refine ⟨24377374524370592940819749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16251583016247061960546499 24377374524370592940819749)
    ·
      refine ⟨4570757723319486176403703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24377374524370592940819749 4570757723319486176403703)
      ·
        refine ⟨6856136584979229264605555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4570757723319486176403703 6856136584979229264605555)
        ·
          refine ⟨10284204877468843896908333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6856136584979229264605555 10284204877468843896908333)
          ·
            refine ⟨3856576829050816461340625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10284204877468843896908333 3856576829050816461340625)
            ·
              refine ⟨2892432621788112346005469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3856576829050816461340625 2892432621788112346005469)
              ·
                refine ⟨1084662233170542129752051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2892432621788112346005469 1084662233170542129752051)
                ·
                  refine ⟨1626993349755813194628077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1084662233170542129752051 1626993349755813194628077)
                  ·
                    refine ⟨610122506158429947985529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1626993349755813194628077 610122506158429947985529)
                    ·
                      rfl

theorem cell22_1782314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_1782314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782314 prefixEnd_1782314 := by exact prefixLift 1782314
  have htrace : WordTrace (prefixWord ++ tailWord_1782314) baseStart_1782314 baseEnd_1782314 := by
    simpa [prefixWord, tailWord_1782314, baseEnd_1782314] using wordTrace_append hprefix tailTrace_1782314
  have hstable : (prefixWord ++ tailWord_1782314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782314).length < 2 ^ (prefixWord ++ tailWord_1782314).sum := by decide
  have hdescent : baseEnd_1782314 < baseStart_1782314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782342 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_1782342 : Nat := 118140960795 + 1782342 * 2 ^ 59
def prefixEnd_1782342 : Nat := 4983230072969 + 3 ^ 40 * 1782342 * 2
def baseEnd_1782342 : Nat := 610132091130647208285443

theorem tailTrace_1782342 : CollatzResearch.WordTrace tailWord_1782342 prefixEnd_1782342 610132091130647208285443 := by
  unfold tailWord_1782342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2031479790902712769506415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43338235539257872416136853 2031479790902712769506415)
  ·
    refine ⟨3047219686354069154259623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2031479790902712769506415 3047219686354069154259623)
    ·
      refine ⟨4570829529531103731389435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3047219686354069154259623 4570829529531103731389435)
      ·
        refine ⟨6856244294296655597084153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4570829529531103731389435 6856244294296655597084153)
        ·
          refine ⟨5142183220722491697813115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6856244294296655597084153 5142183220722491697813115)
          ·
            refine ⟨7713274831083737546719673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5142183220722491697813115 7713274831083737546719673)
            ·
              refine ⟨5784956123312803160039755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7713274831083737546719673 5784956123312803160039755)
              ·
                refine ⟨8677434184969204740059633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5784956123312803160039755 8677434184969204740059633)
                ·
                  refine ⟨6508075638726903555044725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8677434184969204740059633 6508075638726903555044725)
                  ·
                    refine ⟨610132091130647208285443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6508075638726903555044725 610132091130647208285443)
                    ·
                      rfl

theorem cell22_1782342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_1782342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782342 prefixEnd_1782342 := by exact prefixLift 1782342
  have htrace : WordTrace (prefixWord ++ tailWord_1782342) baseStart_1782342 baseEnd_1782342 := by
    simpa [prefixWord, tailWord_1782342, baseEnd_1782342] using wordTrace_append hprefix tailTrace_1782342
  have hstable : (prefixWord ++ tailWord_1782342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782342).length < 2 ^ (prefixWord ++ tailWord_1782342).sum := by decide
  have hdescent : baseEnd_1782342 < baseStart_1782342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782368 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 1, 6]
def baseStart_1782368 : Nat := 118140960795 + 1782368 * 2 ^ 59
def prefixEnd_1782368 : Nat := 4983230072969 + 3 ^ 40 * 1782368 * 2
def baseEnd_1782368 : Nat := 610140991461991807135363

theorem tailTrace_1782368 : CollatzResearch.WordTrace tailWord_1782368 prefixEnd_1782368 610140991461991807135363 := by
  unfold tailWord_1782368
  simp only [CollatzResearch.WordTrace]
  refine ⟨32504150803396307532325879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43338867737861743376434505 32504150803396307532325879)
  ·
    refine ⟨48756226205094461298488819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32504150803396307532325879 48756226205094461298488819)
    ·
      refine ⟨73134339307641691947733229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48756226205094461298488819 73134339307641691947733229)
      ·
        refine ⟨27425377240365634480399961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73134339307641691947733229 27425377240365634480399961)
        ·
          refine ⟨20569032930274225860299971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27425377240365634480399961 20569032930274225860299971)
          ·
            refine ⟨30853549395411338790449957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20569032930274225860299971 30853549395411338790449957)
            ·
              refine ⟨5785040511639626023209367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30853549395411338790449957 5785040511639626023209367)
              ·
                refine ⟨8677560767459439034814051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5785040511639626023209367 8677560767459439034814051)
                ·
                  refine ⟨13016341151189158552221077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8677560767459439034814051 13016341151189158552221077)
                  ·
                    refine ⟨610140991461991807135363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13016341151189158552221077 610140991461991807135363)
                    ·
                      rfl

theorem cell22_1782368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_1782368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782368 prefixEnd_1782368 := by exact prefixLift 1782368
  have htrace : WordTrace (prefixWord ++ tailWord_1782368) baseStart_1782368 baseEnd_1782368 := by
    simpa [prefixWord, tailWord_1782368, baseEnd_1782368] using wordTrace_append hprefix tailTrace_1782368
  have hstable : (prefixWord ++ tailWord_1782368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782368).length < 2 ^ (prefixWord ++ tailWord_1782368).sum := by decide
  have hdescent : baseEnd_1782368 < baseStart_1782368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782389 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 6]
def baseStart_1782389 : Nat := 118140960795 + 1782389 * 2 ^ 59
def prefixEnd_1782389 : Nat := 4983230072969 + 3 ^ 40 * 1782389 * 2
def baseEnd_1782389 : Nat := 203382726730384917453433

theorem tailTrace_1782389 : CollatzResearch.WordTrace tailWord_1782389 prefixEnd_1782389 203382726730384917453433 := by
  unfold tailWord_1782389
  simp only [CollatzResearch.WordTrace]
  refine ⟨65009067539716535651166221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43339378359811023767444147 65009067539716535651166221)
  ·
    refine ⟨24378400327393700869187333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65009067539716535651166221 24378400327393700869187333)
    ·
      refine ⟨4570950061386318912972625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24378400327393700869187333 4570950061386318912972625)
      ·
        refine ⟨3428212546039739184729469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4570950061386318912972625 3428212546039739184729469)
        ·
          refine ⟨1285579704764902194273551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3428212546039739184729469 1285579704764902194273551)
          ·
            refine ⟨1928369557147353291410327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285579704764902194273551 1928369557147353291410327)
            ·
              refine ⟨2892554335721029937115491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1928369557147353291410327 2892554335721029937115491)
              ·
                refine ⟨4338831503581544905673237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2892554335721029937115491 4338831503581544905673237)
                ·
                  refine ⟨203382726730384917453433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4338831503581544905673237 203382726730384917453433)
                  ·
                    rfl

theorem cell22_1782389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_1782389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782389 prefixEnd_1782389 := by exact prefixLift 1782389
  have htrace : WordTrace (prefixWord ++ tailWord_1782389) baseStart_1782389 baseEnd_1782389 := by
    simpa [prefixWord, tailWord_1782389, baseEnd_1782389] using wordTrace_append hprefix tailTrace_1782389
  have hstable : (prefixWord ++ tailWord_1782389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782389).length < 2 ^ (prefixWord ++ tailWord_1782389).sum := by decide
  have hdescent : baseEnd_1782389 < baseStart_1782389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782404 : List Nat := [2, 3, 2, 1, 3, 1, 4, 1, 2, 3]
def baseStart_1782404 : Nat := 118140960795 + 1782404 * 2 ^ 59
def prefixEnd_1782404 : Nat := 4983230072969 + 3 ^ 40 * 1782404 * 2
def baseEnd_1782404 : Nat := 610153314997699713235253

theorem tailTrace_1782404 : CollatzResearch.WordTrace tailWord_1782404 prefixEnd_1782404 610153314997699713235253 := by
  unfold tailWord_1782404
  simp only [CollatzResearch.WordTrace]
  refine ⟨32504807317331096606481133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43339743089774795475308177 32504807317331096606481133)
  ·
    refine ⟨12189302743999161227430425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32504807317331096606481133 12189302743999161227430425)
    ·
      refine ⟨9141977057999370920572819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12189302743999161227430425 9141977057999370920572819)
      ·
        refine ⟨13712965586999056380859229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9141977057999370920572819 13712965586999056380859229)
        ·
          refine ⟨5142362095124646142822211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13712965586999056380859229 5142362095124646142822211)
          ·
            refine ⟨7713543142686969214233317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5142362095124646142822211 7713543142686969214233317)
            ·
              refine ⟨1446289339253806727668747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7713543142686969214233317 1446289339253806727668747)
              ·
                refine ⟨2169434008880710091503121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446289339253806727668747 2169434008880710091503121)
                ·
                  refine ⟨1627075506660532568627341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2169434008880710091503121 1627075506660532568627341)
                  ·
                    refine ⟨610153314997699713235253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1627075506660532568627341 610153314997699713235253)
                    ·
                      rfl

theorem cell22_1782404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_1782404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782404 prefixEnd_1782404 := by exact prefixLift 1782404
  have htrace : WordTrace (prefixWord ++ tailWord_1782404) baseStart_1782404 baseEnd_1782404 := by
    simpa [prefixWord, tailWord_1782404, baseEnd_1782404] using wordTrace_append hprefix tailTrace_1782404
  have hstable : (prefixWord ++ tailWord_1782404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782404).length < 2 ^ (prefixWord ++ tailWord_1782404).sum := by decide
  have hdescent : baseEnd_1782404 < baseStart_1782404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782460 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 2, 5]
def baseStart_1782460 : Nat := 118140960795 + 1782460 * 2 ^ 59
def prefixEnd_1782460 : Nat := 4983230072969 + 3 ^ 40 * 1782460 * 2
def baseEnd_1782460 : Nat := 610172484942134233835081

theorem tailTrace_1782460 : CollatzResearch.WordTrace tailWord_1782460 prefixEnd_1782460 610172484942134233835081 := by
  unfold tailWord_1782460
  simp only [CollatzResearch.WordTrace]
  refine ⟨32505828561229657388500417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43341104748306209851333889 32505828561229657388500417)
  ·
    refine ⟨24379371420922243041375313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32505828561229657388500417 24379371420922243041375313)
    ·
      refine ⟨18284528565691682281031485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24379371420922243041375313 18284528565691682281031485)
      ·
        refine ⟨6856698212134380855386807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18284528565691682281031485 6856698212134380855386807)
        ·
          refine ⟨10285047318201571283080211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6856698212134380855386807 10285047318201571283080211)
          ·
            refine ⟨15427570977302356924620317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10285047318201571283080211 15427570977302356924620317)
            ·
              refine ⟨5785339116488383846732619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15427570977302356924620317 5785339116488383846732619)
              ·
                refine ⟨8678008674732575770098929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5785339116488383846732619 8678008674732575770098929)
                ·
                  refine ⟨6508506506049431827574197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8678008674732575770098929 6508506506049431827574197)
                  ·
                    refine ⟨610172484942134233835081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6508506506049431827574197 610172484942134233835081)
                    ·
                      rfl

theorem cell22_1782460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_1782460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782460 prefixEnd_1782460 := by exact prefixLift 1782460
  have htrace : WordTrace (prefixWord ++ tailWord_1782460) baseStart_1782460 baseEnd_1782460 := by
    simpa [prefixWord, tailWord_1782460, baseEnd_1782460] using wordTrace_append hprefix tailTrace_1782460
  have hstable : (prefixWord ++ tailWord_1782460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782460).length < 2 ^ (prefixWord ++ tailWord_1782460).sum := by decide
  have hdescent : baseEnd_1782460 < baseStart_1782460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782522 : List Nat := [3, 1, 1, 1, 1, 3, 2, 5, 2, 3]
def baseStart_1782522 : Nat := 118140960795 + 1782522 * 2 ^ 59
def prefixEnd_1782522 : Nat := 4983230072969 + 3 ^ 40 * 1782522 * 2
def baseEnd_1782522 : Nat := 610193708809186738784891

theorem tailTrace_1782522 : CollatzResearch.WordTrace tailWord_1782522 prefixEnd_1782522 610193708809186738784891 := by
  unfold tailWord_1782522
  simp only [CollatzResearch.WordTrace]
  refine ⟨16253479612058674841439455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43342612298823132910505213 16253479612058674841439455)
  ·
    refine ⟨24380219418088012262159183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16253479612058674841439455 24380219418088012262159183)
    ·
      refine ⟨36570329127132018393238775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24380219418088012262159183 36570329127132018393238775)
      ·
        refine ⟨54855493690698027589858163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36570329127132018393238775 54855493690698027589858163)
        ·
          refine ⟨82283240536047041384787245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54855493690698027589858163 82283240536047041384787245)
          ·
            refine ⟨30856215201017640519295217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82283240536047041384787245 30856215201017640519295217)
            ·
              refine ⟨23142161400763230389471413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30856215201017640519295217 23142161400763230389471413)
              ·
                refine ⟨2169577631321552849012945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23142161400763230389471413 2169577631321552849012945)
                ·
                  refine ⟨1627183223491164636759709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2169577631321552849012945 1627183223491164636759709)
                  ·
                    refine ⟨610193708809186738784891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1627183223491164636759709 610193708809186738784891)
                    ·
                      rfl

theorem cell22_1782522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_1782522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782522 prefixEnd_1782522 := by exact prefixLift 1782522
  have htrace : WordTrace (prefixWord ++ tailWord_1782522) baseStart_1782522 baseEnd_1782522 := by
    simpa [prefixWord, tailWord_1782522, baseEnd_1782522] using wordTrace_append hprefix tailTrace_1782522
  have hstable : (prefixWord ++ tailWord_1782522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782522).length < 2 ^ (prefixWord ++ tailWord_1782522).sum := by decide
  have hdescent : baseEnd_1782522 < baseStart_1782522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782565 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 2, 6]
def baseStart_1782565 : Nat := 118140960795 + 1782565 * 2 ^ 59
def prefixEnd_1782565 : Nat := 4983230072969 + 3 ^ 40 * 1782565 * 2
def baseEnd_1782565 : Nat := 610208428587948959959759

theorem tailTrace_1782565 : CollatzResearch.WordTrace tailWord_1782565 prefixEnd_1782565 610208428587948959959759 := by
  unfold tailWord_1782565
  simp only [CollatzResearch.WordTrace]
  refine ⟨65015486787078917709573149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43343657858052611806382099 65015486787078917709573149)
  ·
    refine ⟨24380807545154594141089931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65015486787078917709573149 24380807545154594141089931)
    ·
      refine ⟨36571211317731891211634897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24380807545154594141089931 36571211317731891211634897)
      ·
        refine ⟨27428408488298918408726173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36571211317731891211634897 27428408488298918408726173)
        ·
          refine ⟨10285653183112094403272315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27428408488298918408726173 10285653183112094403272315)
          ·
            refine ⟨15428479774668141604908473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10285653183112094403272315 15428479774668141604908473)
            ·
              refine ⟨11571359831001106203681355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15428479774668141604908473 11571359831001106203681355)
              ·
                refine ⟨17357039746501659305522033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11571359831001106203681355 17357039746501659305522033)
                ·
                  refine ⟨13017779809876244479141525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17357039746501659305522033 13017779809876244479141525)
                  ·
                    refine ⟨610208428587948959959759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13017779809876244479141525 610208428587948959959759)
                    ·
                      rfl

theorem cell22_1782565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_1782565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782565 prefixEnd_1782565 := by exact prefixLift 1782565
  have htrace : WordTrace (prefixWord ++ tailWord_1782565) baseStart_1782565 baseEnd_1782565 := by
    simpa [prefixWord, tailWord_1782565, baseEnd_1782565] using wordTrace_append hprefix tailTrace_1782565
  have hstable : (prefixWord ++ tailWord_1782565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782565).length < 2 ^ (prefixWord ++ tailWord_1782565).sum := by decide
  have hdescent : baseEnd_1782565 < baseStart_1782565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782573 : List Nat := [1, 5, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1782573 : Nat := 118140960795 + 1782573 * 2 ^ 59
def prefixEnd_1782573 : Nat := 4983230072969 + 3 ^ 40 * 1782573 * 2
def baseEnd_1782573 : Nat := 610211167151439605759735

theorem tailTrace_1782573 : CollatzResearch.WordTrace tailWord_1782573 prefixEnd_1782573 610211167151439605759735 := by
  unfold tailWord_1782573
  simp only [CollatzResearch.WordTrace]
  refine ⟨65015778571049935075864373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43343852380699956717242915 65015778571049935075864373)
  ·
    refine ⟨6095229241035931413362285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65015778571049935075864373 6095229241035931413362285)
    ·
      refine ⟨2285710965388474280010857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6095229241035931413362285 2285710965388474280010857)
      ·
        refine ⟨1714283224041355710008143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2285710965388474280010857 1714283224041355710008143)
        ·
          refine ⟨2571424836062033565012215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1714283224041355710008143 2571424836062033565012215)
          ·
            refine ⟨3857137254093050347518323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2571424836062033565012215 3857137254093050347518323)
            ·
              refine ⟨5785705881139575521277485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3857137254093050347518323 5785705881139575521277485)
              ·
                refine ⟨2169639705427340820479057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5785705881139575521277485 2169639705427340820479057)
                ·
                  refine ⟨1627229779070505615359293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2169639705427340820479057 1627229779070505615359293)
                  ·
                    refine ⟨610211167151439605759735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1627229779070505615359293 610211167151439605759735)
                    ·
                      rfl

theorem cell22_1782573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1782573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782573 prefixEnd_1782573 := by exact prefixLift 1782573
  have htrace : WordTrace (prefixWord ++ tailWord_1782573) baseStart_1782573 baseEnd_1782573 := by
    simpa [prefixWord, tailWord_1782573, baseEnd_1782573] using wordTrace_append hprefix tailTrace_1782573
  have hstable : (prefixWord ++ tailWord_1782573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782573).length < 2 ^ (prefixWord ++ tailWord_1782573).sum := by decide
  have hdescent : baseEnd_1782573 < baseStart_1782573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782618 : List Nat := [3, 1, 1, 2, 1, 6, 2, 2, 1, 3]
def baseStart_1782618 : Nat := 118140960795 + 1782618 * 2 ^ 59
def prefixEnd_1782618 : Nat := 4983230072969 + 3 ^ 40 * 1782618 * 2
def baseEnd_1782618 : Nat := 610226571571074488384597

theorem tailTrace_1782618 : CollatzResearch.WordTrace tailWord_1782618 prefixEnd_1782618 610226571571074488384597 := by
  unfold tailWord_1782618
  simp only [CollatzResearch.WordTrace]
  refine ⟨16254354963971726940313127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43344946570591271840835005 16254354963971726940313127)
  ·
    refine ⟨24381532445957590410469691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16254354963971726940313127 24381532445957590410469691)
    ·
      refine ⟨36572298668936385615704537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24381532445957590410469691 36572298668936385615704537)
      ·
        refine ⟨27429224001702289211778403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36572298668936385615704537 27429224001702289211778403)
        ·
          refine ⟨41143836002553433817667605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27429224001702289211778403 41143836002553433817667605)
          ·
            refine ⟨1928617312619692210203169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41143836002553433817667605 1928617312619692210203169)
            ·
              refine ⟨1446462984464769157652377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1928617312619692210203169 1446462984464769157652377)
              ·
                refine ⟨1084847238348576868239283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1446462984464769157652377 1084847238348576868239283)
                ·
                  refine ⟨1627270857522865302358925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1084847238348576868239283 1627270857522865302358925)
                  ·
                    refine ⟨610226571571074488384597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1627270857522865302358925 610226571571074488384597)
                    ·
                      rfl

theorem cell22_1782618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_1782618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782618 prefixEnd_1782618 := by exact prefixLift 1782618
  have htrace : WordTrace (prefixWord ++ tailWord_1782618) baseStart_1782618 baseEnd_1782618 := by
    simpa [prefixWord, tailWord_1782618, baseEnd_1782618] using wordTrace_append hprefix tailTrace_1782618
  have hstable : (prefixWord ++ tailWord_1782618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782618).length < 2 ^ (prefixWord ++ tailWord_1782618).sum := by decide
  have hdescent : baseEnd_1782618 < baseStart_1782618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782627 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 3, 4]
def baseStart_1782627 : Nat := 118140960795 + 1782627 * 2 ^ 59
def prefixEnd_1782627 : Nat := 4983230072969 + 3 ^ 40 * 1782627 * 2
def baseEnd_1782627 : Nat := 610229652455001464909569

theorem tailTrace_1782627 : CollatzResearch.WordTrace tailWord_1782627 prefixEnd_1782627 610229652455001464909569 := by
  unfold tailWord_1782627
  simp only [CollatzResearch.WordTrace]
  refine ⟨65017748112854302298330135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43345165408569534865553423 65017748112854302298330135)
  ·
    refine ⟨97526622169281453447495203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65017748112854302298330135 97526622169281453447495203)
    ·
      refine ⟨146289933253922180171242805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97526622169281453447495203 146289933253922180171242805)
      ·
        refine ⟨13714681242555204391054013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146289933253922180171242805 13714681242555204391054013)
        ·
          refine ⟨5143005465958201646645255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13714681242555204391054013 5143005465958201646645255)
          ·
            refine ⟨7714508198937302469967883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143005465958201646645255 7714508198937302469967883)
            ·
              refine ⟨11571762298405953704951825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7714508198937302469967883 11571762298405953704951825)
              ·
                refine ⟨8678821723804465278713869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11571762298405953704951825 8678821723804465278713869)
                ·
                  refine ⟨3254558146426674479517701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8678821723804465278713869 3254558146426674479517701)
                  ·
                    refine ⟨610229652455001464909569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3254558146426674479517701 610229652455001464909569)
                    ·
                      rfl

theorem cell22_1782627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 4].length) (baseStart_1782627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782627 prefixEnd_1782627 := by exact prefixLift 1782627
  have htrace : WordTrace (prefixWord ++ tailWord_1782627) baseStart_1782627 baseEnd_1782627 := by
    simpa [prefixWord, tailWord_1782627, baseEnd_1782627] using wordTrace_append hprefix tailTrace_1782627
  have hstable : (prefixWord ++ tailWord_1782627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782627).length < 2 ^ (prefixWord ++ tailWord_1782627).sum := by decide
  have hdescent : baseEnd_1782627 < baseStart_1782627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782659 : List Nat := [1, 1, 1, 3, 4, 1, 4, 3, 4]
def baseStart_1782659 : Nat := 118140960795 + 1782659 * 2 ^ 59
def prefixEnd_1782659 : Nat := 4983230072969 + 3 ^ 40 * 1782659 * 2
def baseEnd_1782659 : Nat := 203413535569654682703157

theorem tailTrace_1782659 : CollatzResearch.WordTrace tailWord_1782659 prefixEnd_1782659 203413535569654682703157 := by
  unfold tailWord_1782659
  simp only [CollatzResearch.WordTrace]
  refine ⟨65018915248738371763495031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43345943499158914508996687 65018915248738371763495031)
  ·
    refine ⟨97528372873107557645242547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65018915248738371763495031 97528372873107557645242547)
    ·
      refine ⟨146292559309661336467863821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97528372873107557645242547 146292559309661336467863821)
      ·
        refine ⟨54859709741123001175448933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146292559309661336467863821 54859709741123001175448933)
        ·
          refine ⟨10286195576460562720396675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54859709741123001175448933 10286195576460562720396675)
          ·
            refine ⟨15429293364690844080595013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10286195576460562720396675 15429293364690844080595013)
            ·
              refine ⟨2892992505879533265111565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15429293364690844080595013 2892992505879533265111565)
              ·
                refine ⟨1084872189704824974416837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2892992505879533265111565 1084872189704824974416837)
                ·
                  refine ⟨203413535569654682703157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1084872189704824974416837 203413535569654682703157)
                  ·
                    rfl

theorem cell22_1782659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 4].length) (baseStart_1782659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782659 prefixEnd_1782659 := by exact prefixLift 1782659
  have htrace : WordTrace (prefixWord ++ tailWord_1782659) baseStart_1782659 baseEnd_1782659 := by
    simpa [prefixWord, tailWord_1782659, baseEnd_1782659] using wordTrace_append hprefix tailTrace_1782659
  have hstable : (prefixWord ++ tailWord_1782659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782659).length < 2 ^ (prefixWord ++ tailWord_1782659).sum := by decide
  have hdescent : baseEnd_1782659 < baseStart_1782659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782661 : List Nat := [1, 3, 1, 1, 3, 5, 2, 1, 1, 4]
def baseStart_1782661 : Nat := 118140960795 + 1782661 * 2 ^ 59
def prefixEnd_1782661 : Nat := 4983230072969 + 3 ^ 40 * 1782661 * 2
def baseEnd_1782661 : Nat := 610241291349836709559465

theorem tailTrace_1782661 : CollatzResearch.WordTrace tailWord_1782661 prefixEnd_1782661 610241291349836709559465 := by
  unfold tailWord_1782661
  simp only [CollatzResearch.WordTrace]
  refine ⟨65018988194731126105067837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43345992129820750736711891 65018988194731126105067837)
  ·
    refine ⟨24382120573024172289400439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65018988194731126105067837 24382120573024172289400439)
    ·
      refine ⟨36573180859536258434100659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24382120573024172289400439 36573180859536258434100659)
      ·
        refine ⟨54859771289304387651150989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36573180859536258434100659 54859771289304387651150989)
        ·
          refine ⟨20572414233489145369181621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54859771289304387651150989 20572414233489145369181621)
          ·
            refine ⟨1928663834389607378360777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20572414233489145369181621 1928663834389607378360777)
            ·
              refine ⟨1446497875792205533770583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1928663834389607378360777 1446497875792205533770583)
              ·
                refine ⟨2169746813688308300655875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446497875792205533770583 2169746813688308300655875)
                ·
                  refine ⟨3254620220532462450983813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2169746813688308300655875 3254620220532462450983813)
                  ·
                    refine ⟨610241291349836709559465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3254620220532462450983813 610241291349836709559465)
                    ·
                      rfl

theorem cell22_1782661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_1782661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782661 prefixEnd_1782661 := by exact prefixLift 1782661
  have htrace : WordTrace (prefixWord ++ tailWord_1782661) baseStart_1782661 baseEnd_1782661 := by
    simpa [prefixWord, tailWord_1782661, baseEnd_1782661] using wordTrace_append hprefix tailTrace_1782661
  have hstable : (prefixWord ++ tailWord_1782661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782661).length < 2 ^ (prefixWord ++ tailWord_1782661).sum := by decide
  have hdescent : baseEnd_1782661 < baseStart_1782661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782732 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 7]
def baseStart_1782732 : Nat := 118140960795 + 1782732 * 2 ^ 59
def prefixEnd_1782732 : Nat := 4983230072969 + 3 ^ 40 * 1782732 * 2
def baseEnd_1782732 : Nat := 203421865366938730344749

theorem tailTrace_1782732 : CollatzResearch.WordTrace tailWord_1782732 prefixEnd_1782732 203421865366938730344749 := by
  unfold tailWord_1782732
  simp only [CollatzResearch.WordTrace]
  refine ⟨32510788888736952615451225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43347718518315936820601633 32510788888736952615451225)
  ·
    refine ⟨24383091666552714461588419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32510788888736952615451225 24383091666552714461588419)
    ·
      refine ⟨36574637499829071692382629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24383091666552714461588419 36574637499829071692382629)
      ·
        refine ⟨6857744531217950942321743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36574637499829071692382629 6857744531217950942321743)
        ·
          refine ⟨10286616796826926413482615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6857744531217950942321743 10286616796826926413482615)
          ·
            refine ⟨15429925195240389620223923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10286616796826926413482615 15429925195240389620223923)
            ·
              refine ⟨23144887792860584430335885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15429925195240389620223923 23144887792860584430335885)
              ·
                refine ⟨8679332922322719161375957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23144887792860584430335885 8679332922322719161375957)
                ·
                  refine ⟨203421865366938730344749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8679332922322719161375957 203421865366938730344749)
                  ·
                    rfl

theorem cell22_1782732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_1782732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782732 prefixEnd_1782732 := by exact prefixLift 1782732
  have htrace : WordTrace (prefixWord ++ tailWord_1782732) baseStart_1782732 baseEnd_1782732 := by
    simpa [prefixWord, tailWord_1782732, baseEnd_1782732] using wordTrace_append hprefix tailTrace_1782732
  have hstable : (prefixWord ++ tailWord_1782732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782732).length < 2 ^ (prefixWord ++ tailWord_1782732).sum := by decide
  have hdescent : baseEnd_1782732 < baseStart_1782732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782867 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 9]
def baseStart_1782867 : Nat := 118140960795 + 1782867 * 2 ^ 59
def prefixEnd_1782867 : Nat := 4983230072969 + 3 ^ 40 * 1782867 * 2
def baseEnd_1782867 : Nat := 203437269786573612969611

theorem tailTrace_1782867 : CollatzResearch.WordTrace tailWord_1782867 prefixEnd_1782867 203437269786573612969611 := by
  unfold tailWord_1782867
  simp only [CollatzResearch.WordTrace]
  refine ⟨65026501631984823287066855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43351001087989882191377903 65026501631984823287066855)
  ·
    refine ⟨97539752447977234930600283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65026501631984823287066855 97539752447977234930600283)
    ·
      refine ⟨146309628671965852395900425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97539752447977234930600283 146309628671965852395900425)
      ·
        refine ⟨109732221503974389296925319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146309628671965852395900425 109732221503974389296925319)
        ·
          refine ⟨164598332255961583945387979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109732221503974389296925319 164598332255961583945387979)
          ·
            refine ⟨246897498383942375918081969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164598332255961583945387979 246897498383942375918081969)
            ·
              refine ⟨185173123787956781938561477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246897498383942375918081969 185173123787956781938561477)
              ·
                refine ⟨34719960710241896613480277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185173123787956781938561477 34719960710241896613480277)
                ·
                  refine ⟨203437269786573612969611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34719960710241896613480277 203437269786573612969611)
                  ·
                    rfl

theorem cell22_1782867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 9].length) (baseStart_1782867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782867 prefixEnd_1782867 := by exact prefixLift 1782867
  have htrace : WordTrace (prefixWord ++ tailWord_1782867) baseStart_1782867 baseEnd_1782867 := by
    simpa [prefixWord, tailWord_1782867, baseEnd_1782867] using wordTrace_append hprefix tailTrace_1782867
  have hstable : (prefixWord ++ tailWord_1782867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782867).length < 2 ^ (prefixWord ++ tailWord_1782867).sum := by decide
  have hdescent : baseEnd_1782867 < baseStart_1782867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782905 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 3, 3]
def baseStart_1782905 : Nat := 118140960795 + 1782905 * 2 ^ 59
def prefixEnd_1782905 : Nat := 4983230072969 + 3 ^ 40 * 1782905 * 2
def baseEnd_1782905 : Nat := 610324817536301406458717

theorem tailTrace_1782905 : CollatzResearch.WordTrace tailWord_1782905 prefixEnd_1782905 610324817536301406458717 := by
  unfold tailWord_1782905
  simp only [CollatzResearch.WordTrace]
  refine ⟨65027887605847155776950169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43351925070564770517966779 65027887605847155776950169)
  ·
    refine ⟨48770915704385366832712627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65027887605847155776950169 48770915704385366832712627)
    ·
      refine ⟨73156373556578050249068941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48770915704385366832712627 73156373556578050249068941)
      ·
        refine ⟨27433640083716768843400853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73156373556578050249068941 27433640083716768843400853)
        ·
          refine ⟨1285951878924223539534415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27433640083716768843400853 1285951878924223539534415)
          ·
            refine ⟨1928927818386335309301623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285951878924223539534415 1928927818386335309301623)
            ·
              refine ⟨2893391727579502963952435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1928927818386335309301623 2893391727579502963952435)
              ·
                refine ⟨4340087591369254445928653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2893391727579502963952435 4340087591369254445928653)
                ·
                  refine ⟨1627532846763470417223245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4340087591369254445928653 1627532846763470417223245)
                  ·
                    refine ⟨610324817536301406458717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1627532846763470417223245 610324817536301406458717)
                    ·
                      rfl

theorem cell22_1782905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 3, 3].length) (baseStart_1782905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782905 prefixEnd_1782905 := by exact prefixLift 1782905
  have htrace : WordTrace (prefixWord ++ tailWord_1782905) baseStart_1782905 baseEnd_1782905 := by
    simpa [prefixWord, tailWord_1782905, baseEnd_1782905] using wordTrace_append hprefix tailTrace_1782905
  have hstable : (prefixWord ++ tailWord_1782905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782905).length < 2 ^ (prefixWord ++ tailWord_1782905).sum := by decide
  have hdescent : baseEnd_1782905 < baseStart_1782905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782931 : List Nat := [1, 1, 1, 2, 1, 2, 7, 2, 1, 4]
def baseStart_1782931 : Nat := 118140960795 + 1782931 * 2 ^ 59
def prefixEnd_1782931 : Nat := 4983230072969 + 3 ^ 40 * 1782931 * 2
def baseEnd_1782931 : Nat := 610333717867646005308637

theorem tailTrace_1782931 : CollatzResearch.WordTrace tailWord_1782931 prefixEnd_1782931 610333717867646005308637 := by
  unfold tailWord_1782931
  simp only [CollatzResearch.WordTrace]
  refine ⟨65028835903752962217396647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43352557269168641478264431 65028835903752962217396647)
  ·
    refine ⟨97543253855629443326094971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65028835903752962217396647 97543253855629443326094971)
    ·
      refine ⟨146314880783444164989142457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97543253855629443326094971 146314880783444164989142457)
      ·
        refine ⟨109736160587583123741856843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146314880783444164989142457 109736160587583123741856843)
        ·
          refine ⟨164604240881374685612785265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109736160587583123741856843 164604240881374685612785265)
          ·
            refine ⟨123453180661031014209588949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164604240881374685612785265 123453180661031014209588949)
            ·
              refine ⟨2893433921742914395537241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 123453180661031014209588949 2893433921742914395537241)
              ·
                refine ⟨2170075441307185796652931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2893433921742914395537241 2170075441307185796652931)
                ·
                  refine ⟨3255113161960778694979397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2170075441307185796652931 3255113161960778694979397)
                  ·
                    refine ⟨610333717867646005308637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3255113161960778694979397 610333717867646005308637)
                    ·
                      rfl

theorem cell22_1782931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 4].length) (baseStart_1782931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782931 prefixEnd_1782931 := by exact prefixLift 1782931
  have htrace : WordTrace (prefixWord ++ tailWord_1782931) baseStart_1782931 baseEnd_1782931 := by
    simpa [prefixWord, tailWord_1782931, baseEnd_1782931] using wordTrace_append hprefix tailTrace_1782931
  have hstable : (prefixWord ++ tailWord_1782931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782931).length < 2 ^ (prefixWord ++ tailWord_1782931).sum := by decide
  have hdescent : baseEnd_1782931 < baseStart_1782931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782963 : List Nat := [1, 1, 1, 2, 3, 2, 6, 2, 4]
def baseStart_1782963 : Nat := 118140960795 + 1782963 * 2 ^ 59
def prefixEnd_1782963 : Nat := 4983230072969 + 3 ^ 40 * 1782963 * 2
def baseEnd_1782963 : Nat := 203448224040536196169513

theorem tailTrace_1782963 : CollatzResearch.WordTrace tailWord_1782963 prefixEnd_1782963 203448224040536196169513 := by
  unfold tailWord_1782963
  simp only [CollatzResearch.WordTrace]
  refine ⟨65030003039637031682561543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43353335359758021121707695 65030003039637031682561543)
  ·
    refine ⟨97545004559455547523842315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65030003039637031682561543 97545004559455547523842315)
    ·
      refine ⟨146317506839183321285763473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97545004559455547523842315 146317506839183321285763473)
      ·
        refine ⟨109738130129387490964322605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146317506839183321285763473 109738130129387490964322605)
        ·
          refine ⟨41151798798520309111620977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109738130129387490964322605 41151798798520309111620977)
          ·
            refine ⟨30863849098890231833715733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41151798798520309111620977 30863849098890231833715733)
            ·
              refine ⟨1446742926510479617205425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30863849098890231833715733 1446742926510479617205425)
              ·
                refine ⟨1085057194882859712904069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1446742926510479617205425 1085057194882859712904069)
                ·
                  refine ⟨203448224040536196169513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1085057194882859712904069 203448224040536196169513)
                  ·
                    rfl

theorem cell22_1782963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 4].length) (baseStart_1782963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1782963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1782963 prefixEnd_1782963 := by exact prefixLift 1782963
  have htrace : WordTrace (prefixWord ++ tailWord_1782963) baseStart_1782963 baseEnd_1782963 := by
    simpa [prefixWord, tailWord_1782963, baseEnd_1782963] using wordTrace_append hprefix tailTrace_1782963
  have hstable : (prefixWord ++ tailWord_1782963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782963).length < 2 ^ (prefixWord ++ tailWord_1782963).sum := by decide
  have hdescent : baseEnd_1782963 < baseStart_1782963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783042 : List Nat := [3, 4, 1, 1, 4, 1, 2, 6]
def baseStart_1783042 : Nat := 118140960795 + 1783042 * 2 ^ 59
def prefixEnd_1783042 : Nat := 4983230072969 + 3 ^ 40 * 1783042 * 2
def baseEnd_1783042 : Nat := 67819079492897635087033

theorem tailTrace_1783042 : CollatzResearch.WordTrace tailWord_1783042 prefixEnd_1783042 67819079492897635087033 := by
  unfold tailWord_1783042
  simp only [CollatzResearch.WordTrace]
  refine ⟨16258221101587707043671845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43355256270900552116458253 16258221101587707043671845)
  ·
    refine ⟨3048416456547695070688471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16258221101587707043671845 3048416456547695070688471)
    ·
      refine ⟨4572624684821542606032707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3048416456547695070688471 4572624684821542606032707)
      ·
        refine ⟨6858937027232313909049061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4572624684821542606032707 6858937027232313909049061)
        ·
          refine ⟨1286050692606058857946699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6858937027232313909049061 1286050692606058857946699)
          ·
            refine ⟨1929076038909088286920049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286050692606058857946699 1929076038909088286920049)
            ·
              refine ⟨1446807029181816215190037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1929076038909088286920049 1446807029181816215190037)
              ·
                refine ⟨67819079492897635087033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1446807029181816215190037 67819079492897635087033)
                ·
                  rfl

theorem cell22_1783042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 6].length) (baseStart_1783042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783042 prefixEnd_1783042 := by exact prefixLift 1783042
  have htrace : WordTrace (prefixWord ++ tailWord_1783042) baseStart_1783042 baseEnd_1783042 := by
    simpa [prefixWord, tailWord_1783042, baseEnd_1783042] using wordTrace_append hprefix tailTrace_1783042
  have hstable : (prefixWord ++ tailWord_1783042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783042).length < 2 ^ (prefixWord ++ tailWord_1783042).sum := by decide
  have hdescent : baseEnd_1783042 < baseStart_1783042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783074 : List Nat := [3, 3, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_1783074 : Nat := 118140960795 + 1783074 * 2 ^ 59
def prefixEnd_1783074 : Nat := 4983230072969 + 3 ^ 40 * 1783074 * 2
def baseEnd_1783074 : Nat := 610382669690041298983199

theorem tailTrace_1783074 : CollatzResearch.WordTrace tailWord_1783074 prefixEnd_1783074 610382669690041298983199 := by
  unfold tailWord_1783074
  simp only [CollatzResearch.WordTrace]
  refine ⟨16258512885558724409963069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43356034361489931759901517 16258512885558724409963069)
  ·
    refine ⟨6096942332084521653736151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16258512885558724409963069 6096942332084521653736151)
    ·
      refine ⟨9145413498126782480604227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6096942332084521653736151 9145413498126782480604227)
      ·
        refine ⟨13718120247190173720906341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9145413498126782480604227 13718120247190173720906341)
        ·
          refine ⟨2572147546348157572669939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13718120247190173720906341 2572147546348157572669939)
          ·
            refine ⟨3858221319522236359004909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2572147546348157572669939 3858221319522236359004909)
            ·
              refine ⟨1446832994820838634626841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3858221319522236359004909 1446832994820838634626841)
              ·
                refine ⟨1085124746115628975970131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1446832994820838634626841 1085124746115628975970131)
                ·
                  refine ⟨1627687119173443463955197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085124746115628975970131 1627687119173443463955197)
                  ·
                    refine ⟨610382669690041298983199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1627687119173443463955197 610382669690041298983199)
                    ·
                      rfl

theorem cell22_1783074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_1783074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783074 prefixEnd_1783074 := by exact prefixLift 1783074
  have htrace : WordTrace (prefixWord ++ tailWord_1783074) baseStart_1783074 baseEnd_1783074 := by
    simpa [prefixWord, tailWord_1783074, baseEnd_1783074] using wordTrace_append hprefix tailTrace_1783074
  have hstable : (prefixWord ++ tailWord_1783074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783074).length < 2 ^ (prefixWord ++ tailWord_1783074).sum := by decide
  have hdescent : baseEnd_1783074 < baseStart_1783074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783096 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 1, 5]
def baseStart_1783096 : Nat := 118140960795 + 1783096 * 2 ^ 59
def prefixEnd_1783096 : Nat := 4983230072969 + 3 ^ 40 * 1783096 * 2
def baseEnd_1783096 : Nat := 610390200739640574933131

theorem tailTrace_1783096 : CollatzResearch.WordTrace tailWord_1783096 prefixEnd_1783096 610390200739640574933131 := by
  unfold tailWord_1783096
  simp only [CollatzResearch.WordTrace]
  refine ⟨32517426974077597698576571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43356569298770130264768761 32517426974077597698576571)
  ·
    refine ⟨48776140461116396547864857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32517426974077597698576571 48776140461116396547864857)
    ·
      refine ⟨36582105345837297410898643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48776140461116396547864857 36582105345837297410898643)
      ·
        refine ⟨54873158018755946116347965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36582105345837297410898643 54873158018755946116347965)
        ·
          refine ⟨20577434257033479793630487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54873158018755946116347965 20577434257033479793630487)
          ·
            refine ⟨30866151385550219690445731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20577434257033479793630487 30866151385550219690445731)
            ·
              refine ⟨46299227078325329535668597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30866151385550219690445731 46299227078325329535668597)
              ·
                refine ⟨4340552538592999643968931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46299227078325329535668597 4340552538592999643968931)
                ·
                  refine ⟨6510828807889499465953397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340552538592999643968931 6510828807889499465953397)
                  ·
                    refine ⟨610390200739640574933131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6510828807889499465953397 610390200739640574933131)
                    ·
                      rfl

theorem cell22_1783096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_1783096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783096 prefixEnd_1783096 := by exact prefixLift 1783096
  have htrace : WordTrace (prefixWord ++ tailWord_1783096) baseStart_1783096 baseEnd_1783096 := by
    simpa [prefixWord, tailWord_1783096, baseEnd_1783096] using wordTrace_append hprefix tailTrace_1783096
  have hstable : (prefixWord ++ tailWord_1783096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783096).length < 2 ^ (prefixWord ++ tailWord_1783096).sum := by decide
  have hdescent : baseEnd_1783096 < baseStart_1783096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783100 : List Nat := [2, 2, 2, 2, 1, 5, 1, 2, 1, 4]
def baseStart_1783100 : Nat := 118140960795 + 1783100 * 2 ^ 59
def prefixEnd_1783100 : Nat := 4983230072969 + 3 ^ 40 * 1783100 * 2
def baseEnd_1783100 : Nat := 610391570021385897833119

theorem tailTrace_1783100 : CollatzResearch.WordTrace tailWord_1783100 prefixEnd_1783100 610391570021385897833119 := by
  unfold tailWord_1783100
  simp only [CollatzResearch.WordTrace]
  refine ⟨32517499920070352040149377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43356666560093802720199169 32517499920070352040149377)
  ·
    refine ⟨24388124940052764030112033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32517499920070352040149377 24388124940052764030112033)
    ·
      refine ⟨18291093705039573022584025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24388124940052764030112033 18291093705039573022584025)
      ·
        refine ⟨13718320278779679766938019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18291093705039573022584025 13718320278779679766938019)
        ·
          refine ⟨20577480418169519650407029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13718320278779679766938019 20577480418169519650407029)
          ·
            refine ⟨1929138789203392467225659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20577480418169519650407029 1929138789203392467225659)
            ·
              refine ⟨2893708183805088700838489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1929138789203392467225659 2893708183805088700838489)
              ·
                refine ⟨2170281137853816525628867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2893708183805088700838489 2170281137853816525628867)
                ·
                  refine ⟨3255421706780724788443301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2170281137853816525628867 3255421706780724788443301)
                  ·
                    refine ⟨610391570021385897833119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3255421706780724788443301 610391570021385897833119)
                    ·
                      rfl

theorem cell22_1783100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_1783100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783100 prefixEnd_1783100 := by exact prefixLift 1783100
  have htrace : WordTrace (prefixWord ++ tailWord_1783100) baseStart_1783100 baseEnd_1783100 := by
    simpa [prefixWord, tailWord_1783100, baseEnd_1783100] using wordTrace_append hprefix tailTrace_1783100
  have hstable : (prefixWord ++ tailWord_1783100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783100).length < 2 ^ (prefixWord ++ tailWord_1783100).sum := by decide
  have hdescent : baseEnd_1783100 < baseStart_1783100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783192 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 3, 3]
def baseStart_1783192 : Nat := 118140960795 + 1783192 * 2 ^ 59
def prefixEnd_1783192 : Nat := 4983230072969 + 3 ^ 40 * 1783192 * 2
def baseEnd_1783192 : Nat := 610423063501528324532837

theorem tailTrace_1783192 : CollatzResearch.WordTrace tailWord_1783192 prefixEnd_1783192 610423063501528324532837 := by
  unfold tailWord_1783192
  simp only [CollatzResearch.WordTrace]
  refine ⟨32519177677903701896323915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43358903570538269195098553 32519177677903701896323915)
  ·
    refine ⟨48778766516855552844485873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32519177677903701896323915 48778766516855552844485873)
    ·
      refine ⟨36584074887641664633364405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48778766516855552844485873 36584074887641664633364405)
      ·
        refine ⟨3429757020716406059377913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36584074887641664633364405 3429757020716406059377913)
        ·
          refine ⟨2572317765537304544533435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3429757020716406059377913 2572317765537304544533435)
          ·
            refine ⟨3858476648305956816800153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2572317765537304544533435 3858476648305956816800153)
            ·
              refine ⟨2893857486229467612600115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3858476648305956816800153 2893857486229467612600115)
              ·
                refine ⟨4340786229344201418900173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2893857486229467612600115 4340786229344201418900173)
                ·
                  refine ⟨1627794836004075532087565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4340786229344201418900173 1627794836004075532087565)
                  ·
                    refine ⟨610423063501528324532837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1627794836004075532087565 610423063501528324532837)
                    ·
                      rfl

theorem cell22_1783192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_1783192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783192 prefixEnd_1783192 := by exact prefixLift 1783192
  have htrace : WordTrace (prefixWord ++ tailWord_1783192) baseStart_1783192 baseEnd_1783192 := by
    simpa [prefixWord, tailWord_1783192, baseEnd_1783192] using wordTrace_append hprefix tailTrace_1783192
  have hstable : (prefixWord ++ tailWord_1783192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783192).length < 2 ^ (prefixWord ++ tailWord_1783192).sum := by decide
  have hdescent : baseEnd_1783192 < baseStart_1783192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783216 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 8]
def baseStart_1783216 : Nat := 118140960795 + 1783216 * 2 ^ 59
def prefixEnd_1783216 : Nat := 4983230072969 + 3 ^ 40 * 1783216 * 2
def baseEnd_1783216 : Nat := 203477093064000087310921

theorem tailTrace_1783216 : CollatzResearch.WordTrace tailWord_1783216 prefixEnd_1783216 203477093064000087310921 := by
  unfold tailWord_1783216
  simp only [CollatzResearch.WordTrace]
  refine ⟨32519615353860227945760751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43359487138480303927681001 32519615353860227945760751)
  ·
    refine ⟨48779423030790341918641127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32519615353860227945760751 48779423030790341918641127)
    ·
      refine ⟨73169134546185512877961691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48779423030790341918641127 73169134546185512877961691)
      ·
        refine ⟨109753701819278269316942537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73169134546185512877961691 109753701819278269316942537)
        ·
          refine ⟨82315276364458701987706903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109753701819278269316942537 82315276364458701987706903)
          ·
            refine ⟨123472914546688052981560355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82315276364458701987706903 123472914546688052981560355)
            ·
              refine ⟨185209371820032079472340533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123472914546688052981560355 185209371820032079472340533)
              ·
                refine ⟨17363378608128007450531925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185209371820032079472340533 17363378608128007450531925)
                ·
                  refine ⟨203477093064000087310921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17363378608128007450531925 203477093064000087310921)
                  ·
                    rfl

theorem cell22_1783216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 8].length) (baseStart_1783216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783216 prefixEnd_1783216 := by exact prefixLift 1783216
  have htrace : WordTrace (prefixWord ++ tailWord_1783216) baseStart_1783216 baseEnd_1783216 := by
    simpa [prefixWord, tailWord_1783216, baseEnd_1783216] using wordTrace_append hprefix tailTrace_1783216
  have hstable : (prefixWord ++ tailWord_1783216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783216).length < 2 ^ (prefixWord ++ tailWord_1783216).sum := by decide
  have hdescent : baseEnd_1783216 < baseStart_1783216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783263 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 4, 4]
def baseStart_1783263 : Nat := 118140960795 + 1783263 * 2 ^ 59
def prefixEnd_1783263 : Nat := 4983230072969 + 3 ^ 40 * 1783263 * 2
def baseEnd_1783263 : Nat := 610447368252507806007619

theorem tailTrace_1783263 : CollatzResearch.WordTrace tailWord_1783263 prefixEnd_1783263 610447368252507806007619 := by
  unfold tailWord_1783263
  simp only [CollatzResearch.WordTrace]
  refine ⟨65040944938550182918482443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43360629959033455278988295 65040944938550182918482443)
  ·
    refine ⟨97561417407825274377723665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65040944938550182918482443 97561417407825274377723665)
    ·
      refine ⟨73171063055868955783292749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97561417407825274377723665 73171063055868955783292749)
      ·
        refine ⟨27439148645950858418734781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73171063055868955783292749 27439148645950858418734781)
        ·
          refine ⟨10289680742231571907025543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27439148645950858418734781 10289680742231571907025543)
          ·
            refine ⟨15434521113347357860538315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10289680742231571907025543 15434521113347357860538315)
            ·
              refine ⟨23151781670021036790807473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15434521113347357860538315 23151781670021036790807473)
              ·
                refine ⟨17363836252515777593105605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23151781670021036790807473 17363836252515777593105605)
                ·
                  refine ⟨3255719297346708298707301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17363836252515777593105605 3255719297346708298707301)
                  ·
                    refine ⟨610447368252507806007619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3255719297346708298707301 610447368252507806007619)
                    ·
                      rfl

theorem cell22_1783263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_1783263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783263 prefixEnd_1783263 := by exact prefixLift 1783263
  have htrace : WordTrace (prefixWord ++ tailWord_1783263) baseStart_1783263 baseEnd_1783263 := by
    simpa [prefixWord, tailWord_1783263, baseEnd_1783263] using wordTrace_append hprefix tailTrace_1783263
  have hstable : (prefixWord ++ tailWord_1783263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783263).length < 2 ^ (prefixWord ++ tailWord_1783263).sum := by decide
  have hdescent : baseEnd_1783263 < baseStart_1783263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783278 : List Nat := [4, 1, 2, 1, 2, 1, 1, 10]
def baseStart_1783278 : Nat := 118140960795 + 1783278 * 2 ^ 59
def prefixEnd_1783278 : Nat := 4983230072969 + 3 ^ 40 * 1783278 * 2
def baseEnd_1783278 : Nat := 67828055895450307431397

theorem tailTrace_1783278 : CollatzResearch.WordTrace tailWord_1783278 prefixEnd_1783278 67828055895450307431397 := by
  unfold tailWord_1783278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8130186504186980060034811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43360994688997226986852325 8130186504186980060034811)
  ·
    refine ⟨12195279756280470090052217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8130186504186980060034811 12195279756280470090052217)
    ·
      refine ⟨9146459817210352567539163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12195279756280470090052217 9146459817210352567539163)
      ·
        refine ⟨13719689725815528851308745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9146459817210352567539163 13719689725815528851308745)
        ·
          refine ⟨10289767294361646638481559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13719689725815528851308745 10289767294361646638481559)
          ·
            refine ⟨15434650941542469957722339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10289767294361646638481559 15434650941542469957722339)
            ·
              refine ⟨23151976412313704936583509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15434650941542469957722339 23151976412313704936583509)
              ·
                refine ⟨67828055895450307431397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23151976412313704936583509 67828055895450307431397)
                ·
                  rfl

theorem cell22_1783278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_1783278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783278 prefixEnd_1783278 := by exact prefixLift 1783278
  have htrace : WordTrace (prefixWord ++ tailWord_1783278) baseStart_1783278 baseEnd_1783278 := by
    simpa [prefixWord, tailWord_1783278, baseEnd_1783278] using wordTrace_append hprefix tailTrace_1783278
  have hstable : (prefixWord ++ tailWord_1783278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783278).length < 2 ^ (prefixWord ++ tailWord_1783278).sum := by decide
  have hdescent : baseEnd_1783278 < baseStart_1783278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783280 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 2, 4]
def baseStart_1783280 : Nat := 118140960795 + 1783280 * 2 ^ 59
def prefixEnd_1783280 : Nat := 4983230072969 + 3 ^ 40 * 1783280 * 2
def baseEnd_1783280 : Nat := 610453187699925428332567

theorem tailTrace_1783280 : CollatzResearch.WordTrace tailWord_1783280 prefixEnd_1783280 610453187699925428332567 := by
  unfold tailWord_1783280
  simp only [CollatzResearch.WordTrace]
  refine ⟨32520782489744297410925647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43361043319659063214567529 32520782489744297410925647)
  ·
    refine ⟨48781173734616446116388471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32520782489744297410925647 48781173734616446116388471)
    ·
      refine ⟨73171760601924669174582707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48781173734616446116388471 73171760601924669174582707)
      ·
        refine ⟨109757640902887003761874061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73171760601924669174582707 109757640902887003761874061)
        ·
          refine ⟨41159115338582626410702773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109757640902887003761874061 41159115338582626410702773)
          ·
            refine ⟨3858667062992121226003385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41159115338582626410702773 3858667062992121226003385)
            ·
              refine ⟨2894000297244090919502539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3858667062992121226003385 2894000297244090919502539)
              ·
                refine ⟨4341000445866136379253809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894000297244090919502539 4341000445866136379253809)
                ·
                  refine ⟨3255750334399602284440357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4341000445866136379253809 3255750334399602284440357)
                  ·
                    refine ⟨610453187699925428332567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3255750334399602284440357 610453187699925428332567)
                    ·
                      rfl

theorem cell22_1783280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_1783280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783280 prefixEnd_1783280 := by exact prefixLift 1783280
  have htrace : WordTrace (prefixWord ++ tailWord_1783280) baseStart_1783280 baseEnd_1783280 := by
    simpa [prefixWord, tailWord_1783280, baseEnd_1783280] using wordTrace_append hprefix tailTrace_1783280
  have hstable : (prefixWord ++ tailWord_1783280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783280).length < 2 ^ (prefixWord ++ tailWord_1783280).sum := by decide
  have hdescent : baseEnd_1783280 < baseStart_1783280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783417 : List Nat := [1, 2, 1, 3, 3, 1, 2, 4, 2, 3]
def baseStart_1783417 : Nat := 118140960795 + 1783417 * 2 ^ 59
def prefixEnd_1783417 : Nat := 4983230072969 + 3 ^ 40 * 1783417 * 2
def baseEnd_1783417 : Nat := 610500085599702737657147

theorem tailTrace_1783417 : CollatzResearch.WordTrace tailWord_1783417 prefixEnd_1783417 610500085599702737657147 := by
  unfold tailWord_1783417
  simp only [CollatzResearch.WordTrace]
  refine ⟨65046561779992267219588505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43364374519994844813059003 65046561779992267219588505)
  ·
    refine ⟨48784921334994200414691379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65046561779992267219588505 48784921334994200414691379)
    ·
      refine ⟨73177382002491300622037069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48784921334994200414691379 73177382002491300622037069)
      ·
        refine ⟨27441518250934237733263901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73177382002491300622037069 27441518250934237733263901)
        ·
          refine ⟨10290569344100339149973963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27441518250934237733263901 10290569344100339149973963)
          ·
            refine ⟨15435854016150508724960945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10290569344100339149973963 15435854016150508724960945)
            ·
              refine ⟨11576890512112881543720709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15435854016150508724960945 11576890512112881543720709)
              ·
                refine ⟨2170666971021165289447633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11576890512112881543720709 2170666971021165289447633)
                ·
                  refine ⟨1628000228265873967085725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2170666971021165289447633 1628000228265873967085725)
                  ·
                    refine ⟨610500085599702737657147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1628000228265873967085725 610500085599702737657147)
                    ·
                      rfl

theorem cell22_1783417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 3].length) (baseStart_1783417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783417 prefixEnd_1783417 := by exact prefixLift 1783417
  have htrace : WordTrace (prefixWord ++ tailWord_1783417) baseStart_1783417 baseEnd_1783417 := by
    simpa [prefixWord, tailWord_1783417, baseEnd_1783417] using wordTrace_append hprefix tailTrace_1783417
  have hstable : (prefixWord ++ tailWord_1783417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783417).length < 2 ^ (prefixWord ++ tailWord_1783417).sum := by decide
  have hdescent : baseEnd_1783417 < baseStart_1783417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783434 : List Nat := [3, 1, 2, 3, 2, 2, 1, 3, 2, 3]
def baseStart_1783434 : Nat := 118140960795 + 1783434 * 2 ^ 59
def prefixEnd_1783434 : Nat := 4983230072969 + 3 ^ 40 * 1783434 * 2
def baseEnd_1783434 : Nat := 610505905047120359982095

theorem tailTrace_1783434 : CollatzResearch.WordTrace tailWord_1783434 prefixEnd_1783434 610505905047120359982095 := by
  unfold tailWord_1783434
  simp only [CollatzResearch.WordTrace]
  refine ⟨16261795455232669780739339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43364787880620452748638237 16261795455232669780739339)
  ·
    refine ⟨24392693182849004671109009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16261795455232669780739339 24392693182849004671109009)
    ·
      refine ⟨18294519887136753503331757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24392693182849004671109009 18294519887136753503331757)
      ·
        refine ⟨6860444957676282563749409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18294519887136753503331757 6860444957676282563749409)
        ·
          refine ⟨5145333718257211922812057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6860444957676282563749409 5145333718257211922812057)
          ·
            refine ⟨3859000288692908942109043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5145333718257211922812057 3859000288692908942109043)
            ·
              refine ⟨5788500433039363413163565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3859000288692908942109043 5788500433039363413163565)
              ·
                refine ⟨2170687662389761279936337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5788500433039363413163565 2170687662389761279936337)
                ·
                  refine ⟨1628015746792320959952253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2170687662389761279936337 1628015746792320959952253)
                  ·
                    refine ⟨610505905047120359982095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1628015746792320959952253 610505905047120359982095)
                    ·
                      rfl

theorem cell22_1783434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_1783434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783434 prefixEnd_1783434 := by exact prefixLift 1783434
  have htrace : WordTrace (prefixWord ++ tailWord_1783434) baseStart_1783434 baseEnd_1783434 := by
    simpa [prefixWord, tailWord_1783434, baseEnd_1783434] using wordTrace_append hprefix tailTrace_1783434
  have hstable : (prefixWord ++ tailWord_1783434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783434).length < 2 ^ (prefixWord ++ tailWord_1783434).sum := by decide
  have hdescent : baseEnd_1783434 < baseStart_1783434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783464 : List Nat := [2, 1, 7, 1, 1, 10]
def baseStart_1783464 : Nat := 118140960795 + 1783464 * 2 ^ 59
def prefixEnd_1783464 : Nat := 4983230072969 + 3 ^ 40 * 1783464 * 2
def baseEnd_1783464 : Nat := 7537236724200126934963

theorem tailTrace_1783464 : CollatzResearch.WordTrace tailWord_1783464 prefixEnd_1783464 7537236724200126934963 := by
  unfold tailWord_1783464
  simp only [CollatzResearch.WordTrace]
  refine ⟨32524138005410997123274723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43365517340547996164366297 32524138005410997123274723)
  ·
    refine ⟨48786207008116495684912085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32524138005410997123274723 48786207008116495684912085)
    ·
      refine ⟨1143426726752730367615127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 48786207008116495684912085 1143426726752730367615127)
      ·
        refine ⟨1715140090129095551422691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143426726752730367615127 1715140090129095551422691)
        ·
          refine ⟨2572710135193643327134037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715140090129095551422691 2572710135193643327134037)
          ·
            refine ⟨7537236724200126934963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2572710135193643327134037 7537236724200126934963)
            ·
              rfl

theorem cell22_1783464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 10].length) (baseStart_1783464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783464 prefixEnd_1783464 := by exact prefixLift 1783464
  have htrace : WordTrace (prefixWord ++ tailWord_1783464) baseStart_1783464 baseEnd_1783464 := by
    simpa [prefixWord, tailWord_1783464, baseEnd_1783464] using wordTrace_append hprefix tailTrace_1783464
  have hstable : (prefixWord ++ tailWord_1783464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783464).length < 2 ^ (prefixWord ++ tailWord_1783464).sum := by decide
  have hdescent : baseEnd_1783464 < baseStart_1783464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783470 : List Nat := [4, 1, 4, 1, 3, 1, 2, 2, 4]
def baseStart_1783470 : Nat := 118140960795 + 1783470 * 2 ^ 59
def prefixEnd_1783470 : Nat := 4983230072969 + 3 ^ 40 * 1783470 * 2
def baseEnd_1783470 : Nat := 203506076194276088693995

theorem tailTrace_1783470 : CollatzResearch.WordTrace tailWord_1783470 prefixEnd_1783470 203506076194276088693995 := by
  unfold tailWord_1783470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8131061856100032158908483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43365663232533504847511909 8131061856100032158908483)
  ·
    refine ⟨12196592784150048238362725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8131061856100032158908483 12196592784150048238362725)
    ·
      refine ⟨2286861147028134044693011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12196592784150048238362725 2286861147028134044693011)
      ·
        refine ⟨3430291720542201067039517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2286861147028134044693011 3430291720542201067039517)
        ·
          refine ⟨1286359395203325400139819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3430291720542201067039517 1286359395203325400139819)
          ·
            refine ⟨1929539092804988100209729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286359395203325400139819 1929539092804988100209729)
            ·
              refine ⟨1447154319603741075157297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1929539092804988100209729 1447154319603741075157297)
              ·
                refine ⟨1085365739702805806367973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1447154319603741075157297 1085365739702805806367973)
                ·
                  refine ⟨203506076194276088693995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1085365739702805806367973 203506076194276088693995)
                  ·
                    rfl

theorem cell22_1783470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_1783470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783470 prefixEnd_1783470 := by exact prefixLift 1783470
  have htrace : WordTrace (prefixWord ++ tailWord_1783470) baseStart_1783470 baseEnd_1783470 := by
    simpa [prefixWord, tailWord_1783470, baseEnd_1783470] using wordTrace_append hprefix tailTrace_1783470
  have hstable : (prefixWord ++ tailWord_1783470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783470).length < 2 ^ (prefixWord ++ tailWord_1783470).sum := by decide
  have hdescent : baseEnd_1783470 < baseStart_1783470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783492 : List Nat := [2, 3, 3, 1, 1, 1, 1, 5, 5]
def baseStart_1783492 : Nat := 118140960795 + 1783492 * 2 ^ 59
def prefixEnd_1783492 : Nat := 4983230072969 + 3 ^ 40 * 1783492 * 2
def baseEnd_1783492 : Nat := 203508586544142514010639

theorem tailTrace_1783492 : CollatzResearch.WordTrace tailWord_1783492 prefixEnd_1783492 203508586544142514010639 := by
  unfold tailWord_1783492
  simp only [CollatzResearch.WordTrace]
  refine ⟨32524648627360277514284365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43366198169813703352379153 32524648627360277514284365)
  ·
    refine ⟨12196743235260104067856637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32524648627360277514284365 12196743235260104067856637)
    ·
      refine ⟨4573778713222539025446239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12196743235260104067856637 4573778713222539025446239)
      ·
        refine ⟨6860668069833808538169359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4573778713222539025446239 6860668069833808538169359)
        ·
          refine ⟨10291002104750712807254039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6860668069833808538169359 10291002104750712807254039)
          ·
            refine ⟨15436503157126069210881059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10291002104750712807254039 15436503157126069210881059)
            ·
              refine ⟨23154754735689103816321589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15436503157126069210881059 23154754735689103816321589)
              ·
                refine ⟨2170758256470853482780149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23154754735689103816321589 2170758256470853482780149)
                ·
                  refine ⟨203508586544142514010639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2170758256470853482780149 203508586544142514010639)
                  ·
                    rfl

theorem cell22_1783492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_1783492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783492 prefixEnd_1783492 := by exact prefixLift 1783492
  have htrace : WordTrace (prefixWord ++ tailWord_1783492) baseStart_1783492 baseEnd_1783492 := by
    simpa [prefixWord, tailWord_1783492, baseEnd_1783492] using wordTrace_append hprefix tailTrace_1783492
  have hstable : (prefixWord ++ tailWord_1783492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783492).length < 2 ^ (prefixWord ++ tailWord_1783492).sum := by decide
  have hdescent : baseEnd_1783492 < baseStart_1783492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783537 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 6]
def baseStart_1783537 : Nat := 118140960795 + 1783537 * 2 ^ 59
def prefixEnd_1783537 : Nat := 4983230072969 + 3 ^ 40 * 1783537 * 2
def baseEnd_1783537 : Nat := 203513721350687474885593

theorem tailTrace_1783537 : CollatzResearch.WordTrace tailWord_1783537 prefixEnd_1783537 203513721350687474885593 := by
  unfold tailWord_1783537
  simp only [CollatzResearch.WordTrace]
  refine ⟨65050938539557527713956865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43367292359705018475971243 65050938539557527713956865)
  ·
    refine ⟨48788203904668145785467649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65050938539557527713956865 48788203904668145785467649)
    ·
      refine ⟨36591152928501109339100737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48788203904668145785467649 36591152928501109339100737)
      ·
        refine ⟨27443364696375832004325553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36591152928501109339100737 27443364696375832004325553)
        ·
          refine ⟨20582523522281874003244165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27443364696375832004325553 20582523522281874003244165)
          ·
            refine ⟨3859223160427851375608281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20582523522281874003244165 3859223160427851375608281)
            ·
              refine ⟨2894417370320888531706211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3859223160427851375608281 2894417370320888531706211)
              ·
                refine ⟨4341626055481332797559317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894417370320888531706211 4341626055481332797559317)
                ·
                  refine ⟨203513721350687474885593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4341626055481332797559317 203513721350687474885593)
                  ·
                    rfl

theorem cell22_1783537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 6].length) (baseStart_1783537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783537 prefixEnd_1783537 := by exact prefixLift 1783537
  have htrace : WordTrace (prefixWord ++ tailWord_1783537) baseStart_1783537 baseEnd_1783537 := by
    simpa [prefixWord, tailWord_1783537, baseEnd_1783537] using wordTrace_append hprefix tailTrace_1783537
  have hstable : (prefixWord ++ tailWord_1783537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783537).length < 2 ^ (prefixWord ++ tailWord_1783537).sum := by decide
  have hdescent : baseEnd_1783537 < baseStart_1783537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783603 : List Nat := [1, 1, 1, 2, 7, 2, 2, 1, 2, 3]
def baseStart_1783603 : Nat := 118140960795 + 1783603 * 2 ^ 59
def prefixEnd_1783603 : Nat := 4983230072969 + 3 ^ 40 * 1783603 * 2
def baseEnd_1783603 : Nat := 610563757200860252506577

theorem tailTrace_1783603 : CollatzResearch.WordTrace tailWord_1783603 prefixEnd_1783603 610563757200860252506577 := by
  unfold tailWord_1783603
  simp only [CollatzResearch.WordTrace]
  refine ⟨65053345757318420985859463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43368897171545613990572975 65053345757318420985859463)
  ·
    refine ⟨97580018635977631478789195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65053345757318420985859463 97580018635977631478789195)
    ·
      refine ⟨146370027953966447218183793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97580018635977631478789195 146370027953966447218183793)
      ·
        refine ⟨109777520965474835413637845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146370027953966447218183793 109777520965474835413637845)
        ·
          refine ⟨2572910647628316455007137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 109777520965474835413637845 2572910647628316455007137)
          ·
            refine ⟨1929682985721237341255353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2572910647628316455007137 1929682985721237341255353)
            ·
              refine ⟨1447262239290928005941515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1929682985721237341255353 1447262239290928005941515)
              ·
                refine ⟨2170893358936392008912273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1447262239290928005941515 2170893358936392008912273)
                ·
                  refine ⟨1628170019202294006684205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2170893358936392008912273 1628170019202294006684205)
                  ·
                    refine ⟨610563757200860252506577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1628170019202294006684205 610563757200860252506577)
                    ·
                      rfl

theorem cell22_1783603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 2, 3].length) (baseStart_1783603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783603 prefixEnd_1783603 := by exact prefixLift 1783603
  have htrace : WordTrace (prefixWord ++ tailWord_1783603) baseStart_1783603 baseEnd_1783603 := by
    simpa [prefixWord, tailWord_1783603, baseEnd_1783603] using wordTrace_append hprefix tailTrace_1783603
  have hstable : (prefixWord ++ tailWord_1783603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783603).length < 2 ^ (prefixWord ++ tailWord_1783603).sum := by decide
  have hdescent : baseEnd_1783603 < baseStart_1783603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783642 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 2, 5]
def baseStart_1783642 : Nat := 118140960795 + 1783642 * 2 ^ 59
def prefixEnd_1783642 : Nat := 4983230072969 + 3 ^ 40 * 1783642 * 2
def baseEnd_1783642 : Nat := 610577107697877150781457

theorem tailTrace_1783642 : CollatzResearch.WordTrace tailWord_1783642 prefixEnd_1783642 610577107697877150781457 := by
  unfold tailWord_1783642
  simp only [CollatzResearch.WordTrace]
  refine ⟨16263692051044282661632295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43369845469451420431019453 16263692051044282661632295)
  ·
    refine ⟨24395538076566423992448443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16263692051044282661632295 24395538076566423992448443)
    ·
      refine ⟨36593307114849635988672665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24395538076566423992448443 36593307114849635988672665)
      ·
        refine ⟨27444980336137226991504499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36593307114849635988672665 27444980336137226991504499)
        ·
          refine ⟨41167470504205840487256749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27444980336137226991504499 41167470504205840487256749)
          ·
            refine ⟨15437801439077190182721281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41167470504205840487256749 15437801439077190182721281)
            ·
              refine ⟨11578351079307892637040961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15437801439077190182721281 11578351079307892637040961)
              ·
                refine ⟨8683763309480919477780721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11578351079307892637040961 8683763309480919477780721)
                ·
                  refine ⟨6512822482110689608335541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8683763309480919477780721 6512822482110689608335541)
                  ·
                    refine ⟨610577107697877150781457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6512822482110689608335541 610577107697877150781457)
                    ·
                      rfl

theorem cell22_1783642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_1783642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783642 prefixEnd_1783642 := by exact prefixLift 1783642
  have htrace : WordTrace (prefixWord ++ tailWord_1783642) baseStart_1783642 baseEnd_1783642 := by
    simpa [prefixWord, tailWord_1783642, baseEnd_1783642] using wordTrace_append hprefix tailTrace_1783642
  have hstable : (prefixWord ++ tailWord_1783642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783642).length < 2 ^ (prefixWord ++ tailWord_1783642).sum := by decide
  have hdescent : baseEnd_1783642 < baseStart_1783642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783648 : List Nat := [2, 1, 1, 3, 3, 2, 4, 2, 1, 3]
def baseStart_1783648 : Nat := 118140960795 + 1783648 * 2 ^ 59
def prefixEnd_1783648 : Nat := 4983230072969 + 3 ^ 40 * 1783648 * 2
def baseEnd_1783648 : Nat := 610579161620495135131439

theorem tailTrace_1783648 : CollatzResearch.WordTrace tailWord_1783648 prefixEnd_1783648 610579161620495135131439 := by
  unfold tailWord_1783648
  simp only [CollatzResearch.WordTrace]
  refine ⟨32527493521077696835623799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43369991361436929114165065 32527493521077696835623799)
  ·
    refine ⟨48791240281616545253435699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32527493521077696835623799 48791240281616545253435699)
    ·
      refine ⟨73186860422424817880153549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48791240281616545253435699 73186860422424817880153549)
      ·
        refine ⟨27445072658409306705057581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73186860422424817880153549 27445072658409306705057581)
        ·
          refine ⟨10291902246903490014396593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27445072658409306705057581 10291902246903490014396593)
          ·
            refine ⟨7718926685177617510797445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10291902246903490014396593 7718926685177617510797445)
            ·
              refine ⟨1447298753470803283274521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7718926685177617510797445 1447298753470803283274521)
              ·
                refine ⟨1085474065103102462455891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1447298753470803283274521 1085474065103102462455891)
                ·
                  refine ⟨1628211097654653693683837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085474065103102462455891 1628211097654653693683837)
                  ·
                    refine ⟨610579161620495135131439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1628211097654653693683837 610579161620495135131439)
                    ·
                      rfl

theorem cell22_1783648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 1, 3].length) (baseStart_1783648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783648 prefixEnd_1783648 := by exact prefixLift 1783648
  have htrace : WordTrace (prefixWord ++ tailWord_1783648) baseStart_1783648 baseEnd_1783648 := by
    simpa [prefixWord, tailWord_1783648, baseEnd_1783648] using wordTrace_append hprefix tailTrace_1783648
  have hstable : (prefixWord ++ tailWord_1783648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783648).length < 2 ^ (prefixWord ++ tailWord_1783648).sum := by decide
  have hdescent : baseEnd_1783648 < baseStart_1783648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783706 : List Nat := [3, 1, 1, 4, 2, 1, 2, 4, 4]
def baseStart_1783706 : Nat := 118140960795 + 1783706 * 2 ^ 59
def prefixEnd_1783706 : Nat := 4983230072969 + 3 ^ 40 * 1783706 * 2
def baseEnd_1783706 : Nat := 203533005401934105727087

theorem tailTrace_1783706 : CollatzResearch.WordTrace tailWord_1783706 prefixEnd_1783706 203533005401934105727087 := by
  unfold tailWord_1783706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16264275618986317394214743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43371401650630179717905981 16264275618986317394214743)
  ·
    refine ⟨24396413428479476091322115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16264275618986317394214743 24396413428479476091322115)
    ·
      refine ⟨36594620142719214136983173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24396413428479476091322115 36594620142719214136983173)
      ·
        refine ⟨6861491276759852650684345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36594620142719214136983173 6861491276759852650684345)
        ·
          refine ⟨5146118457569889488013259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6861491276759852650684345 5146118457569889488013259)
          ·
            refine ⟨7719177686354834232019889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5146118457569889488013259 7719177686354834232019889)
            ·
              refine ⟨5789383264766125674014917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7719177686354834232019889 5789383264766125674014917)
              ·
                refine ⟨1085509362143648563877797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5789383264766125674014917 1085509362143648563877797)
                ·
                  refine ⟨203533005401934105727087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1085509362143648563877797 203533005401934105727087)
                  ·
                    rfl

theorem cell22_1783706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_1783706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783706 prefixEnd_1783706 := by exact prefixLift 1783706
  have htrace : WordTrace (prefixWord ++ tailWord_1783706) baseStart_1783706 baseEnd_1783706 := by
    simpa [prefixWord, tailWord_1783706, baseEnd_1783706] using wordTrace_append hprefix tailTrace_1783706
  have hstable : (prefixWord ++ tailWord_1783706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783706).length < 2 ^ (prefixWord ++ tailWord_1783706).sum := by decide
  have hdescent : baseEnd_1783706 < baseStart_1783706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783719 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1783719 : Nat := 118140960795 + 1783719 * 2 ^ 59
def prefixEnd_1783719 : Nat := 4983230072969 + 3 ^ 40 * 1783719 * 2
def baseEnd_1783719 : Nat := 610603466371474616606221

theorem tailTrace_1783719 : CollatzResearch.WordTrace tailWord_1783719 prefixEnd_1783719 610603466371474616606221 := by
  unfold tailWord_1783719
  simp only [CollatzResearch.WordTrace]
  refine ⟨65057576624898172797082211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43371717749932115198054807 65057576624898172797082211)
  ·
    refine ⟨97586364937347259195623317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65057576624898172797082211 97586364937347259195623317)
    ·
      refine ⟨4574360856438152774794843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97586364937347259195623317 4574360856438152774794843)
      ·
        refine ⟨6861541284657229162192265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4574360856438152774794843 6861541284657229162192265)
        ·
          refine ⟨5146155963492921871644199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6861541284657229162192265 5146155963492921871644199)
          ·
            refine ⟨7719233945239382807466299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5146155963492921871644199 7719233945239382807466299)
            ·
              refine ⟨11578850917859074211199449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7719233945239382807466299 11578850917859074211199449)
              ·
                refine ⟨8684138188394305658399587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11578850917859074211199449 8684138188394305658399587)
                ·
                  refine ⟨13026207282591458487599381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8684138188394305658399587 13026207282591458487599381)
                  ·
                    refine ⟨610603466371474616606221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13026207282591458487599381 610603466371474616606221)
                    ·
                      rfl

theorem cell22_1783719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1783719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783719 prefixEnd_1783719 := by exact prefixLift 1783719
  have htrace : WordTrace (prefixWord ++ tailWord_1783719) baseStart_1783719 baseEnd_1783719 := by
    simpa [prefixWord, tailWord_1783719, baseEnd_1783719] using wordTrace_append hprefix tailTrace_1783719
  have hstable : (prefixWord ++ tailWord_1783719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783719).length < 2 ^ (prefixWord ++ tailWord_1783719).sum := by decide
  have hdescent : baseEnd_1783719 < baseStart_1783719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783740 : List Nat := [2, 2, 2, 5, 1, 2, 1, 3, 4]
def baseStart_1783740 : Nat := 118140960795 + 1783740 * 2 ^ 59
def prefixEnd_1783740 : Nat := 4983230072969 + 3 ^ 40 * 1783740 * 2
def baseEnd_1783740 : Nat := 203536885033545853943719

theorem tailTrace_1783740 : CollatzResearch.WordTrace tailWord_1783740 prefixEnd_1783740 203536885033545853943719 := by
  unfold tailWord_1783740
  simp only [CollatzResearch.WordTrace]
  refine ⟨32529171278911046691798337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43372228371881395589064449 32529171278911046691798337)
  ·
    refine ⟨24396878459183285018848753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32529171278911046691798337 24396878459183285018848753)
    ·
      refine ⟨18297658844387463764136565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24396878459183285018848753 18297658844387463764136565)
      ·
        refine ⟨1715405516661324727887803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18297658844387463764136565 1715405516661324727887803)
        ·
          refine ⟨2573108274991987091831705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715405516661324727887803 2573108274991987091831705)
          ·
            refine ⟨1929831206243990318873779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2573108274991987091831705 1929831206243990318873779)
            ·
              refine ⟨2894746809365985478310669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1929831206243990318873779 2894746809365985478310669)
              ·
                refine ⟨1085530053512244554366501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2894746809365985478310669 1085530053512244554366501)
                ·
                  refine ⟨203536885033545853943719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1085530053512244554366501 203536885033545853943719)
                  ·
                    rfl

theorem cell22_1783740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_1783740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783740 prefixEnd_1783740 := by exact prefixLift 1783740
  have htrace : WordTrace (prefixWord ++ tailWord_1783740) baseStart_1783740 baseEnd_1783740 := by
    simpa [prefixWord, tailWord_1783740, baseEnd_1783740] using wordTrace_append hprefix tailTrace_1783740
  have hstable : (prefixWord ++ tailWord_1783740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783740).length < 2 ^ (prefixWord ++ tailWord_1783740).sum := by decide
  have hdescent : baseEnd_1783740 < baseStart_1783740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783764 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_1783764 : Nat := 118140960795 + 1783764 * 2 ^ 59
def prefixEnd_1783764 : Nat := 4983230072969 + 3 ^ 40 * 1783764 * 2
def baseEnd_1783764 : Nat := 610618870791109499231083

theorem tailTrace_1783764 : CollatzResearch.WordTrace tailWord_1783764 prefixEnd_1783764 610618870791109499231083 := by
  unfold tailWord_1783764
  simp only [CollatzResearch.WordTrace]
  refine ⟨32529608954867572741235173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43372811939823430321646897 32529608954867572741235173)
  ·
    refine ⟨6099301679037669888981595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32529608954867572741235173 6099301679037669888981595)
    ·
      refine ⟨9148952518556504833472393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6099301679037669888981595 9148952518556504833472393)
      ·
        refine ⟨6861714388917378625104295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9148952518556504833472393 6861714388917378625104295)
        ·
          refine ⟨10292571583376067937656443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6861714388917378625104295 10292571583376067937656443)
          ·
            refine ⟨15438857375064101906484665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10292571583376067937656443 15438857375064101906484665)
            ·
              refine ⟨11579143031298076429863499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15438857375064101906484665 11579143031298076429863499)
              ·
                refine ⟨17368714546947114644795249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11579143031298076429863499 17368714546947114644795249)
                ·
                  refine ⟨13026535910210335983596437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17368714546947114644795249 13026535910210335983596437)
                  ·
                    refine ⟨610618870791109499231083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13026535910210335983596437 610618870791109499231083)
                    ·
                      rfl

theorem cell22_1783764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_1783764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783764 prefixEnd_1783764 := by exact prefixLift 1783764
  have htrace : WordTrace (prefixWord ++ tailWord_1783764) baseStart_1783764 baseEnd_1783764 := by
    simpa [prefixWord, tailWord_1783764, baseEnd_1783764] using wordTrace_append hprefix tailTrace_1783764
  have hstable : (prefixWord ++ tailWord_1783764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783764).length < 2 ^ (prefixWord ++ tailWord_1783764).sum := by decide
  have hdescent : baseEnd_1783764 < baseStart_1783764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783772 : List Nat := [2, 2, 6, 1, 1, 1, 1, 3, 2, 3]
def baseStart_1783772 : Nat := 118140960795 + 1783772 * 2 ^ 59
def prefixEnd_1783772 : Nat := 4983230072969 + 3 ^ 40 * 1783772 * 2
def baseEnd_1783772 : Nat := 610621609354600145031059

theorem tailTrace_1783772 : CollatzResearch.WordTrace tailWord_1783772 prefixEnd_1783772 610621609354600145031059 := by
  unfold tailWord_1783772
  simp only [CollatzResearch.WordTrace]
  refine ⟨32529754846853081424380785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43373006462470775232507713 32529754846853081424380785)
  ·
    refine ⟨24397316135139811068285589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32529754846853081424380785 24397316135139811068285589)
    ·
      refine ⟨1143624193834678643825887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24397316135139811068285589 1143624193834678643825887)
      ·
        refine ⟨1715436290752017965738831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143624193834678643825887 1715436290752017965738831)
        ·
          refine ⟨2573154436128026948608247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715436290752017965738831 2573154436128026948608247)
          ·
            refine ⟨3859731654192040422912371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573154436128026948608247 3859731654192040422912371)
            ·
              refine ⟨5789597481288060634368557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3859731654192040422912371 5789597481288060634368557)
              ·
                refine ⟨2171099055483022737888209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5789597481288060634368557 2171099055483022737888209)
                ·
                  refine ⟨1628324291612267053416157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2171099055483022737888209 1628324291612267053416157)
                  ·
                    refine ⟨610621609354600145031059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1628324291612267053416157 610621609354600145031059)
                    ·
                      rfl

theorem cell22_1783772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_1783772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783772 prefixEnd_1783772 := by exact prefixLift 1783772
  have htrace : WordTrace (prefixWord ++ tailWord_1783772) baseStart_1783772 baseEnd_1783772 := by
    simpa [prefixWord, tailWord_1783772, baseEnd_1783772] using wordTrace_append hprefix tailTrace_1783772
  have hstable : (prefixWord ++ tailWord_1783772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783772).length < 2 ^ (prefixWord ++ tailWord_1783772).sum := by decide
  have hdescent : baseEnd_1783772 < baseStart_1783772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783841 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 6]
def baseStart_1783841 : Nat := 118140960795 + 1783841 * 2 ^ 59
def prefixEnd_1783841 : Nat := 4983230072969 + 3 ^ 40 * 1783841 * 2
def baseEnd_1783841 : Nat := 203548409821568988351949

theorem tailTrace_1783841 : CollatzResearch.WordTrace tailWord_1783841 prefixEnd_1783841 203548409821568988351949 := by
  unfold tailWord_1783841
  simp only [CollatzResearch.WordTrace]
  refine ⟨65062026330456187633023377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43374684220304125088682251 65062026330456187633023377)
  ·
    refine ⟨48796519747842140724767533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65062026330456187633023377 48796519747842140724767533)
    ·
      refine ⟨18298694905440802771787825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48796519747842140724767533 18298694905440802771787825)
      ·
        refine ⟨13724021179080602078840869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18298694905440802771787825 13724021179080602078840869)
        ·
          refine ⟨2573253971077612889782663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13724021179080602078840869 2573253971077612889782663)
          ·
            refine ⟨3859880956616419334673995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573253971077612889782663 3859880956616419334673995)
            ·
              refine ⟨5789821434924629002010993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3859880956616419334673995 5789821434924629002010993)
              ·
                refine ⟨4342366076193471751508245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5789821434924629002010993 4342366076193471751508245)
                ·
                  refine ⟨203548409821568988351949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4342366076193471751508245 203548409821568988351949)
                  ·
                    rfl

theorem cell22_1783841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 6].length) (baseStart_1783841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783841 prefixEnd_1783841 := by exact prefixLift 1783841
  have htrace : WordTrace (prefixWord ++ tailWord_1783841) baseStart_1783841 baseEnd_1783841 := by
    simpa [prefixWord, tailWord_1783841, baseEnd_1783841] using wordTrace_append hprefix tailTrace_1783841
  have hstable : (prefixWord ++ tailWord_1783841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783841).length < 2 ^ (prefixWord ++ tailWord_1783841).sum := by decide
  have hdescent : baseEnd_1783841 < baseStart_1783841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783858 : List Nat := [3, 2, 1, 1, 2, 4, 2, 3, 4]
def baseStart_1783858 : Nat := 118140960795 + 1783858 * 2 ^ 59
def prefixEnd_1783858 : Nat := 4983230072969 + 3 ^ 40 * 1783858 * 2
def baseEnd_1783858 : Nat := 203550349637374862460265

theorem tailTrace_1783858 : CollatzResearch.WordTrace tailWord_1783858 prefixEnd_1783858 203550349637374862460265 := by
  unfold tailWord_1783858
  simp only [CollatzResearch.WordTrace]
  refine ⟨16265661592848649884098057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43375097580929733024261485 16265661592848649884098057)
  ·
    refine ⟨12199246194636487413073543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16265661592848649884098057 12199246194636487413073543)
    ·
      refine ⟨18298869291954731119610315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12199246194636487413073543 18298869291954731119610315)
      ·
        refine ⟨27448303937932096679415473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18298869291954731119610315 27448303937932096679415473)
        ·
          refine ⟨20586227953449072509561605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27448303937932096679415473 20586227953449072509561605)
          ·
            refine ⟨3859917741271701095542801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20586227953449072509561605 3859917741271701095542801)
            ·
              refine ⟨2894938305953775821657101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3859917741271701095542801 2894938305953775821657101)
              ·
                refine ⟨1085601864732665933121413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2894938305953775821657101 1085601864732665933121413)
                ·
                  refine ⟨203550349637374862460265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1085601864732665933121413 203550349637374862460265)
                  ·
                    rfl

theorem cell22_1783858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_1783858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783858 prefixEnd_1783858 := by exact prefixLift 1783858
  have htrace : WordTrace (prefixWord ++ tailWord_1783858) baseStart_1783858 baseEnd_1783858 := by
    simpa [prefixWord, tailWord_1783858, baseEnd_1783858] using wordTrace_append hprefix tailTrace_1783858
  have hstable : (prefixWord ++ tailWord_1783858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783858).length < 2 ^ (prefixWord ++ tailWord_1783858).sum := by decide
  have hdescent : baseEnd_1783858 < baseStart_1783858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783860 : List Nat := [2, 5, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1783860 : Nat := 118140960795 + 1783860 * 2 ^ 59
def prefixEnd_1783860 : Nat := 4983230072969 + 3 ^ 40 * 1783860 * 2
def baseEnd_1783860 : Nat := 610651733552997248830789

theorem tailTrace_1783860 : CollatzResearch.WordTrace tailWord_1783860 prefixEnd_1783860 610651733552997248830789 := by
  unfold tailWord_1783860
  simp only [CollatzResearch.WordTrace]
  refine ⟨32531359658693676938982517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43375146211591569251976689 32531359658693676938982517)
  ·
    refine ⟨3049814968002532213029611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32531359658693676938982517 3049814968002532213029611)
    ·
      refine ⟨4574722452003798319544417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3049814968002532213029611 4574722452003798319544417)
      ·
        refine ⟨3431041839002848739658313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4574722452003798319544417 3431041839002848739658313)
        ·
          refine ⟨2573281379252136554743735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3431041839002848739658313 2573281379252136554743735)
          ·
            refine ⟨3859922068878204832115603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573281379252136554743735 3859922068878204832115603)
            ·
              refine ⟨5789883103317307248173405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3859922068878204832115603 5789883103317307248173405)
              ·
                refine ⟨2171206163743990218065027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5789883103317307248173405 2171206163743990218065027)
                ·
                  refine ⟨3256809245615985327097541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2171206163743990218065027 3256809245615985327097541)
                  ·
                    refine ⟨610651733552997248830789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3256809245615985327097541 610651733552997248830789)
                    ·
                      rfl

theorem cell22_1783860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1783860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783860 prefixEnd_1783860 := by exact prefixLift 1783860
  have htrace : WordTrace (prefixWord ++ tailWord_1783860) baseStart_1783860 baseEnd_1783860 := by
    simpa [prefixWord, tailWord_1783860, baseEnd_1783860] using wordTrace_append hprefix tailTrace_1783860
  have hstable : (prefixWord ++ tailWord_1783860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783860).length < 2 ^ (prefixWord ++ tailWord_1783860).sum := by decide
  have hdescent : baseEnd_1783860 < baseStart_1783860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783869 : List Nat := [1, 4, 1, 3, 1, 1, 11]
def baseStart_1783869 : Nat := 118140960795 + 1783869 * 2 ^ 59
def prefixEnd_1783869 : Nat := 4983230072969 + 3 ^ 40 * 1783869 * 2
def baseEnd_1783869 : Nat := 22616844979145341679843

theorem tailTrace_1783869 : CollatzResearch.WordTrace tailWord_1783869 prefixEnd_1783869 22616844979145341679843 := by
  unfold tailWord_1783869
  simp only [CollatzResearch.WordTrace]
  refine ⟨65063047574354748415042661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43375365049569832276695107 65063047574354748415042661)
  ·
    refine ⟨12199321420191515327820499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65063047574354748415042661 12199321420191515327820499)
    ·
      refine ⟨18298982130287272991730749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12199321420191515327820499 18298982130287272991730749)
      ·
        refine ⟨6862118298857727371899031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18298982130287272991730749 6862118298857727371899031)
        ·
          refine ⟨10293177448286591057848547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6862118298857727371899031 10293177448286591057848547)
          ·
            refine ⟨15439766172429886586772821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10293177448286591057848547 15439766172429886586772821)
            ·
              refine ⟨22616844979145341679843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15439766172429886586772821 22616844979145341679843)
              ·
                rfl

theorem cell22_1783869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 11].length) (baseStart_1783869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783869 prefixEnd_1783869 := by exact prefixLift 1783869
  have htrace : WordTrace (prefixWord ++ tailWord_1783869) baseStart_1783869 baseEnd_1783869 := by
    simpa [prefixWord, tailWord_1783869, baseEnd_1783869] using wordTrace_append hprefix tailTrace_1783869
  have hstable : (prefixWord ++ tailWord_1783869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783869).length < 2 ^ (prefixWord ++ tailWord_1783869).sum := by decide
  have hdescent : baseEnd_1783869 < baseStart_1783869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783873 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1783873 : Nat := 118140960795 + 1783873 * 2 ^ 59
def prefixEnd_1783873 : Nat := 4983230072969 + 3 ^ 40 * 1783873 * 2
def baseEnd_1783873 : Nat := 610656183718669548255749

theorem tailTrace_1783873 : CollatzResearch.WordTrace tailWord_1783873 prefixEnd_1783873 610656183718669548255749 := by
  unfold tailWord_1783873
  simp only [CollatzResearch.WordTrace]
  refine ⟨65063193466340257098188273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43375462310893504732125515 65063193466340257098188273)
  ·
    refine ⟨48797395099755192823641205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65063193466340257098188273 48797395099755192823641205)
    ·
      refine ⟨4574755790602049327216363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48797395099755192823641205 4574755790602049327216363)
      ·
        refine ⟨6862133685903073990824545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4574755790602049327216363 6862133685903073990824545)
        ·
          refine ⟨5146600264427305493118409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6862133685903073990824545 5146600264427305493118409)
          ·
            refine ⟨3859950198320479119838807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5146600264427305493118409 3859950198320479119838807)
            ·
              refine ⟨5789925297480718679758211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3859950198320479119838807 5789925297480718679758211)
              ·
                refine ⟨8684887946221078019637317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5789925297480718679758211 8684887946221078019637317)
                ·
                  refine ⟨1628416489916452128681997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8684887946221078019637317 1628416489916452128681997)
                  ·
                    refine ⟨610656183718669548255749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1628416489916452128681997 610656183718669548255749)
                    ·
                      rfl

theorem cell22_1783873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1783873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783873 prefixEnd_1783873 := by exact prefixLift 1783873
  have htrace : WordTrace (prefixWord ++ tailWord_1783873) baseStart_1783873 baseEnd_1783873 := by
    simpa [prefixWord, tailWord_1783873, baseEnd_1783873] using wordTrace_append hprefix tailTrace_1783873
  have hstable : (prefixWord ++ tailWord_1783873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783873).length < 2 ^ (prefixWord ++ tailWord_1783873).sum := by decide
  have hdescent : baseEnd_1783873 < baseStart_1783873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783890 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 1, 5]
def baseStart_1783890 : Nat := 118140960795 + 1783890 * 2 ^ 59
def prefixEnd_1783890 : Nat := 4983230072969 + 3 ^ 40 * 1783890 * 2
def baseEnd_1783890 : Nat := 610662003166087170580697

theorem tailTrace_1783890 : CollatzResearch.WordTrace tailWord_1783890 prefixEnd_1783890 610662003166087170580697 := by
  unfold tailWord_1783890
  simp only [CollatzResearch.WordTrace]
  refine ⟨16265953376819667250389281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43375875671519112667704749 16265953376819667250389281)
  ·
    refine ⟨12199465032614750437791961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16265953376819667250389281 12199465032614750437791961)
    ·
      refine ⟨9149598774461062828343971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12199465032614750437791961 9149598774461062828343971)
      ·
        refine ⟨13724398161691594242515957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9149598774461062828343971 13724398161691594242515957)
        ·
          refine ⟨1286662327658586960235871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13724398161691594242515957 1286662327658586960235871)
          ·
            refine ⟨1929993491487880440353807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286662327658586960235871 1929993491487880440353807)
            ·
              refine ⟨2894990237231820660530711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1929993491487880440353807 2894990237231820660530711)
              ·
                refine ⟨4342485355847730990796067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894990237231820660530711 4342485355847730990796067)
                ·
                  refine ⟨6513728033771596486194101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4342485355847730990796067 6513728033771596486194101)
                  ·
                    refine ⟨610662003166087170580697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6513728033771596486194101 610662003166087170580697)
                    ·
                      rfl

theorem cell22_1783890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_1783890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783890 prefixEnd_1783890 := by exact prefixLift 1783890
  have htrace : WordTrace (prefixWord ++ tailWord_1783890) baseStart_1783890 baseEnd_1783890 := by
    simpa [prefixWord, tailWord_1783890, baseEnd_1783890] using wordTrace_append hprefix tailTrace_1783890
  have hstable : (prefixWord ++ tailWord_1783890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783890).length < 2 ^ (prefixWord ++ tailWord_1783890).sum := by decide
  have hdescent : baseEnd_1783890 < baseStart_1783890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783982 : List Nat := [4, 1, 4, 2, 1, 1, 2, 2, 5]
def baseStart_1783982 : Nat := 118140960795 + 1783982 * 2 ^ 59
def prefixEnd_1783982 : Nat := 4983230072969 + 3 ^ 40 * 1783982 * 2
def baseEnd_1783982 : Nat := 203564498882076532426805

theorem tailTrace_1783982 : CollatzResearch.WordTrace tailWord_1783982 prefixEnd_1783982 203564498882076532426805 := by
  unfold tailWord_1783982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8133396127868171089238275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43378112681963579142604133 8133396127868171089238275)
  ·
    refine ⟨12200094191802256633857413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8133396127868171089238275 12200094191802256633857413)
    ·
      refine ⟨2287517660962923118848265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12200094191802256633857413 2287517660962923118848265)
      ·
        refine ⟨1715638245722192339136199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2287517660962923118848265 1715638245722192339136199)
        ·
          refine ⟨2573457368583288508704299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715638245722192339136199 2573457368583288508704299)
          ·
            refine ⟨3860186052874932763056449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573457368583288508704299 3860186052874932763056449)
            ·
              refine ⟨2895139539656199572292337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3860186052874932763056449 2895139539656199572292337)
              ·
                refine ⟨2171354654742149679219253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2895139539656199572292337 2171354654742149679219253)
                ·
                  refine ⟨203564498882076532426805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2171354654742149679219253 203564498882076532426805)
                  ·
                    rfl

theorem cell22_1783982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_1783982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783982 prefixEnd_1783982 := by exact prefixLift 1783982
  have htrace : WordTrace (prefixWord ++ tailWord_1783982) baseStart_1783982 baseEnd_1783982 := by
    simpa [prefixWord, tailWord_1783982, baseEnd_1783982] using wordTrace_append hprefix tailTrace_1783982
  have hstable : (prefixWord ++ tailWord_1783982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783982).length < 2 ^ (prefixWord ++ tailWord_1783982).sum := by decide
  have hdescent : baseEnd_1783982 < baseStart_1783982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783993 : List Nat := [1, 2, 1, 4, 1, 2, 3, 4, 4]
def baseStart_1783993 : Nat := 118140960795 + 1783993 * 2 ^ 59
def prefixEnd_1783993 : Nat := 4983230072969 + 3 ^ 40 * 1783993 * 2
def baseEnd_1783993 : Nat := 203565754057009745085127

theorem tailTrace_1783993 : CollatzResearch.WordTrace tailWord_1783993 prefixEnd_1783993 203565754057009745085127 := by
  unfold tailWord_1783993
  simp only [CollatzResearch.WordTrace]
  refine ⟨65067570225905517592556633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43378380150603678395037755 65067570225905517592556633)
  ·
    refine ⟨48800677669429138194417475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65067570225905517592556633 48800677669429138194417475)
    ·
      refine ⟨73201016504143707291626213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48800677669429138194417475 73201016504143707291626213)
      ·
        refine ⟨13725190594526945117179915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73201016504143707291626213 13725190594526945117179915)
        ·
          refine ⟨20587785891790417675769873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13725190594526945117179915 20587785891790417675769873)
          ·
            refine ⟨15440839418842813256827405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20587785891790417675769873 15440839418842813256827405)
            ·
              refine ⟨5790314782066054971310277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15440839418842813256827405 5790314782066054971310277)
              ·
                refine ⟨1085684021637385307120677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5790314782066054971310277 1085684021637385307120677)
                ·
                  refine ⟨203565754057009745085127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1085684021637385307120677 203565754057009745085127)
                  ·
                    rfl

theorem cell22_1783993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 4].length) (baseStart_1783993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1783993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1783993 prefixEnd_1783993 := by exact prefixLift 1783993
  have htrace : WordTrace (prefixWord ++ tailWord_1783993) baseStart_1783993 baseEnd_1783993 := by
    simpa [prefixWord, tailWord_1783993, baseEnd_1783993] using wordTrace_append hprefix tailTrace_1783993
  have hstable : (prefixWord ++ tailWord_1783993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783993).length < 2 ^ (prefixWord ++ tailWord_1783993).sum := by decide
  have hdescent : baseEnd_1783993 < baseStart_1783993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784087 : List Nat := [1, 1, 3, 4, 1, 2, 3, 3, 1, 3]
def baseStart_1784087 : Nat := 118140960795 + 1784087 * 2 ^ 59
def prefixEnd_1784087 : Nat := 4983230072969 + 3 ^ 40 * 1784087 * 2
def baseEnd_1784087 : Nat := 610729440292044323405093

theorem tailTrace_1784087 : CollatzResearch.WordTrace tailWord_1784087 prefixEnd_1784087 610729440292044323405093 := by
  unfold tailWord_1784087
  simp only [CollatzResearch.WordTrace]
  refine ⟨65070998687564971646478515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43380665791709981097652343 65070998687564971646478515)
  ·
    refine ⟨97606498031347457469717773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65070998687564971646478515 97606498031347457469717773)
    ·
      refine ⟨36602436761755296551144165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97606498031347457469717773 36602436761755296551144165)
      ·
        refine ⟨6862956892829118103339531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36602436761755296551144165 6862956892829118103339531)
        ·
          refine ⟨10294435339243677155009297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6862956892829118103339531 10294435339243677155009297)
          ·
            refine ⟨7720826504432757866256973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10294435339243677155009297 7720826504432757866256973)
            ·
              refine ⟨2895309939162284199846365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7720826504432757866256973 2895309939162284199846365)
              ·
                refine ⟨1085741227185856574942387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2895309939162284199846365 1085741227185856574942387)
                ·
                  refine ⟨1628611840778784862413581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085741227185856574942387 1628611840778784862413581)
                  ·
                    refine ⟨610729440292044323405093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1628611840778784862413581 610729440292044323405093)
                    ·
                      rfl

theorem cell22_1784087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_1784087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784087 prefixEnd_1784087 := by exact prefixLift 1784087
  have htrace : WordTrace (prefixWord ++ tailWord_1784087) baseStart_1784087 baseEnd_1784087 := by
    simpa [prefixWord, tailWord_1784087, baseEnd_1784087] using wordTrace_append hprefix tailTrace_1784087
  have hstable : (prefixWord ++ tailWord_1784087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784087).length < 2 ^ (prefixWord ++ tailWord_1784087).sum := by decide
  have hdescent : baseEnd_1784087 < baseStart_1784087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784104 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 3, 3]
def baseStart_1784104 : Nat := 118140960795 + 1784104 * 2 ^ 59
def prefixEnd_1784104 : Nat := 4983230072969 + 3 ^ 40 * 1784104 * 2
def baseEnd_1784104 : Nat := 610735259739461945730041

theorem tailTrace_1784104 : CollatzResearch.WordTrace tailWord_1784104 prefixEnd_1784104 610735259739461945730041 := by
  unfold tailWord_1784104
  simp only [CollatzResearch.WordTrace]
  refine ⟨32535809364251691774923683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43381079152335589033231577 32535809364251691774923683)
  ·
    refine ⟨48803714046377537662385525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32535809364251691774923683 48803714046377537662385525)
    ·
      refine ⟨4575348191847894155848643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48803714046377537662385525 4575348191847894155848643)
      ·
        refine ⟨6863022287771841233772965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4575348191847894155848643 6863022287771841233772965)
        ·
          refine ⟨1286816678957220231332431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6863022287771841233772965 1286816678957220231332431)
          ·
            refine ⟨1930225018435830346998647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286816678957220231332431 1930225018435830346998647)
            ·
              refine ⟨2895337527653745520497971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1930225018435830346998647 2895337527653745520497971)
              ·
                refine ⟨4343006291480618280746957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2895337527653745520497971 4343006291480618280746957)
                ·
                  refine ⟨1628627359305231855280109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4343006291480618280746957 1628627359305231855280109)
                  ·
                    refine ⟨610735259739461945730041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1628627359305231855280109 610735259739461945730041)
                    ·
                      rfl

theorem cell22_1784104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_1784104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1784104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1784104 prefixEnd_1784104 := by exact prefixLift 1784104
  have htrace : WordTrace (prefixWord ++ tailWord_1784104) baseStart_1784104 baseEnd_1784104 := by
    simpa [prefixWord, tailWord_1784104, baseEnd_1784104] using wordTrace_append hprefix tailTrace_1784104
  have hstable : (prefixWord ++ tailWord_1784104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784104).length < 2 ^ (prefixWord ++ tailWord_1784104).sum := by decide
  have hdescent : baseEnd_1784104 < baseStart_1784104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
