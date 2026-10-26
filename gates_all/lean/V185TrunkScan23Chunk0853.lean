import V185TrunkScan23Chunk0852

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5048307 : List Nat := [1, 1, 1, 2, 2, 2, 1, 8, 1, 2, 2]
def baseStart_5048307 : Nat := 118140960795 + 5048307 * 2 ^ 59
def prefixEnd_5048307 : Nat := 4983230072969 + 3 ^ 40 * 5048307 * 2
def baseEnd_5048307 : Nat := 2592207982457285209345765

theorem tailTrace_5048307 : CollatzResearch.WordTrace tailWord_5048307 prefixEnd_5048307 2592207982457285209345765 := by
  unfold tailWord_5048307
  simp only [CollatzResearch.WordTrace]
  refine ⟨184126882921853396038879175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122751255281235597359252783 184126882921853396038879175)
  ·
    refine ⟨276190324382780094058318763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184126882921853396038879175 276190324382780094058318763)
    ·
      refine ⟨414285486574170141087478145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276190324382780094058318763 414285486574170141087478145)
      ·
        refine ⟨310714114930627605815608609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414285486574170141087478145 310714114930627605815608609)
        ·
          refine ⟨233035586197970704361706457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310714114930627605815608609 233035586197970704361706457)
          ·
            refine ⟨174776689648478028271279843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233035586197970704361706457 174776689648478028271279843)
            ·
              refine ⟨262165034472717042406919765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174776689648478028271279843 262165034472717042406919765)
              ·
                refine ⟨3072246497727152840706091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 262165034472717042406919765 3072246497727152840706091)
                ·
                  refine ⟨4608369746590729261059137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072246497727152840706091 4608369746590729261059137)
                  ·
                    refine ⟨3456277309943046945794353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4608369746590729261059137 3456277309943046945794353)
                    ·
                      refine ⟨2592207982457285209345765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3456277309943046945794353 2592207982457285209345765)
                      ·
                        rfl

theorem cell23_5048307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 1, 2, 2].length) (baseStart_5048307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048307 prefixEnd_5048307 := by exact prefixLift 5048307
  have htrace : WordTrace (prefixWord ++ tailWord_5048307) baseStart_5048307 baseEnd_5048307 := by
    simpa [prefixWord, tailWord_5048307, baseEnd_5048307] using wordTrace_append hprefix tailTrace_5048307
  have hstable : (prefixWord ++ tailWord_5048307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048307).length < 2 ^ (prefixWord ++ tailWord_5048307).sum := by decide
  have hdescent : baseEnd_5048307 < baseStart_5048307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048316 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_5048316 : Nat := 118140960795 + 5048316 * 2 ^ 59
def prefixEnd_5048316 : Nat := 4983230072969 + 3 ^ 40 * 5048316 * 2
def baseEnd_5048316 : Nat := 2592212603783175674133223

theorem tailTrace_5048316 : CollatzResearch.WordTrace tailWord_5048316 prefixEnd_5048316 2592212603783175674133223 := by
  unfold tailWord_5048316
  simp only [CollatzResearch.WordTrace]
  refine ⟨92063605589410395287978401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122751474119213860383971201 92063605589410395287978401)
  ·
    refine ⟨69047704192057796465983801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92063605589410395287978401 69047704192057796465983801)
    ·
      refine ⟨51785778144043347349487851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69047704192057796465983801 51785778144043347349487851)
      ·
        refine ⟨77678667216065021024231777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51785778144043347349487851 77678667216065021024231777)
        ·
          refine ⟨58259000412048765768173833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77678667216065021024231777 58259000412048765768173833)
          ·
            refine ⟨43694250309036574326130375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58259000412048765768173833 43694250309036574326130375)
            ·
              refine ⟨65541375463554861489195563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43694250309036574326130375 65541375463554861489195563)
              ·
                refine ⟨98312063195332292233793345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65541375463554861489195563 98312063195332292233793345)
                ·
                  refine ⟨73734047396499219175345009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98312063195332292233793345 73734047396499219175345009)
                  ·
                    refine ⟨55300535547374414381508757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73734047396499219175345009 55300535547374414381508757)
                    ·
                      refine ⟨2592212603783175674133223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55300535547374414381508757 2592212603783175674133223)
                      ·
                        rfl

theorem cell23_5048316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_5048316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048316 prefixEnd_5048316 := by exact prefixLift 5048316
  have htrace : WordTrace (prefixWord ++ tailWord_5048316) baseStart_5048316 baseEnd_5048316 := by
    simpa [prefixWord, tailWord_5048316, baseEnd_5048316] using wordTrace_append hprefix tailTrace_5048316
  have hstable : (prefixWord ++ tailWord_5048316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048316).length < 2 ^ (prefixWord ++ tailWord_5048316).sum := by decide
  have hdescent : baseEnd_5048316 < baseStart_5048316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048324 : List Nat := [2, 3, 2, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_5048324 : Nat := 118140960795 + 5048324 * 2 ^ 59
def prefixEnd_5048324 : Nat := 4983230072969 + 3 ^ 40 * 5048324 * 2
def baseEnd_5048324 : Nat := 2592216711628411642833187

theorem tailTrace_5048324 : CollatzResearch.WordTrace tailWord_5048324 prefixEnd_5048324 2592216711628411642833187 := by
  unfold tailWord_5048324
  simp only [CollatzResearch.WordTrace]
  refine ⟨92063751481395903971124013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122751668641861205294832017 92063751481395903971124013)
  ·
    refine ⟨34523906805523463989171505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92063751481395903971124013 34523906805523463989171505)
    ·
      refine ⟨25892930104142597991878629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34523906805523463989171505 25892930104142597991878629)
      ·
        refine ⟨4854924394526737123477243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25892930104142597991878629 4854924394526737123477243)
        ·
          refine ⟨7282386591790105685215865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4854924394526737123477243 7282386591790105685215865)
          ·
            refine ⟨5461789943842579263911899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7282386591790105685215865 5461789943842579263911899)
            ·
              refine ⟨8192684915763868895867849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5461789943842579263911899 8192684915763868895867849)
              ·
                refine ⟨6144513686822901671900887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8192684915763868895867849 6144513686822901671900887)
                ·
                  refine ⟨9216770530234352507851331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6144513686822901671900887 9216770530234352507851331)
                  ·
                    refine ⟨13825155795351528761776997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9216770530234352507851331 13825155795351528761776997)
                    ·
                      refine ⟨2592216711628411642833187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13825155795351528761776997 2592216711628411642833187)
                      ·
                        rfl

theorem cell23_5048324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_5048324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048324 prefixEnd_5048324 := by exact prefixLift 5048324
  have htrace : WordTrace (prefixWord ++ tailWord_5048324) baseStart_5048324 baseEnd_5048324 := by
    simpa [prefixWord, tailWord_5048324, baseEnd_5048324] using wordTrace_append hprefix tailTrace_5048324
  have hstable : (prefixWord ++ tailWord_5048324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048324).length < 2 ^ (prefixWord ++ tailWord_5048324).sum := by decide
  have hdescent : baseEnd_5048324 < baseStart_5048324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048327 : List Nat := [1, 1, 4, 3, 1, 4, 1, 2, 1, 2, 3]
def baseStart_5048327 : Nat := 118140960795 + 5048327 * 2 ^ 59
def prefixEnd_5048327 : Nat := 4983230072969 + 3 ^ 40 * 5048327 * 2
def baseEnd_5048327 : Nat := 2592218252070375131095673

theorem tailTrace_5048327 : CollatzResearch.WordTrace tailWord_5048327 prefixEnd_5048327 2592218252070375131095673 := by
  unfold tailWord_5048327
  simp only [CollatzResearch.WordTrace]
  refine ⟨184127612381780939454607235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122751741587853959636404823 184127612381780939454607235)
  ·
    refine ⟨276191418572671409181910853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184127612381780939454607235 276191418572671409181910853)
    ·
      refine ⟨51785890982375889221608285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276191418572671409181910853 51785890982375889221608285)
      ·
        refine ⟨19419709118390958458103107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51785890982375889221608285 19419709118390958458103107)
        ·
          refine ⟨29129563677586437687154661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19419709118390958458103107 29129563677586437687154661)
          ·
            refine ⟨5461793189547457066341499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29129563677586437687154661 5461793189547457066341499)
            ·
              refine ⟨8192689784321185599512249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5461793189547457066341499 8192689784321185599512249)
              ·
                refine ⟨6144517338240889199634187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8192689784321185599512249 6144517338240889199634187)
                ·
                  refine ⟨9216776007361333799451281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6144517338240889199634187 9216776007361333799451281)
                  ·
                    refine ⟨6912582005521000349588461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9216776007361333799451281 6912582005521000349588461)
                    ·
                      refine ⟨2592218252070375131095673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6912582005521000349588461 2592218252070375131095673)
                      ·
                        rfl

theorem cell23_5048327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_5048327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048327 prefixEnd_5048327 := by exact prefixLift 5048327
  have htrace : WordTrace (prefixWord ++ tailWord_5048327) baseStart_5048327 baseEnd_5048327 := by
    simpa [prefixWord, tailWord_5048327, baseEnd_5048327] using wordTrace_append hprefix tailTrace_5048327
  have hstable : (prefixWord ++ tailWord_5048327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048327).length < 2 ^ (prefixWord ++ tailWord_5048327).sum := by decide
  have hdescent : baseEnd_5048327 < baseStart_5048327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048357 : List Nat := [1, 3, 1, 2, 2, 4, 2, 2, 2, 1, 3]
def baseStart_5048357 : Nat := 118140960795 + 5048357 * 2 ^ 59
def prefixEnd_5048357 : Nat := 4983230072969 + 3 ^ 40 * 5048357 * 2
def baseEnd_5048357 : Nat := 2592233656490010013720535

theorem tailTrace_5048357 : CollatzResearch.WordTrace tailWord_5048357 prefixEnd_5048357 2592233656490010013720535 := by
  unfold tailWord_5048357
  simp only [CollatzResearch.WordTrace]
  refine ⟨184128706571672254578199325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122752471047781503052132883 184128706571672254578199325)
  ·
    refine ⟨69048264964377095466824747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184128706571672254578199325 69048264964377095466824747)
    ·
      refine ⟨103572397446565643200237121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69048264964377095466824747 103572397446565643200237121)
      ·
        refine ⟨77679298084924232400177841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103572397446565643200237121 77679298084924232400177841)
        ·
          refine ⟨58259473563693174300133381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77679298084924232400177841 58259473563693174300133381)
          ·
            refine ⟨10923651293192470181275009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58259473563693174300133381 10923651293192470181275009)
            ·
              refine ⟨8192738469894352635956257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10923651293192470181275009 8192738469894352635956257)
              ·
                refine ⟨6144553852420764476967193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8192738469894352635956257 6144553852420764476967193)
                ·
                  refine ⟨4608415389315573357725395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6144553852420764476967193 4608415389315573357725395)
                  ·
                    refine ⟨6912623083973360036588093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4608415389315573357725395 6912623083973360036588093)
                    ·
                      refine ⟨2592233656490010013720535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6912623083973360036588093 2592233656490010013720535)
                      ·
                        rfl

theorem cell23_5048357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_5048357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048357 prefixEnd_5048357 := by exact prefixLift 5048357
  have htrace : WordTrace (prefixWord ++ tailWord_5048357) baseStart_5048357 baseEnd_5048357 := by
    simpa [prefixWord, tailWord_5048357, baseEnd_5048357] using wordTrace_append hprefix tailTrace_5048357
  have hstable : (prefixWord ++ tailWord_5048357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048357).length < 2 ^ (prefixWord ++ tailWord_5048357).sum := by decide
  have hdescent : baseEnd_5048357 < baseStart_5048357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048390 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_5048390 : Nat := 118140960795 + 5048390 * 2 ^ 59
def prefixEnd_5048390 : Nat := 4983230072969 + 3 ^ 40 * 5048390 * 2
def baseEnd_5048390 : Nat := 864083533783869461535961

theorem tailTrace_5048390 : CollatzResearch.WordTrace tailWord_5048390 prefixEnd_5048390 864083533783869461535961 := by
  unfold tailWord_5048390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5754059693142271912942207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122753273453701800809433749 5754059693142271912942207)
  ·
    refine ⟨8631089539713407869413311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5754059693142271912942207 8631089539713407869413311)
    ·
      refine ⟨12946634309570111804119967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8631089539713407869413311 12946634309570111804119967)
      ·
        refine ⟨19419951464355167706179951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12946634309570111804119967 19419951464355167706179951)
        ·
          refine ⟨29129927196532751559269927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19419951464355167706179951 29129927196532751559269927)
          ·
            refine ⟨43694890794799127338904891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29129927196532751559269927 43694890794799127338904891)
            ·
              refine ⟨65542336192198691008357337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43694890794799127338904891 65542336192198691008357337)
              ·
                refine ⟨49156752144149018256268003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65542336192198691008357337 49156752144149018256268003)
                ·
                  refine ⟨73735128216223527384402005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49156752144149018256268003 73735128216223527384402005)
                  ·
                    refine ⟨864083533783869461535961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73735128216223527384402005 864083533783869461535961)
                    ·
                      rfl

theorem cell23_5048390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_5048390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048390 prefixEnd_5048390 := by exact prefixLift 5048390
  have htrace : WordTrace (prefixWord ++ tailWord_5048390) baseStart_5048390 baseEnd_5048390 := by
    simpa [prefixWord, tailWord_5048390, baseEnd_5048390] using wordTrace_append hprefix tailTrace_5048390
  have hstable : (prefixWord ++ tailWord_5048390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048390).length < 2 ^ (prefixWord ++ tailWord_5048390).sum := by decide
  have hdescent : baseEnd_5048390 < baseStart_5048390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048397 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_5048397 : Nat := 118140960795 + 5048397 * 2 ^ 59
def prefixEnd_5048397 : Nat := 4983230072969 + 3 ^ 40 * 5048397 * 2
def baseEnd_5048397 : Nat := 2592254195716189857220351

theorem tailTrace_5048397 : CollatzResearch.WordTrace tailWord_5048397 prefixEnd_5048397 2592254195716189857220351 := by
  unfold tailWord_5048397
  simp only [CollatzResearch.WordTrace]
  refine ⟨184130165491527341409655445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122753443661018227606436963 184130165491527341409655445)
  ·
    refine ⟨8631101507415344128577599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 184130165491527341409655445 8631101507415344128577599)
    ·
      refine ⟨12946652261123016192866399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8631101507415344128577599 12946652261123016192866399)
      ·
        refine ⟨19419978391684524289299599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12946652261123016192866399 19419978391684524289299599)
        ·
          refine ⟨29129967587526786433949399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19419978391684524289299599 29129967587526786433949399)
          ·
            refine ⟨43694951381290179650924099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29129967587526786433949399 43694951381290179650924099)
            ·
              refine ⟨65542427071935269476386149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43694951381290179650924099 65542427071935269476386149)
              ·
                refine ⟨12289205075987863026822403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65542427071935269476386149 12289205075987863026822403)
                ·
                  refine ⟨18433807613981794540233605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12289205075987863026822403 18433807613981794540233605)
                  ·
                    refine ⟨3456338927621586476293801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18433807613981794540233605 3456338927621586476293801)
                    ·
                      refine ⟨2592254195716189857220351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3456338927621586476293801 2592254195716189857220351)
                      ·
                        rfl

theorem cell23_5048397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_5048397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048397 prefixEnd_5048397 := by exact prefixLift 5048397
  have htrace : WordTrace (prefixWord ++ tailWord_5048397) baseStart_5048397 baseEnd_5048397 := by
    simpa [prefixWord, tailWord_5048397, baseEnd_5048397] using wordTrace_append hprefix tailTrace_5048397
  have hstable : (prefixWord ++ tailWord_5048397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048397).length < 2 ^ (prefixWord ++ tailWord_5048397).sum := by decide
  have hdescent : baseEnd_5048397 < baseStart_5048397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048420 : List Nat := [2, 3, 1, 1, 2, 1, 4, 4, 5]
def baseStart_5048420 : Nat := 118140960795 + 5048420 * 2 ^ 59
def prefixEnd_5048420 : Nat := 4983230072969 + 3 ^ 40 * 5048420 * 2
def baseEnd_5048420 : Nat := 288029556196804807470305

theorem tailTrace_5048420 : CollatzResearch.WordTrace tailWord_5048420 prefixEnd_5048420 288029556196804807470305 := by
  unfold tailWord_5048420
  simp only [CollatzResearch.WordTrace]
  refine ⟨92065502185222008168871357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122754002913629344225161809 92065502185222008168871357)
  ·
    refine ⟨34524563319458253063326759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92065502185222008168871357 34524563319458253063326759)
    ·
      refine ⟨51786844979187379594990139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34524563319458253063326759 51786844979187379594990139)
      ·
        refine ⟨77680267468781069392485209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51786844979187379594990139 77680267468781069392485209)
        ·
          refine ⟨58260200601585802044363907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77680267468781069392485209 58260200601585802044363907)
          ·
            refine ⟨87390300902378703066545861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58260200601585802044363907 87390300902378703066545861)
            ·
              refine ⟨16385681419196006824977349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87390300902378703066545861 16385681419196006824977349)
              ·
                refine ⟨3072315266099251279683253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16385681419196006824977349 3072315266099251279683253)
                ·
                  refine ⟨288029556196804807470305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3072315266099251279683253 288029556196804807470305)
                  ·
                    rfl

theorem cell23_5048420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_5048420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048420 prefixEnd_5048420 := by exact prefixLift 5048420
  have htrace : WordTrace (prefixWord ++ tailWord_5048420) baseStart_5048420 baseEnd_5048420 := by
    simpa [prefixWord, tailWord_5048420, baseEnd_5048420] using wordTrace_append hprefix tailTrace_5048420
  have hstable : (prefixWord ++ tailWord_5048420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048420).length < 2 ^ (prefixWord ++ tailWord_5048420).sum := by decide
  have hdescent : baseEnd_5048420 < baseStart_5048420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048430 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_5048430 : Nat := 118140960795 + 5048430 * 2 ^ 59
def prefixEnd_5048430 : Nat := 4983230072969 + 3 ^ 40 * 5048430 * 2
def baseEnd_5048430 : Nat := 2592271140577788228107699

theorem tailTrace_5048430 : CollatzResearch.WordTrace tailWord_5048430 prefixEnd_5048430 2592271140577788228107699 := by
  unfold tailWord_5048430
  simp only [CollatzResearch.WordTrace]
  refine ⟨23016421137550973505700843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122754246066938525363737829 23016421137550973505700843)
  ·
    refine ⟨34524631706326460258551265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23016421137550973505700843 34524631706326460258551265)
    ·
      refine ⟨25893473779744845193913449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34524631706326460258551265 25893473779744845193913449)
      ·
        refine ⟨19420105334808633895435087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25893473779744845193913449 19420105334808633895435087)
        ·
          refine ⟨29130158002212950843152631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19420105334808633895435087 29130158002212950843152631)
          ·
            refine ⟨43695237003319426264728947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29130158002212950843152631 43695237003319426264728947)
            ·
              refine ⟨65542855504979139397093421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43695237003319426264728947 65542855504979139397093421)
              ·
                refine ⟨24578570814367177273910033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65542855504979139397093421 24578570814367177273910033)
                ·
                  refine ⟨18433928110775382955432525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24578570814367177273910033 18433928110775382955432525)
                  ·
                    refine ⟨6912723041540768608287197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18433928110775382955432525 6912723041540768608287197)
                    ·
                      refine ⟨2592271140577788228107699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6912723041540768608287197 2592271140577788228107699)
                      ·
                        rfl

theorem cell23_5048430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_5048430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048430 prefixEnd_5048430 := by exact prefixLift 5048430
  have htrace : WordTrace (prefixWord ++ tailWord_5048430) baseStart_5048430 baseEnd_5048430 := by
    simpa [prefixWord, tailWord_5048430, baseEnd_5048430] using wordTrace_append hprefix tailTrace_5048430
  have hstable : (prefixWord ++ tailWord_5048430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048430).length < 2 ^ (prefixWord ++ tailWord_5048430).sum := by decide
  have hdescent : baseEnd_5048430 < baseStart_5048430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048553 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 5, 6]
def baseStart_5048553 : Nat := 118140960795 + 5048553 * 2 ^ 59
def prefixEnd_5048553 : Nat := 4983230072969 + 3 ^ 40 * 5048553 * 2
def baseEnd_5048553 : Nat := 864111432899430415623211

theorem tailTrace_5048553 : CollatzResearch.WordTrace tailWord_5048553 prefixEnd_5048553 864111432899430415623211 := by
  unfold tailWord_5048553
  simp only [CollatzResearch.WordTrace]
  refine ⟨184135855278962180052334313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122757236852641453368222875 184135855278962180052334313)
  ·
    refine ⟨138101891459221635039250735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184135855278962180052334313 138101891459221635039250735)
    ·
      refine ⟨207152837188832452558876103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138101891459221635039250735 207152837188832452558876103)
      ·
        refine ⟨310729255783248678838314155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207152837188832452558876103 310729255783248678838314155)
        ·
          refine ⟨466093883674873018257471233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310729255783248678838314155 466093883674873018257471233)
          ·
            refine ⟨349570412756154763693103425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 466093883674873018257471233 349570412756154763693103425)
            ·
              refine ⟨262177809567116072769827569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349570412756154763693103425 262177809567116072769827569)
              ·
                refine ⟨196633357175337054577370677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262177809567116072769827569 196633357175337054577370677)
                ·
                  refine ⟨18434377235187848866628501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 196633357175337054577370677 18434377235187848866628501)
                  ·
                    refine ⟨864111432899430415623211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18434377235187848866628501 864111432899430415623211)
                    ·
                      rfl

theorem cell23_5048553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 6].length) (baseStart_5048553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048553 prefixEnd_5048553 := by exact prefixLift 5048553
  have htrace : WordTrace (prefixWord ++ tailWord_5048553) baseStart_5048553 baseEnd_5048553 := by
    simpa [prefixWord, tailWord_5048553, baseEnd_5048553] using wordTrace_append hprefix tailTrace_5048553
  have hstable : (prefixWord ++ tailWord_5048553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048553).length < 2 ^ (prefixWord ++ tailWord_5048553).sum := by decide
  have hdescent : baseEnd_5048553 < baseStart_5048553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048570 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 1, 6]
def baseStart_5048570 : Nat := 118140960795 + 5048570 * 2 ^ 59
def prefixEnd_5048570 : Nat := 4983230072969 + 3 ^ 40 * 5048570 * 2
def baseEnd_5048570 : Nat := 864114342623139226785685

theorem tailTrace_5048570 : CollatzResearch.WordTrace tailWord_5048570 prefixEnd_5048570 864114342623139226785685 := by
  unfold tailWord_5048570
  simp only [CollatzResearch.WordTrace]
  refine ⟨46034118829975147988925791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122757650213267061303802109 46034118829975147988925791)
  ·
    refine ⟨69051178244962721983388687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46034118829975147988925791 69051178244962721983388687)
    ·
      refine ⟨103576767367444082975083031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69051178244962721983388687 103576767367444082975083031)
      ·
        refine ⟨155365151051166124462624547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103576767367444082975083031 155365151051166124462624547)
        ·
          refine ⟨233047726576749186693936821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155365151051166124462624547 233047726576749186693936821)
          ·
            refine ⟨21848224366570236252556577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 233047726576749186693936821 21848224366570236252556577)
            ·
              refine ⟨16386168274927677189417433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21848224366570236252556577 16386168274927677189417433)
              ·
                refine ⟨12289626206195757892063075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16386168274927677189417433 12289626206195757892063075)
                ·
                  refine ⟨18434439309293636838094613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12289626206195757892063075 18434439309293636838094613)
                  ·
                    refine ⟨864114342623139226785685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18434439309293636838094613 864114342623139226785685)
                    ·
                      rfl

theorem cell23_5048570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_5048570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048570 prefixEnd_5048570 := by exact prefixLift 5048570
  have htrace : WordTrace (prefixWord ++ tailWord_5048570) baseStart_5048570 baseEnd_5048570 := by
    simpa [prefixWord, tailWord_5048570, baseEnd_5048570] using wordTrace_append hprefix tailTrace_5048570
  have hstable : (prefixWord ++ tailWord_5048570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048570).length < 2 ^ (prefixWord ++ tailWord_5048570).sum := by decide
  have hdescent : baseEnd_5048570 < baseStart_5048570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048577 : List Nat := [1, 2, 4, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_5048577 : Nat := 118140960795 + 5048577 * 2 ^ 59
def prefixEnd_5048577 : Nat := 4983230072969 + 3 ^ 40 * 5048577 * 2
def baseEnd_5048577 : Nat := 2592346622233999152969523

theorem tailTrace_5048577 : CollatzResearch.WordTrace tailWord_5048577 prefixEnd_5048577 2592346622233999152969523 := by
  unfold tailWord_5048577
  simp only [CollatzResearch.WordTrace]
  refine ⟨184136730630875232151207985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122757820420583488100805323 184136730630875232151207985)
  ·
    refine ⟨138102547973156424113405989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184136730630875232151207985 138102547973156424113405989)
    ·
      refine ⟨25894227744966829521263623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138102547973156424113405989 25894227744966829521263623)
      ·
        refine ⟨38841341617450244281895435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25894227744966829521263623 38841341617450244281895435)
        ·
          refine ⟨58262012426175366422843153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38841341617450244281895435 58262012426175366422843153)
          ·
            refine ⟨43696509319631524817132365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58262012426175366422843153 43696509319631524817132365)
            ·
              refine ⟨16386190994861821806424637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43696509319631524817132365 16386190994861821806424637)
              ·
                refine ⟨6144821623073183177409239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16386190994861821806424637 6144821623073183177409239)
                ·
                  refine ⟨9217232434609774766113859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6144821623073183177409239 9217232434609774766113859)
                  ·
                    refine ⟨13825848651914662149170789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9217232434609774766113859 13825848651914662149170789)
                    ·
                      refine ⟨2592346622233999152969523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13825848651914662149170789 2592346622233999152969523)
                      ·
                        rfl

theorem cell23_5048577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_5048577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048577 prefixEnd_5048577 := by exact prefixLift 5048577
  have htrace : WordTrace (prefixWord ++ tailWord_5048577) baseStart_5048577 baseEnd_5048577 := by
    simpa [prefixWord, tailWord_5048577, baseEnd_5048577] using wordTrace_append hprefix tailTrace_5048577
  have hstable : (prefixWord ++ tailWord_5048577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048577).length < 2 ^ (prefixWord ++ tailWord_5048577).sum := by decide
  have hdescent : baseEnd_5048577 < baseStart_5048577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048590 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_5048590 : Nat := 118140960795 + 5048590 * 2 ^ 59
def prefixEnd_5048590 : Nat := 4983230072969 + 3 ^ 40 * 5048590 * 2
def baseEnd_5048590 : Nat := 2592353297482507602106963

theorem tailTrace_5048590 : CollatzResearch.WordTrace tailWord_5048590 prefixEnd_5048590 2592353297482507602106963 := by
  unfold tailWord_5048590
  simp only [CollatzResearch.WordTrace]
  refine ⟨23017150597478516921428903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122758136519885423580954149 23017150597478516921428903)
  ·
    refine ⟨34525725896217775382143355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23017150597478516921428903 34525725896217775382143355)
    ·
      refine ⟨51788588844326663073215033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34525725896217775382143355 51788588844326663073215033)
      ·
        refine ⟨38841441633244997304911275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51788588844326663073215033 38841441633244997304911275)
        ·
          refine ⟨58262162449867495957366913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38841441633244997304911275 58262162449867495957366913)
          ·
            refine ⟨43696621837400621968025185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58262162449867495957366913 43696621837400621968025185)
            ·
              refine ⟨32772466378050466476018889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43696621837400621968025185 32772466378050466476018889)
              ·
                refine ⟨24579349783537849857014167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32772466378050466476018889 24579349783537849857014167)
                ·
                  refine ⟨36869024675306774785521251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24579349783537849857014167 36869024675306774785521251)
                  ·
                    refine ⟨55303537012960162178281877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36869024675306774785521251 55303537012960162178281877)
                    ·
                      refine ⟨2592353297482507602106963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55303537012960162178281877 2592353297482507602106963)
                      ·
                        rfl

theorem cell23_5048590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_5048590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048590 prefixEnd_5048590 := by exact prefixLift 5048590
  have htrace : WordTrace (prefixWord ++ tailWord_5048590) baseStart_5048590 baseEnd_5048590 := by
    simpa [prefixWord, tailWord_5048590, baseEnd_5048590] using wordTrace_append hprefix tailTrace_5048590
  have hstable : (prefixWord ++ tailWord_5048590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048590).length < 2 ^ (prefixWord ++ tailWord_5048590).sum := by decide
  have hdescent : baseEnd_5048590 < baseStart_5048590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048607 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 4]
def baseStart_5048607 : Nat := 118140960795 + 5048607 * 2 ^ 59
def prefixEnd_5048607 : Nat := 4983230072969 + 3 ^ 40 * 5048607 * 2
def baseEnd_5048607 : Nat := 2592362026653634035594385

theorem tailTrace_5048607 : CollatzResearch.WordTrace tailWord_5048607 prefixEnd_5048607 2592362026653634035594385 := by
  unfold tailWord_5048607
  simp only [CollatzResearch.WordTrace]
  refine ⟨184137824820766547274800075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122758549880511031516533383 184137824820766547274800075)
  ·
    refine ⟨276206737231149820912200113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184137824820766547274800075 276206737231149820912200113)
    ·
      refine ⟨207155052923362365684150085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276206737231149820912200113 207155052923362365684150085)
      ·
        refine ⟨38841572423130443565778141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207155052923362365684150085 38841572423130443565778141)
        ·
          refine ⟨14565589658673916337166803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38841572423130443565778141 14565589658673916337166803)
          ·
            refine ⟨21848384488010874505750205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14565589658673916337166803 21848384488010874505750205)
            ·
              refine ⟨8193144183004077939656327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21848384488010874505750205 8193144183004077939656327)
              ·
                refine ⟨12289716274506116909484491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8193144183004077939656327 12289716274506116909484491)
                ·
                  refine ⟨18434574411759175364226737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12289716274506116909484491 18434574411759175364226737)
                  ·
                    refine ⟨13825930808819381523170053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18434574411759175364226737 13825930808819381523170053)
                    ·
                      refine ⟨2592362026653634035594385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13825930808819381523170053 2592362026653634035594385)
                      ·
                        rfl

theorem cell23_5048607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_5048607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048607 prefixEnd_5048607 := by exact prefixLift 5048607
  have htrace : WordTrace (prefixWord ++ tailWord_5048607) baseStart_5048607 baseEnd_5048607 := by
    simpa [prefixWord, tailWord_5048607, baseEnd_5048607] using wordTrace_append hprefix tailTrace_5048607
  have hstable : (prefixWord ++ tailWord_5048607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048607).length < 2 ^ (prefixWord ++ tailWord_5048607).sum := by decide
  have hdescent : baseEnd_5048607 < baseStart_5048607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048622 : List Nat := [4, 1, 3, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5048622 : Nat := 118140960795 + 5048622 * 2 ^ 59
def prefixEnd_5048622 : Nat := 4983230072969 + 3 ^ 40 * 5048622 * 2
def baseEnd_5048622 : Nat := 2592369728863451476906817

theorem tailTrace_5048622 : CollatzResearch.WordTrace tailWord_5048622 prefixEnd_5048622 2592369728863451476906817 := by
  unfold tailWord_5048622
  simp only [CollatzResearch.WordTrace]
  refine ⟨23017296489464025604574515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122758914610474803224397413 23017296489464025604574515)
  ·
    refine ⟨34525944734196038406861773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23017296489464025604574515 34525944734196038406861773)
    ·
      refine ⟨12947229275323514402573165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34525944734196038406861773 12947229275323514402573165)
      ·
        refine ⟨4855210978246317900964937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12947229275323514402573165 4855210978246317900964937)
        ·
          refine ⟨3641408233684738425723703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4855210978246317900964937 3641408233684738425723703)
          ·
            refine ⟨5462112350527107638585555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3641408233684738425723703 5462112350527107638585555)
            ·
              refine ⟨8193168525790661457878333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5462112350527107638585555 8193168525790661457878333)
              ·
                refine ⟨3072438197171498046704375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8193168525790661457878333 3072438197171498046704375)
                ·
                  refine ⟨4608657295757247070056563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072438197171498046704375 4608657295757247070056563)
                  ·
                    refine ⟨6912985943635870605084845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4608657295757247070056563 6912985943635870605084845)
                    ·
                      refine ⟨2592369728863451476906817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6912985943635870605084845 2592369728863451476906817)
                      ·
                        rfl

theorem cell23_5048622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5048622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048622 prefixEnd_5048622 := by exact prefixLift 5048622
  have htrace : WordTrace (prefixWord ++ tailWord_5048622) baseStart_5048622 baseEnd_5048622 := by
    simpa [prefixWord, tailWord_5048622, baseEnd_5048622] using wordTrace_append hprefix tailTrace_5048622
  have hstable : (prefixWord ++ tailWord_5048622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048622).length < 2 ^ (prefixWord ++ tailWord_5048622).sum := by decide
  have hdescent : baseEnd_5048622 < baseStart_5048622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048627 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 6, 1, 3]
def baseStart_5048627 : Nat := 118140960795 + 5048627 * 2 ^ 59
def prefixEnd_5048627 : Nat := 4983230072969 + 3 ^ 40 * 5048627 * 2
def baseEnd_5048627 : Nat := 2592372296266723957344293

theorem tailTrace_5048627 : CollatzResearch.WordTrace tailWord_5048627 prefixEnd_5048627 2592372296266723957344293 := by
  unfold tailWord_5048627
  simp only [CollatzResearch.WordTrace]
  refine ⟨184138554280694090690528135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122759036187129393793685423 184138554280694090690528135)
  ·
    refine ⟨276207831421041136035792203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184138554280694090690528135 276207831421041136035792203)
    ·
      refine ⟨414311747131561704053688305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276207831421041136035792203 414311747131561704053688305)
      ·
        refine ⟨310733810348671278040266229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414311747131561704053688305 310733810348671278040266229)
        ·
          refine ⟨29131294720187932316274959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 310733810348671278040266229 29131294720187932316274959)
          ·
            refine ⟨43696942080281898474412439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29131294720187932316274959 43696942080281898474412439)
            ·
              refine ⟨65545413120422847711618659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43696942080281898474412439 65545413120422847711618659)
              ·
                refine ⟨98318119680634271567427989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65545413120422847711618659 98318119680634271567427989)
                ·
                  refine ⟨4608661860029731479723187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98318119680634271567427989 4608661860029731479723187)
                  ·
                    refine ⟨6912992790044597219584781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4608661860029731479723187 6912992790044597219584781)
                    ·
                      refine ⟨2592372296266723957344293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6912992790044597219584781 2592372296266723957344293)
                      ·
                        rfl

theorem cell23_5048627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 1, 3].length) (baseStart_5048627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048627 prefixEnd_5048627 := by exact prefixLift 5048627
  have htrace : WordTrace (prefixWord ++ tailWord_5048627) baseStart_5048627 baseEnd_5048627 := by
    simpa [prefixWord, tailWord_5048627, baseEnd_5048627] using wordTrace_append hprefix tailTrace_5048627
  have hstable : (prefixWord ++ tailWord_5048627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048627).length < 2 ^ (prefixWord ++ tailWord_5048627).sum := by decide
  have hdescent : baseEnd_5048627 < baseStart_5048627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048661 : List Nat := [1, 3, 2, 2, 4, 1, 1, 3, 2, 1, 3]
def baseStart_5048661 : Nat := 118140960795 + 5048661 * 2 ^ 59
def prefixEnd_5048661 : Nat := 4983230072969 + 3 ^ 40 * 5048661 * 2
def baseEnd_5048661 : Nat := 2592389754608976824319137

theorem tailTrace_5048661 : CollatzResearch.WordTrace tailWord_5048661 prefixEnd_5048661 2592389754608976824319137 := by
  unfold tailWord_5048661
  simp only [CollatzResearch.WordTrace]
  refine ⟨184139794362570914497265837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122759862908380609664843891 184139794362570914497265837)
  ·
    refine ⟨69052422885964092936474689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184139794362570914497265837 69052422885964092936474689)
    ·
      refine ⟨51789317164473069702356017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69052422885964092936474689 51789317164473069702356017)
      ·
        refine ⟨38841987873354802276767013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51789317164473069702356017 38841987873354802276767013)
        ·
          refine ⟨7282872726254025426893815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38841987873354802276767013 7282872726254025426893815)
          ·
            refine ⟨10924309089381038140340723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7282872726254025426893815 10924309089381038140340723)
            ·
              refine ⟨16386463634071557210511085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10924309089381038140340723 16386463634071557210511085)
              ·
                refine ⟨6144923862776833953941657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16386463634071557210511085 6144923862776833953941657)
                ·
                  refine ⟨4608692897082625465456243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6144923862776833953941657 4608692897082625465456243)
                  ·
                    refine ⟨6913039345623938198184365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4608692897082625465456243 6913039345623938198184365)
                    ·
                      refine ⟨2592389754608976824319137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6913039345623938198184365 2592389754608976824319137)
                      ·
                        rfl

theorem cell23_5048661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_5048661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048661 prefixEnd_5048661 := by exact prefixLift 5048661
  have htrace : WordTrace (prefixWord ++ tailWord_5048661) baseStart_5048661 baseEnd_5048661 := by
    simpa [prefixWord, tailWord_5048661, baseEnd_5048661] using wordTrace_append hprefix tailTrace_5048661
  have hstable : (prefixWord ++ tailWord_5048661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048661).length < 2 ^ (prefixWord ++ tailWord_5048661).sum := by decide
  have hdescent : baseEnd_5048661 < baseStart_5048661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048701 : List Nat := [1, 4, 1, 1, 2, 3, 1, 4, 2, 2, 2]
def baseStart_5048701 : Nat := 118140960795 + 5048701 * 2 ^ 59
def prefixEnd_5048701 : Nat := 4983230072969 + 3 ^ 40 * 5048701 * 2
def baseEnd_5048701 : Nat := 2592410293835156667818953

theorem tailTrace_5048701 : CollatzResearch.WordTrace tailWord_5048701 prefixEnd_5048701 2592410293835156667818953 := by
  unfold tailWord_5048701
  simp only [CollatzResearch.WordTrace]
  refine ⟨184141253282426001328721957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122760835521617334219147971 184141253282426001328721957)
  ·
    refine ⟨34526484990454875249135367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184141253282426001328721957 34526484990454875249135367)
    ·
      refine ⟨51789727485682312873703051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34526484990454875249135367 51789727485682312873703051)
      ·
        refine ⟨77684591228523469310554577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51789727485682312873703051 77684591228523469310554577)
        ·
          refine ⟨58263443421392601982915933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77684591228523469310554577 58263443421392601982915933)
          ·
            refine ⟨21848791283022225743593475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58263443421392601982915933 21848791283022225743593475)
            ·
              refine ⟨32773186924533338615390213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21848791283022225743593475 32773186924533338615390213)
              ·
                refine ⟨6144972548350000990385665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32773186924533338615390213 6144972548350000990385665)
                ·
                  refine ⟨4608729411262500742789249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6144972548350000990385665 4608729411262500742789249)
                  ·
                    refine ⟨3456547058446875557091937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4608729411262500742789249 3456547058446875557091937)
                    ·
                      refine ⟨2592410293835156667818953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3456547058446875557091937 2592410293835156667818953)
                      ·
                        rfl

theorem cell23_5048701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_5048701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048701 prefixEnd_5048701 := by exact prefixLift 5048701
  have htrace : WordTrace (prefixWord ++ tailWord_5048701) baseStart_5048701 baseEnd_5048701 := by
    simpa [prefixWord, tailWord_5048701, baseEnd_5048701] using wordTrace_append hprefix tailTrace_5048701
  have hstable : (prefixWord ++ tailWord_5048701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048701).length < 2 ^ (prefixWord ++ tailWord_5048701).sum := by decide
  have hdescent : baseEnd_5048701 < baseStart_5048701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048718 : List Nat := [4, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2]
def baseStart_5048718 : Nat := 118140960795 + 5048718 * 2 ^ 59
def prefixEnd_5048718 : Nat := 4983230072969 + 3 ^ 40 * 5048718 * 2
def baseEnd_5048718 : Nat := 2592419023006283101306375

theorem tailTrace_5048718 : CollatzResearch.WordTrace tailWord_5048718 prefixEnd_5048718 2592419023006283101306375 := by
  unfold tailWord_5048718
  simp only [CollatzResearch.WordTrace]
  refine ⟨23017734165420551654011351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122761248882242942154727205 23017734165420551654011351)
  ·
    refine ⟨34526601248130827481017027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23017734165420551654011351 34526601248130827481017027)
    ·
      refine ⟨51789901872196241221525541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34526601248130827481017027 51789901872196241221525541)
      ·
        refine ⟨9710606601036795229036039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51789901872196241221525541 9710606601036795229036039)
        ·
          refine ⟨14565909901555192843554059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9710606601036795229036039 14565909901555192843554059)
          ·
            refine ⟨21848864852332789265331089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14565909901555192843554059 21848864852332789265331089)
            ·
              refine ⟨16386648639249591948998317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21848864852332789265331089 16386648639249591948998317)
              ·
                refine ⟨6144993239718596980874369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16386648639249591948998317 6144993239718596980874369)
                ·
                  refine ⟨4608744929788947735655777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6144993239718596980874369 4608744929788947735655777)
                  ·
                    refine ⟨3456558697341710801741833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4608744929788947735655777 3456558697341710801741833)
                    ·
                      refine ⟨2592419023006283101306375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3456558697341710801741833 2592419023006283101306375)
                      ·
                        rfl

theorem cell23_5048718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_5048718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048718 prefixEnd_5048718 := by exact prefixLift 5048718
  have htrace : WordTrace (prefixWord ++ tailWord_5048718) baseStart_5048718 baseEnd_5048718 := by
    simpa [prefixWord, tailWord_5048718, baseEnd_5048718] using wordTrace_append hprefix tailTrace_5048718
  have hstable : (prefixWord ++ tailWord_5048718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048718).length < 2 ^ (prefixWord ++ tailWord_5048718).sum := by decide
  have hdescent : baseEnd_5048718 < baseStart_5048718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048724 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 7]
def baseStart_5048724 : Nat := 118140960795 + 5048724 * 2 ^ 59
def prefixEnd_5048724 : Nat := 4983230072969 + 3 ^ 40 * 5048724 * 2
def baseEnd_5048724 : Nat := 288046900432245564203483

theorem tailTrace_5048724 : CollatzResearch.WordTrace tailWord_5048724 prefixEnd_5048724 288046900432245564203483 := by
  unfold tailWord_5048724
  simp only [CollatzResearch.WordTrace]
  refine ⟨92071046080671338128404613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122761394774228450837872817 92071046080671338128404613)
  ·
    refine ⟨17263321140125875899075865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92071046080671338128404613 17263321140125875899075865)
    ·
      refine ⟨12947490855094406924306899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17263321140125875899075865 12947490855094406924306899)
      ·
        refine ⟨19421236282641610386460349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12947490855094406924306899 19421236282641610386460349)
        ·
          refine ⟨7282963605990603894922631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19421236282641610386460349 7282963605990603894922631)
          ·
            refine ⟨10924445408985905842383947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7282963605990603894922631 10924445408985905842383947)
            ·
              refine ⟨16386668113478858763575921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10924445408985905842383947 16386668113478858763575921)
              ·
                refine ⟨12290001085109144072681941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16386668113478858763575921 12290001085109144072681941)
                ·
                  refine ⟨288046900432245564203483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12290001085109144072681941 288046900432245564203483)
                  ·
                    rfl

theorem cell23_5048724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_5048724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048724 prefixEnd_5048724 := by exact prefixLift 5048724
  have htrace : WordTrace (prefixWord ++ tailWord_5048724) baseStart_5048724 baseEnd_5048724 := by
    simpa [prefixWord, tailWord_5048724, baseEnd_5048724] using wordTrace_append hprefix tailTrace_5048724
  have hstable : (prefixWord ++ tailWord_5048724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048724).length < 2 ^ (prefixWord ++ tailWord_5048724).sum := by decide
  have hdescent : baseEnd_5048724 < baseStart_5048724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048769 : List Nat := [1, 2, 7, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_5048769 : Nat := 118140960795 + 5048769 * 2 ^ 59
def prefixEnd_5048769 : Nat := 4983230072969 + 3 ^ 40 * 5048769 * 2
def baseEnd_5048769 : Nat := 2592445210519662401768641

theorem tailTrace_5048769 : CollatzResearch.WordTrace tailWord_5048769 prefixEnd_5048769 2592445210519662401768641 := by
  unfold tailWord_5048769
  simp only [CollatzResearch.WordTrace]
  refine ⟨184143733446179648942197361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122762488964119765961464907 184143733446179648942197361)
  ·
    refine ⟨138107800084634736706648021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184143733446179648942197361 138107800084634736706648021)
    ·
      refine ⟨3236901564483626641562063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 138107800084634736706648021 3236901564483626641562063)
      ·
        refine ⟨4855352346725439962343095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3236901564483626641562063 4855352346725439962343095)
        ·
          refine ⟨7283028520088159943514643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4855352346725439962343095 7283028520088159943514643)
          ·
            refine ⟨10924542780132239915271965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7283028520088159943514643 10924542780132239915271965)
            ·
              refine ⟨4096703542549589968226987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10924542780132239915271965 4096703542549589968226987)
              ·
                refine ⟨6145055313824384952340481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4096703542549589968226987 6145055313824384952340481)
                ·
                  refine ⟨4608791485368288714255361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6145055313824384952340481 4608791485368288714255361)
                  ·
                    refine ⟨3456593614026216535691521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4608791485368288714255361 3456593614026216535691521)
                    ·
                      refine ⟨2592445210519662401768641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3456593614026216535691521 2592445210519662401768641)
                      ·
                        rfl

theorem cell23_5048769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_5048769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048769 prefixEnd_5048769 := by exact prefixLift 5048769
  have htrace : WordTrace (prefixWord ++ tailWord_5048769) baseStart_5048769 baseEnd_5048769 := by
    simpa [prefixWord, tailWord_5048769, baseEnd_5048769] using wordTrace_append hprefix tailTrace_5048769
  have hstable : (prefixWord ++ tailWord_5048769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048769).length < 2 ^ (prefixWord ++ tailWord_5048769).sum := by decide
  have hdescent : baseEnd_5048769 < baseStart_5048769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048777 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 1, 4, 3]
def baseStart_5048777 : Nat := 118140960795 + 5048777 * 2 ^ 59
def prefixEnd_5048777 : Nat := 4983230072969 + 3 ^ 40 * 5048777 * 2
def baseEnd_5048777 : Nat := 2592449318364898370468603

theorem tailTrace_5048777 : CollatzResearch.WordTrace tailWord_5048777 prefixEnd_5048777 2592449318364898370468603 := by
  unfold tailWord_5048777
  simp only [CollatzResearch.WordTrace]
  refine ⟨184144025230150666308488585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122762683486767110872325723 184144025230150666308488585)
  ·
    refine ⟨138108018922612999731366439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184144025230150666308488585 138108018922612999731366439)
    ·
      refine ⟨207162028383919499597049659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138108018922612999731366439 207162028383919499597049659)
      ·
        refine ⟨310743042575879249395574489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207162028383919499597049659 310743042575879249395574489)
        ·
          refine ⟨233057281931909437046680867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310743042575879249395574489 233057281931909437046680867)
          ·
            refine ⟨349585922897864155570021301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233057281931909437046680867 349585922897864155570021301)
            ·
              refine ⟨32773680271674764584689497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 349585922897864155570021301 32773680271674764584689497)
              ·
                refine ⟨24580260203756073438517123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32773680271674764584689497 24580260203756073438517123)
                ·
                  refine ⟨36870390305634110157775685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24580260203756073438517123 36870390305634110157775685)
                  ·
                    refine ⟨6913198182306395654582941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36870390305634110157775685 6913198182306395654582941)
                    ·
                      refine ⟨2592449318364898370468603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6913198182306395654582941 2592449318364898370468603)
                      ·
                        rfl

theorem cell23_5048777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 4, 3].length) (baseStart_5048777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048777 prefixEnd_5048777 := by exact prefixLift 5048777
  have htrace : WordTrace (prefixWord ++ tailWord_5048777) baseStart_5048777 baseEnd_5048777 := by
    simpa [prefixWord, tailWord_5048777, baseEnd_5048777] using wordTrace_append hprefix tailTrace_5048777
  have hstable : (prefixWord ++ tailWord_5048777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048777).length < 2 ^ (prefixWord ++ tailWord_5048777).sum := by decide
  have hdescent : baseEnd_5048777 < baseStart_5048777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048794 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3]
def baseStart_5048794 : Nat := 118140960795 + 5048794 * 2 ^ 59
def prefixEnd_5048794 : Nat := 4983230072969 + 3 ^ 40 * 5048794 * 2
def baseEnd_5048794 : Nat := 2592458047536024803956025

theorem tailTrace_5048794 : CollatzResearch.WordTrace tailWord_5048794 prefixEnd_5048794 2592458047536024803956025 := by
  unfold tailWord_5048794
  simp only [CollatzResearch.WordTrace]
  refine ⟨46036161317772269552964359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122763096847392718807904957 46036161317772269552964359)
  ·
    refine ⟨69054241976658404329446539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46036161317772269552964359 69054241976658404329446539)
    ·
      refine ⟨103581362964987606494169809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69054241976658404329446539 103581362964987606494169809)
      ·
        refine ⟨77686022223740704870627357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103581362964987606494169809 77686022223740704870627357)
        ·
          refine ⟨29132258333902764326485259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77686022223740704870627357 29132258333902764326485259)
          ·
            refine ⟨43698387500854146489727889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29132258333902764326485259 43698387500854146489727889)
            ·
              refine ⟨32773790625640609867295917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43698387500854146489727889 32773790625640609867295917)
              ·
                refine ⟨12290171484615228700235969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32773790625640609867295917 12290171484615228700235969)
                ·
                  refine ⟨9217628613461421525176977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12290171484615228700235969 9217628613461421525176977)
                  ·
                    refine ⟨6913221460096066143882733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9217628613461421525176977 6913221460096066143882733)
                    ·
                      refine ⟨2592458047536024803956025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6913221460096066143882733 2592458047536024803956025)
                      ·
                        rfl

theorem cell23_5048794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_5048794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048794 prefixEnd_5048794 := by exact prefixLift 5048794
  have htrace : WordTrace (prefixWord ++ tailWord_5048794) baseStart_5048794 baseEnd_5048794 := by
    simpa [prefixWord, tailWord_5048794, baseEnd_5048794] using wordTrace_append hprefix tailTrace_5048794
  have hstable : (prefixWord ++ tailWord_5048794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048794).length < 2 ^ (prefixWord ++ tailWord_5048794).sum := by decide
  have hdescent : baseEnd_5048794 < baseStart_5048794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048797 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 10]
def baseStart_5048797 : Nat := 118140960795 + 5048797 * 2 ^ 59
def prefixEnd_5048797 : Nat := 4983230072969 + 3 ^ 40 * 5048797 * 2
def baseEnd_5048797 : Nat := 288051065330887588024279

theorem tailTrace_5048797 : CollatzResearch.WordTrace tailWord_5048797 prefixEnd_5048797 288051065330887588024279 := by
  unfold tailWord_5048797
  simp only [CollatzResearch.WordTrace]
  refine ⟨184144754690078209724216645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122763169793385473149477763 184144754690078209724216645)
  ·
    refine ⟨34527141504389664323290621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184144754690078209724216645 34527141504389664323290621)
    ·
      refine ⟨12947678064146124121233983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34527141504389664323290621 12947678064146124121233983)
      ·
        refine ⟨19421517096219186181850975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12947678064146124121233983 19421517096219186181850975)
        ·
          refine ⟨29132275644328779272776463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19421517096219186181850975 29132275644328779272776463)
          ·
            refine ⟨43698413466493168909164695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29132275644328779272776463 43698413466493168909164695)
            ·
              refine ⟨65547620199739753363747043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43698413466493168909164695 65547620199739753363747043)
              ·
                refine ⟨98321430299609630045620565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65547620199739753363747043 98321430299609630045620565)
                ·
                  refine ⟨288051065330887588024279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 98321430299609630045620565 288051065330887588024279)
                  ·
                    rfl

theorem cell23_5048797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_5048797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048797 prefixEnd_5048797 := by exact prefixLift 5048797
  have htrace : WordTrace (prefixWord ++ tailWord_5048797) baseStart_5048797 baseEnd_5048797 := by
    simpa [prefixWord, tailWord_5048797, baseEnd_5048797] using wordTrace_append hprefix tailTrace_5048797
  have hstable : (prefixWord ++ tailWord_5048797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048797).length < 2 ^ (prefixWord ++ tailWord_5048797).sum := by decide
  have hdescent : baseEnd_5048797 < baseStart_5048797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048818 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 3, 4]
def baseStart_5048818 : Nat := 118140960795 + 5048818 * 2 ^ 59
def prefixEnd_5048818 : Nat := 4983230072969 + 3 ^ 40 * 5048818 * 2
def baseEnd_5048818 : Nat := 864156790357244236685305

theorem tailTrace_5048818 : CollatzResearch.WordTrace tailWord_5048818 prefixEnd_5048818 864156790357244236685305 := by
  unfold tailWord_5048818
  simp only [CollatzResearch.WordTrace]
  refine ⟨46036380155750532577682777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122763680415334753540487405 46036380155750532577682777)
  ·
    refine ⟨34527285116812899433262083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46036380155750532577682777 34527285116812899433262083)
    ·
      refine ⟨51790927675219349149893125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34527285116812899433262083 51790927675219349149893125)
      ·
        refine ⟨9710798939103627965604961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51790927675219349149893125 9710798939103627965604961)
        ·
          refine ⟨7283099204327720974203721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9710798939103627965604961 7283099204327720974203721)
          ·
            refine ⟨5462324403245790730652791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7283099204327720974203721 5462324403245790730652791)
            ·
              refine ⟨8193486604868686095979187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5462324403245790730652791 8193486604868686095979187)
              ·
                refine ⟨12290229907303029143968781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8193486604868686095979187 12290229907303029143968781)
                ·
                  refine ⟨4608836215238635928988293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12290229907303029143968781 4608836215238635928988293)
                  ·
                    refine ⟨864156790357244236685305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4608836215238635928988293 864156790357244236685305)
                    ·
                      rfl

theorem cell23_5048818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_5048818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048818 prefixEnd_5048818 := by exact prefixLift 5048818
  have htrace : WordTrace (prefixWord ++ tailWord_5048818) baseStart_5048818 baseEnd_5048818 := by
    simpa [prefixWord, tailWord_5048818, baseEnd_5048818] using wordTrace_append hprefix tailTrace_5048818
  have hstable : (prefixWord ++ tailWord_5048818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048818).length < 2 ^ (prefixWord ++ tailWord_5048818).sum := by decide
  have hdescent : baseEnd_5048818 < baseStart_5048818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048844 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 3, 5]
def baseStart_5048844 : Nat := 118140960795 + 5048844 * 2 ^ 59
def prefixEnd_5048844 : Nat := 4983230072969 + 3 ^ 40 * 5048844 * 2
def baseEnd_5048844 : Nat := 864161240522916536110265

theorem tailTrace_5048844 : CollatzResearch.WordTrace tailWord_5048844 prefixEnd_5048844 864161240522916536110265 := by
  unfold tailWord_5048844
  simp only [CollatzResearch.WordTrace]
  refine ⟨92073234460453968375588793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122764312613938624500785057 92073234460453968375588793)
  ·
    refine ⟨69054925845340476281691595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92073234460453968375588793 69054925845340476281691595)
    ·
      refine ⟨103582388768010714422537393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69054925845340476281691595 103582388768010714422537393)
      ·
        refine ⟨77686791576008035816903045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103582388768010714422537393 77686791576008035816903045)
        ·
          refine ⟨14566273420501506715669321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77686791576008035816903045 14566273420501506715669321)
          ·
            refine ⟨10924705065376130036751991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14566273420501506715669321 10924705065376130036751991)
            ·
              refine ⟨16387057598064195055127987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10924705065376130036751991 16387057598064195055127987)
              ·
                refine ⟨24580586397096292582691981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16387057598064195055127987 24580586397096292582691981)
                ·
                  refine ⟨9217719898911109718509493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24580586397096292582691981 9217719898911109718509493)
                  ·
                    refine ⟨864161240522916536110265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9217719898911109718509493 864161240522916536110265)
                    ·
                      rfl

theorem cell23_5048844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_5048844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048844 prefixEnd_5048844 := by exact prefixLift 5048844
  have htrace : WordTrace (prefixWord ++ tailWord_5048844) baseStart_5048844 baseEnd_5048844 := by
    simpa [prefixWord, tailWord_5048844, baseEnd_5048844] using wordTrace_append hprefix tailTrace_5048844
  have hstable : (prefixWord ++ tailWord_5048844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048844).length < 2 ^ (prefixWord ++ tailWord_5048844).sum := by decide
  have hdescent : baseEnd_5048844 < baseStart_5048844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048845 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_5048845 : Nat := 118140960795 + 5048845 * 2 ^ 59
def prefixEnd_5048845 : Nat := 4983230072969 + 3 ^ 40 * 5048845 * 2
def baseEnd_5048845 : Nat := 2592484235049404104418291

theorem tailTrace_5048845 : CollatzResearch.WordTrace tailWord_5048845 prefixEnd_5048845 2592484235049404104418291 := by
  unfold tailWord_5048845
  simp only [CollatzResearch.WordTrace]
  refine ⟨184146505393904313921963989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122764336929269542614642659 184146505393904313921963989)
  ·
    refine ⟨4315933720169632357546031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 184146505393904313921963989 4315933720169632357546031)
    ·
      refine ⟨6473900580254448536319047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4315933720169632357546031 6473900580254448536319047)
      ·
        refine ⟨9710850870381672804478571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6473900580254448536319047 9710850870381672804478571)
        ·
          refine ⟨14566276305572509206717857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9710850870381672804478571 14566276305572509206717857)
          ·
            refine ⟨10924707229179381905038393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14566276305572509206717857 10924707229179381905038393)
            ·
              refine ⟨8193530421884536428778795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10924707229179381905038393 8193530421884536428778795)
              ·
                refine ⟨12290295632826804643168193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8193530421884536428778795 12290295632826804643168193)
                ·
                  refine ⟨9217721724620103482376145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12290295632826804643168193 9217721724620103482376145)
                  ·
                    refine ⟨6913291293465077611782109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9217721724620103482376145 6913291293465077611782109)
                    ·
                      refine ⟨2592484235049404104418291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6913291293465077611782109 2592484235049404104418291)
                      ·
                        rfl

theorem cell23_5048845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_5048845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048845 prefixEnd_5048845 := by exact prefixLift 5048845
  have htrace : WordTrace (prefixWord ++ tailWord_5048845) baseStart_5048845 baseEnd_5048845 := by
    simpa [prefixWord, tailWord_5048845, baseEnd_5048845] using wordTrace_append hprefix tailTrace_5048845
  have hstable : (prefixWord ++ tailWord_5048845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048845).length < 2 ^ (prefixWord ++ tailWord_5048845).sum := by decide
  have hdescent : baseEnd_5048845 < baseStart_5048845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048851 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 2, 3, 2]
def baseStart_5048851 : Nat := 118140960795 + 5048851 * 2 ^ 59
def prefixEnd_5048851 : Nat := 4983230072969 + 3 ^ 40 * 5048851 * 2
def baseEnd_5048851 : Nat := 2592487315933331080943263

theorem tailTrace_5048851 : CollatzResearch.WordTrace tailWord_5048851 prefixEnd_5048851 2592487315933331080943263 := by
  unfold tailWord_5048851
  simp only [CollatzResearch.WordTrace]
  refine ⟨184146724231882576946682407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122764482821255051297788271 184146724231882576946682407)
  ·
    refine ⟨276220086347823865420023611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184146724231882576946682407 276220086347823865420023611)
    ·
      refine ⟨414330129521735798130035417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276220086347823865420023611 414330129521735798130035417)
      ·
        refine ⟨310747597141301848597526563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414330129521735798130035417 310747597141301848597526563)
        ·
          refine ⟨466121395711952772896289845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310747597141301848597526563 466121395711952772896289845)
          ·
            refine ⟨43698880847995572459027173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 466121395711952772896289845 43698880847995572459027173)
            ·
              refine ⟨8193540158999169836067595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43698880847995572459027173 8193540158999169836067595)
              ·
                refine ⟨12290310238498754754101393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8193540158999169836067595 12290310238498754754101393)
                ·
                  refine ⟨9217732678874066065576045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12290310238498754754101393 9217732678874066065576045)
                  ·
                    refine ⟨3456649754577774774591017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9217732678874066065576045 3456649754577774774591017)
                    ·
                      refine ⟨2592487315933331080943263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3456649754577774774591017 2592487315933331080943263)
                      ·
                        rfl

theorem cell23_5048851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 3, 2].length) (baseStart_5048851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048851 prefixEnd_5048851 := by exact prefixLift 5048851
  have htrace : WordTrace (prefixWord ++ tailWord_5048851) baseStart_5048851 baseEnd_5048851 := by
    simpa [prefixWord, tailWord_5048851, baseEnd_5048851] using wordTrace_append hprefix tailTrace_5048851
  have hstable : (prefixWord ++ tailWord_5048851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048851).length < 2 ^ (prefixWord ++ tailWord_5048851).sum := by decide
  have hdescent : baseEnd_5048851 < baseStart_5048851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048857 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 1, 6]
def baseStart_5048857 : Nat := 118140960795 + 5048857 * 2 ^ 59
def prefixEnd_5048857 : Nat := 4983230072969 + 3 ^ 40 * 5048857 * 2
def baseEnd_5048857 : Nat := 864163465605752685822745

theorem tailTrace_5048857 : CollatzResearch.WordTrace tailWord_5048857 prefixEnd_5048857 864163465605752685822745 := by
  unfold tailWord_5048857
  simp only [CollatzResearch.WordTrace]
  refine ⟨184146943069860839971400825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122764628713240559980933883 184146943069860839971400825)
  ·
    refine ⟨138110207302395629978550619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184146943069860839971400825 138110207302395629978550619)
    ·
      refine ⟨207165310953593444967825929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138110207302395629978550619 207165310953593444967825929)
      ·
        refine ⟨155373983215195083725869447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207165310953593444967825929 155373983215195083725869447)
        ·
          refine ⟨233060974822792625588804171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155373983215195083725869447 233060974822792625588804171)
          ·
            refine ⟨349591462234188938383206257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233060974822792625588804171 349591462234188938383206257)
            ·
              refine ⟨262193596675641703787404693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349591462234188938383206257 262193596675641703787404693)
              ·
                refine ⟨12290324844170704865034595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 262193596675641703787404693 12290324844170704865034595)
                ·
                  refine ⟨18435487266256057297551893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12290324844170704865034595 18435487266256057297551893)
                  ·
                    refine ⟨864163465605752685822745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18435487266256057297551893 864163465605752685822745)
                    ·
                      rfl

theorem cell23_5048857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 6].length) (baseStart_5048857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048857 prefixEnd_5048857 := by exact prefixLift 5048857
  have htrace : WordTrace (prefixWord ++ tailWord_5048857) baseStart_5048857 baseEnd_5048857 := by
    simpa [prefixWord, tailWord_5048857, baseEnd_5048857] using wordTrace_append hprefix tailTrace_5048857
  have hstable : (prefixWord ++ tailWord_5048857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048857).length < 2 ^ (prefixWord ++ tailWord_5048857).sum := by decide
  have hdescent : baseEnd_5048857 < baseStart_5048857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048902 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_5048902 : Nat := 118140960795 + 5048902 * 2 ^ 59
def prefixEnd_5048902 : Nat := 4983230072969 + 3 ^ 40 * 5048902 * 2
def baseEnd_5048902 : Nat := 2592513503446710381405529

theorem tailTrace_5048902 : CollatzResearch.WordTrace tailWord_5048902 prefixEnd_5048902 2592513503446710381405529 := by
  unfold tailWord_5048902
  simp only [CollatzResearch.WordTrace]
  refine ⟨5754643261084306645524655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122765722903131875104525973 5754643261084306645524655)
  ·
    refine ⟨8631964891626459968286983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5754643261084306645524655 8631964891626459968286983)
    ·
      refine ⟨12947947337439689952430475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8631964891626459968286983 12947947337439689952430475)
      ·
        refine ⟨19421921006159534928645713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12947947337439689952430475 19421921006159534928645713)
        ·
          refine ⟨14566440754619651196484285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19421921006159534928645713 14566440754619651196484285)
          ·
            refine ⟨5462415282982369198681607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14566440754619651196484285 5462415282982369198681607)
            ·
              refine ⟨8193622924473553798022411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5462415282982369198681607 8193622924473553798022411)
              ·
                refine ⟨12290434386710330697033617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8193622924473553798022411 12290434386710330697033617)
                ·
                  refine ⟨9217825790032748022775213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12290434386710330697033617 9217825790032748022775213)
                  ·
                    refine ⟨3456684671262280508540705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9217825790032748022775213 3456684671262280508540705)
                    ·
                      refine ⟨2592513503446710381405529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3456684671262280508540705 2592513503446710381405529)
                      ·
                        rfl

theorem cell23_5048902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_5048902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048902 prefixEnd_5048902 := by exact prefixLift 5048902
  have htrace : WordTrace (prefixWord ++ tailWord_5048902) baseStart_5048902 baseEnd_5048902 := by
    simpa [prefixWord, tailWord_5048902, baseEnd_5048902] using wordTrace_append hprefix tailTrace_5048902
  have hstable : (prefixWord ++ tailWord_5048902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048902).length < 2 ^ (prefixWord ++ tailWord_5048902).sum := by decide
  have hdescent : baseEnd_5048902 < baseStart_5048902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048931 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 4, 1, 3]
def baseStart_5048931 : Nat := 118140960795 + 5048931 * 2 ^ 59
def prefixEnd_5048931 : Nat := 4983230072969 + 3 ^ 40 * 5048931 * 2
def baseEnd_5048931 : Nat := 2592528394385690767942895

theorem tailTrace_5048931 : CollatzResearch.WordTrace tailWord_5048931 prefixEnd_5048931 2592528394385690767942895 := by
  unfold tailWord_5048931
  simp only [CollatzResearch.WordTrace]
  refine ⟨184149642071592750609594647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122766428047728500406396431 184149642071592750609594647)
  ·
    refine ⟨276224463107389125914391971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184149642071592750609594647 276224463107389125914391971)
    ·
      refine ⟨414336694661083688871587957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276224463107389125914391971 414336694661083688871587957)
      ·
        refine ⟨38844065124476595831711371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 414336694661083688871587957 38844065124476595831711371)
        ·
          refine ⟨58266097686714893747567057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38844065124476595831711371 58266097686714893747567057)
          ·
            refine ⟨43699573265036170310675293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58266097686714893747567057 43699573265036170310675293)
            ·
              refine ⟨16387339974388563866503235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43699573265036170310675293 16387339974388563866503235)
              ·
                refine ⟨24581009961582845799754853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16387339974388563866503235 24581009961582845799754853)
                ·
                  refine ⟨4608939367796783587454035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24581009961582845799754853 4608939367796783587454035)
                  ·
                    refine ⟨6913409051695175381181053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4608939367796783587454035 6913409051695175381181053)
                    ·
                      refine ⟨2592528394385690767942895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6913409051695175381181053 2592528394385690767942895)
                      ·
                        rfl

theorem cell23_5048931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_5048931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048931 prefixEnd_5048931 := by exact prefixLift 5048931
  have htrace : WordTrace (prefixWord ++ tailWord_5048931) baseStart_5048931 baseEnd_5048931 := by
    simpa [prefixWord, tailWord_5048931, baseEnd_5048931] using wordTrace_append hprefix tailTrace_5048931
  have hstable : (prefixWord ++ tailWord_5048931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048931).length < 2 ^ (prefixWord ++ tailWord_5048931).sum := by decide
  have hdescent : baseEnd_5048931 < baseStart_5048931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048947 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 1, 8]
def baseStart_5048947 : Nat := 118140960795 + 5048947 * 2 ^ 59
def prefixEnd_5048947 : Nat := 4983230072969 + 3 ^ 40 * 5048947 * 2
def baseEnd_5048947 : Nat := 864178870025387568447607

theorem tailTrace_5048947 : CollatzResearch.WordTrace tailWord_5048947 prefixEnd_5048947 864178870025387568447607 := by
  unfold tailWord_5048947
  simp only [CollatzResearch.WordTrace]
  refine ⟨184150225639534785342177095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122766817093023190228118063 184150225639534785342177095)
  ·
    refine ⟨276225338459302178013265643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184150225639534785342177095 276225338459302178013265643)
    ·
      refine ⟨414338007688953267019898465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276225338459302178013265643 414338007688953267019898465)
      ·
        refine ⟨310753505766714950264923849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414338007688953267019898465 310753505766714950264923849)
        ·
          refine ⟨233065129325036212698692887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310753505766714950264923849 233065129325036212698692887)
          ·
            refine ⟨349597693987554319048039331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233065129325036212698692887 349597693987554319048039331)
            ·
              refine ⟨524396540981331478572058997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349597693987554319048039331 524396540981331478572058997)
              ·
                refine ⟨49162175716999826116130531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 524396540981331478572058997 49162175716999826116130531)
                ·
                  refine ⟨73743263575499739174195797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49162175716999826116130531 73743263575499739174195797)
                  ·
                    refine ⟨864178870025387568447607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73743263575499739174195797 864178870025387568447607)
                    ·
                      rfl

theorem cell23_5048947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 8].length) (baseStart_5048947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048947 prefixEnd_5048947 := by exact prefixLift 5048947
  have htrace : WordTrace (prefixWord ++ tailWord_5048947) baseStart_5048947 baseEnd_5048947 := by
    simpa [prefixWord, tailWord_5048947, baseEnd_5048947] using wordTrace_append hprefix tailTrace_5048947
  have hstable : (prefixWord ++ tailWord_5048947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048947).length < 2 ^ (prefixWord ++ tailWord_5048947).sum := by decide
  have hdescent : baseEnd_5048947 < baseStart_5048947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048999 : List Nat := [1, 1, 6, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_5048999 : Nat := 118140960795 + 5048999 * 2 ^ 59
def prefixEnd_5048999 : Nat := 4983230072969 + 3 ^ 40 * 5048999 * 2
def baseEnd_5048999 : Nat := 2592563311070196501892583

theorem tailTrace_5048999 : CollatzResearch.WordTrace tailWord_5048999 prefixEnd_5048999 2592563311070196501892583 := by
  unfold tailWord_5048999
  simp only [CollatzResearch.WordTrace]
  refine ⟨184152122235346398223070051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122768081490230932148713367 184152122235346398223070051)
  ·
    refine ⟨276228183353019597334605077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184152122235346398223070051 276228183353019597334605077)
    ·
      refine ⟨12948196094672793625059613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 276228183353019597334605077 12948196094672793625059613)
      ·
        refine ⟨4855573535502297609397355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12948196094672793625059613 4855573535502297609397355)
        ·
          refine ⟨7283360303253446414096033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4855573535502297609397355 7283360303253446414096033)
          ·
            refine ⟨5462520227440084810572025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7283360303253446414096033 5462520227440084810572025)
            ·
              refine ⟨4096890170580063607929019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5462520227440084810572025 4096890170580063607929019)
              ·
                refine ⟨6145335255870095411893529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4096890170580063607929019 6145335255870095411893529)
                ·
                  refine ⟨4609001441902571558920147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6145335255870095411893529 4609001441902571558920147)
                  ·
                    refine ⟨6913502162853857338380221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4609001441902571558920147 6913502162853857338380221)
                    ·
                      refine ⟨2592563311070196501892583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6913502162853857338380221 2592563311070196501892583)
                      ·
                        rfl

theorem cell23_5048999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_5048999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048999 prefixEnd_5048999 := by exact prefixLift 5048999
  have htrace : WordTrace (prefixWord ++ tailWord_5048999) baseStart_5048999 baseEnd_5048999 := by
    simpa [prefixWord, tailWord_5048999, baseEnd_5048999] using wordTrace_append hprefix tailTrace_5048999
  have hstable : (prefixWord ++ tailWord_5048999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048999).length < 2 ^ (prefixWord ++ tailWord_5048999).sum := by decide
  have hdescent : baseEnd_5048999 < baseStart_5048999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049009 : List Nat := [1, 2, 2, 6, 2, 1, 1, 2, 1, 3, 2]
def baseStart_5049009 : Nat := 118140960795 + 5049009 * 2 ^ 59
def prefixEnd_5049009 : Nat := 4983230072969 + 3 ^ 40 * 5049009 * 2
def baseEnd_5049009 : Nat := 2592568445876741462767537

theorem tailTrace_5049009 : CollatzResearch.WordTrace tailWord_5049009 prefixEnd_5049009 2592568445876741462767537 := by
  unfold tailWord_5049009
  simp only [CollatzResearch.WordTrace]
  refine ⟨184152486965310169930934081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122768324643540113287289387 184152486965310169930934081)
  ·
    refine ⟨138114365223982627448200561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184152486965310169930934081 138114365223982627448200561)
    ·
      refine ⟨103585773917986970586150421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138114365223982627448200561 103585773917986970586150421)
      ·
        refine ⟨4855583152405639246225801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 103585773917986970586150421 4855583152405639246225801)
        ·
          refine ⟨3641687364304229434669351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4855583152405639246225801 3641687364304229434669351)
          ·
            refine ⟨5462531046456344152004027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3641687364304229434669351 5462531046456344152004027)
            ·
              refine ⟨8193796569684516228006041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5462531046456344152004027 8193796569684516228006041)
              ·
                refine ⟨6145347427263387171004531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8193796569684516228006041 6145347427263387171004531)
                ·
                  refine ⟨9218021140895080756506797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6145347427263387171004531 9218021140895080756506797)
                  ·
                    refine ⟨3456757927835655283690049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9218021140895080756506797 3456757927835655283690049)
                    ·
                      refine ⟨2592568445876741462767537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3456757927835655283690049 2592568445876741462767537)
                      ·
                        rfl

theorem cell23_5049009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_5049009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049009 prefixEnd_5049009 := by exact prefixLift 5049009
  have htrace : WordTrace (prefixWord ++ tailWord_5049009) baseStart_5049009 baseEnd_5049009 := by
    simpa [prefixWord, tailWord_5049009, baseEnd_5049009] using wordTrace_append hprefix tailTrace_5049009
  have hstable : (prefixWord ++ tailWord_5049009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049009).length < 2 ^ (prefixWord ++ tailWord_5049009).sum := by decide
  have hdescent : baseEnd_5049009 < baseStart_5049009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049045 : List Nat := [1, 3, 2, 5, 1, 1, 1, 4, 5]
def baseStart_5049045 : Nat := 118140960795 + 5049045 * 2 ^ 59
def prefixEnd_5049045 : Nat := 4983230072969 + 3 ^ 40 * 5049045 * 2
def baseEnd_5049045 : Nat := 288065214575589257990819

theorem tailTrace_5049045 : CollatzResearch.WordTrace tailWord_5049045 prefixEnd_5049045 288065214575589257990819 := by
  unfold tailWord_5049045
  simp only [CollatzResearch.WordTrace]
  refine ⟨184153799993179748079244589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122769199995453165386163059 184153799993179748079244589)
  ·
    refine ⟨69057674997442405529716721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184153799993179748079244589 69057674997442405529716721)
    ·
      refine ⟨51793256248081804147287541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69057674997442405529716721 51793256248081804147287541)
      ·
        refine ⟨4855617773257669138808207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51793256248081804147287541 4855617773257669138808207)
        ·
          refine ⟨7283426659886503708212311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4855617773257669138808207 7283426659886503708212311)
          ·
            refine ⟨10925139989829755562318467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7283426659886503708212311 10925139989829755562318467)
            ·
              refine ⟨16387709984744633343477701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10925139989829755562318467 16387709984744633343477701)
              ·
                refine ⟨3072695622139618751902069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16387709984744633343477701 3072695622139618751902069)
                ·
                  refine ⟨288065214575589257990819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3072695622139618751902069 288065214575589257990819)
                  ·
                    rfl

theorem cell23_5049045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 5].length) (baseStart_5049045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049045 prefixEnd_5049045 := by exact prefixLift 5049045
  have htrace : WordTrace (prefixWord ++ tailWord_5049045) baseStart_5049045 baseEnd_5049045 := by
    simpa [prefixWord, tailWord_5049045, baseEnd_5049045] using wordTrace_append hprefix tailTrace_5049045
  have hstable : (prefixWord ++ tailWord_5049045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049045).length < 2 ^ (prefixWord ++ tailWord_5049045).sum := by decide
  have hdescent : baseEnd_5049045 < baseStart_5049045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049071 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 5, 4]
def baseStart_5049071 : Nat := 118140960795 + 5049071 * 2 ^ 59
def prefixEnd_5049071 : Nat := 4983230072969 + 3 ^ 40 * 5049071 * 2
def baseEnd_5049071 : Nat := 864200093892440073397417

theorem tailTrace_5049071 : CollatzResearch.WordTrace tailWord_5049071 prefixEnd_5049071 864200093892440073397417 := by
  unfold tailWord_5049071
  simp only [CollatzResearch.WordTrace]
  refine ⟨184154748291085554519691067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122769832194057036346460711 184154748291085554519691067)
  ·
    refine ⟨276232122436628331779536601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184154748291085554519691067 276232122436628331779536601)
    ·
      refine ⟨207174091827471248834652451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276232122436628331779536601 207174091827471248834652451)
      ·
        refine ⟨310761137741206873251978677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207174091827471248834652451 310761137741206873251978677)
        ·
          refine ⟨29133856663238144367373001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 310761137741206873251978677 29133856663238144367373001)
          ·
            refine ⟨21850392497428608275529751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29133856663238144367373001 21850392497428608275529751)
            ·
              refine ⟨32775588746142912413294627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21850392497428608275529751 32775588746142912413294627)
              ·
                refine ⟨49163383119214368619941941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32775588746142912413294627 49163383119214368619941941)
                ·
                  refine ⟨4609067167426347058119557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49163383119214368619941941 4609067167426347058119557)
                  ·
                    refine ⟨864200093892440073397417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4609067167426347058119557 864200093892440073397417)
                    ·
                      rfl

theorem cell23_5049071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 4].length) (baseStart_5049071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049071 prefixEnd_5049071 := by exact prefixLift 5049071
  have htrace : WordTrace (prefixWord ++ tailWord_5049071) baseStart_5049071 baseEnd_5049071 := by
    simpa [prefixWord, tailWord_5049071, baseEnd_5049071] using wordTrace_append hprefix tailTrace_5049071
  have hstable : (prefixWord ++ tailWord_5049071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049071).length < 2 ^ (prefixWord ++ tailWord_5049071).sum := by decide
  have hdescent : baseEnd_5049071 < baseStart_5049071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049078 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2]
def baseStart_5049078 : Nat := 118140960795 + 5049078 * 2 ^ 59
def prefixEnd_5049078 : Nat := 4983230072969 + 3 ^ 40 * 5049078 * 2
def baseEnd_5049078 : Nat := 2592603876041901692804719

theorem tailTrace_5049078 : CollatzResearch.WordTrace tailWord_5049078 prefixEnd_5049078 2592603876041901692804719 := by
  unfold tailWord_5049078
  simp only [CollatzResearch.WordTrace]
  refine ⟨11509687725128762169699743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122770002401373463143463925 11509687725128762169699743)
  ·
    refine ⟨17264531587693143254549615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11509687725128762169699743 17264531587693143254549615)
    ·
      refine ⟨25896797381539714881824423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17264531587693143254549615 25896797381539714881824423)
      ·
        refine ⟨38845196072309572322736635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25896797381539714881824423 38845196072309572322736635)
        ·
          refine ⟨58267794108464358484104953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38845196072309572322736635 58267794108464358484104953)
          ·
            refine ⟨43700845581348268863078715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58267794108464358484104953 43700845581348268863078715)
            ·
              refine ⟨65551268372022403294618073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43700845581348268863078715 65551268372022403294618073)
              ·
                refine ⟨49163451279016802470963555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65551268372022403294618073 49163451279016802470963555)
                ·
                  refine ⟨73745176918525203706445333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49163451279016802470963555 73745176918525203706445333)
                  ·
                    refine ⟨3456805168055868923739625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73745176918525203706445333 3456805168055868923739625)
                    ·
                      refine ⟨2592603876041901692804719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3456805168055868923739625 2592603876041901692804719)
                      ·
                        rfl

theorem cell23_5049078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_5049078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049078 prefixEnd_5049078 := by exact prefixLift 5049078
  have htrace : WordTrace (prefixWord ++ tailWord_5049078) baseStart_5049078 baseEnd_5049078 := by
    simpa [prefixWord, tailWord_5049078, baseEnd_5049078] using wordTrace_append hprefix tailTrace_5049078
  have hstable : (prefixWord ++ tailWord_5049078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049078).length < 2 ^ (prefixWord ++ tailWord_5049078).sum := by decide
  have hdescent : baseEnd_5049078 < baseStart_5049078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049131 : List Nat := [1, 1, 1, 1, 2, 1, 2, 8, 1, 5]
def baseStart_5049131 : Nat := 118140960795 + 5049131 * 2 ^ 59
def prefixEnd_5049131 : Nat := 4983230072969 + 3 ^ 40 * 5049131 * 2
def baseEnd_5049131 : Nat := 864210363505529995147325

theorem tailTrace_5049131 : CollatzResearch.WordTrace tailWord_5049131 prefixEnd_5049131 864210363505529995147325 := by
  unfold tailWord_5049131
  simp only [CollatzResearch.WordTrace]
  refine ⟨184156936670868184766875247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122771291113912123177916831 184156936670868184766875247)
  ·
    refine ⟨276235405006302277150312871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184156936670868184766875247 276235405006302277150312871)
    ·
      refine ⟨414353107509453415725469307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276235405006302277150312871 414353107509453415725469307)
      ·
        refine ⟨621529661264180123588203961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414353107509453415725469307 621529661264180123588203961)
        ·
          refine ⟨466147245948135092691152971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 621529661264180123588203961 466147245948135092691152971)
          ·
            refine ⟨699220868922202639036729457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466147245948135092691152971 699220868922202639036729457)
            ·
              refine ⟨524415651691651979277547093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699220868922202639036729457 524415651691651979277547093)
              ·
                refine ⟨6145495918261546632158755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 524415651691651979277547093 6145495918261546632158755)
                ·
                  refine ⟨9218243877392319948238133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6145495918261546632158755 9218243877392319948238133)
                  ·
                    refine ⟨864210363505529995147325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9218243877392319948238133 864210363505529995147325)
                    ·
                      rfl

theorem cell23_5049131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 5].length) (baseStart_5049131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049131 prefixEnd_5049131 := by exact prefixLift 5049131
  have htrace : WordTrace (prefixWord ++ tailWord_5049131) baseStart_5049131 baseEnd_5049131 := by
    simpa [prefixWord, tailWord_5049131, baseEnd_5049131] using wordTrace_append hprefix tailTrace_5049131
  have hstable : (prefixWord ++ tailWord_5049131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049131).length < 2 ^ (prefixWord ++ tailWord_5049131).sum := by decide
  have hdescent : baseEnd_5049131 < baseStart_5049131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049138 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2]
def baseStart_5049138 : Nat := 118140960795 + 5049138 * 2 ^ 59
def prefixEnd_5049138 : Nat := 4983230072969 + 3 ^ 40 * 5049138 * 2
def baseEnd_5049138 : Nat := 2592634684881171458054443

theorem tailTrace_5049138 : CollatzResearch.WordTrace tailWord_5049138 prefixEnd_5049138 2592634684881171458054443 := by
  unfold tailWord_5049138
  simp only [CollatzResearch.WordTrace]
  refine ⟨46039297995460706240595017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122771461321228549974920045 46039297995460706240595017)
  ·
    refine ⟨34529473496595529680446263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46039297995460706240595017 34529473496595529680446263)
    ·
      refine ⟨51794210244893294520669395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34529473496595529680446263 51794210244893294520669395)
      ·
        refine ⟨77691315367339941781004093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51794210244893294520669395 77691315367339941781004093)
        ·
          refine ⟨29134243262752478167876535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77691315367339941781004093 29134243262752478167876535)
          ·
            refine ⟨43701364894128717251814803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29134243262752478167876535 43701364894128717251814803)
            ·
              refine ⟨65552047341193075877722205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43701364894128717251814803 65552047341193075877722205)
              ·
                refine ⟨24582017752947403454145827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65552047341193075877722205 24582017752947403454145827)
                ·
                  refine ⟨36873026629421105181218741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24582017752947403454145827 36873026629421105181218741)
                  ·
                    refine ⟨3456846246508228610739257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36873026629421105181218741 3456846246508228610739257)
                    ·
                      refine ⟨2592634684881171458054443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3456846246508228610739257 2592634684881171458054443)
                      ·
                        rfl

theorem cell23_5049138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_5049138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049138 prefixEnd_5049138 := by exact prefixLift 5049138
  have htrace : WordTrace (prefixWord ++ tailWord_5049138) baseStart_5049138 baseEnd_5049138 := by
    simpa [prefixWord, tailWord_5049138, baseEnd_5049138] using wordTrace_append hprefix tailTrace_5049138
  have hstable : (prefixWord ++ tailWord_5049138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049138).length < 2 ^ (prefixWord ++ tailWord_5049138).sum := by decide
  have hdescent : baseEnd_5049138 < baseStart_5049138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049156 : List Nat := [2, 3, 4, 2, 1, 1, 3, 2, 1, 4]
def baseStart_5049156 : Nat := 118140960795 + 5049156 * 2 ^ 59
def prefixEnd_5049156 : Nat := 4983230072969 + 3 ^ 40 * 5049156 * 2
def baseEnd_5049156 : Nat := 864214642510984129209787

theorem tailTrace_5049156 : CollatzResearch.WordTrace tailWord_5049156 prefixEnd_5049156 864214642510984129209787 := by
  unfold tailWord_5049156
  simp only [CollatzResearch.WordTrace]
  refine ⟨92078924247888807018267661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122771898997185076024356881 92078924247888807018267661)
  ·
    refine ⟨34529596592958302631850373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92078924247888807018267661 34529596592958302631850373)
    ·
      refine ⟨6474299361179681743471945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34529596592958302631850373 6474299361179681743471945)
      ·
        refine ⟨4855724520884761307603959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6474299361179681743471945 4855724520884761307603959)
        ·
          refine ⟨7283586781327141961405939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4855724520884761307603959 7283586781327141961405939)
          ·
            refine ⟨10925380171990712942108909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7283586781327141961405939 10925380171990712942108909)
            ·
              refine ⟨4097017564496517353290841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10925380171990712942108909 4097017564496517353290841)
              ·
                refine ⟨3072763173372388014968131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4097017564496517353290841 3072763173372388014968131)
                ·
                  refine ⟨4609144760058582022452197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072763173372388014968131 4609144760058582022452197)
                  ·
                    refine ⟨864214642510984129209787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4609144760058582022452197 864214642510984129209787)
                    ·
                      rfl

theorem cell23_5049156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_5049156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049156 prefixEnd_5049156 := by exact prefixLift 5049156
  have htrace : WordTrace (prefixWord ++ tailWord_5049156) baseStart_5049156 baseEnd_5049156 := by
    simpa [prefixWord, tailWord_5049156, baseEnd_5049156] using wordTrace_append hprefix tailTrace_5049156
  have hstable : (prefixWord ++ tailWord_5049156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049156).length < 2 ^ (prefixWord ++ tailWord_5049156).sum := by decide
  have hdescent : baseEnd_5049156 < baseStart_5049156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049191 : List Nat := [1, 1, 5, 1, 2, 2, 2, 9]
def baseStart_5049191 : Nat := 118140960795 + 5049191 * 2 ^ 59
def prefixEnd_5049191 : Nat := 4983230072969 + 3 ^ 40 * 5049191 * 2
def baseEnd_5049191 : Nat := 96024514790957768544137

theorem tailTrace_5049191 : CollatzResearch.WordTrace tailWord_5049191 prefixEnd_5049191 96024514790957768544137 := by
  unfold tailWord_5049191
  simp only [CollatzResearch.WordTrace]
  refine ⟨184159125050650815014059427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122772750033767210009372951 184159125050650815014059427)
  ·
    refine ⟨276238687575976222521089141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184159125050650815014059427 276238687575976222521089141)
    ·
      refine ⟨25897376960247770861352107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 276238687575976222521089141 25897376960247770861352107)
      ·
        refine ⟨38846065440371656292028161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25897376960247770861352107 38846065440371656292028161)
        ·
          refine ⟨29134549080278742219021121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38846065440371656292028161 29134549080278742219021121)
          ·
            refine ⟨21850911810209056664265841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29134549080278742219021121 21850911810209056664265841)
            ·
              refine ⟨16388183857656792498199381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21850911810209056664265841 16388183857656792498199381)
              ·
                refine ⟨96024514790957768544137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16388183857656792498199381 96024514790957768544137)
                ·
                  rfl

theorem cell23_5049191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 9].length) (baseStart_5049191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049191 prefixEnd_5049191 := by exact prefixLift 5049191
  have htrace : WordTrace (prefixWord ++ tailWord_5049191) baseStart_5049191 baseEnd_5049191 := by
    simpa [prefixWord, tailWord_5049191, baseEnd_5049191] using wordTrace_append hprefix tailTrace_5049191
  have hstable : (prefixWord ++ tailWord_5049191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049191).length < 2 ^ (prefixWord ++ tailWord_5049191).sum := by decide
  have hdescent : baseEnd_5049191 < baseStart_5049191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049205 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_5049205 : Nat := 118140960795 + 5049205 * 2 ^ 59
def prefixEnd_5049205 : Nat := 4983230072969 + 3 ^ 40 * 5049205 * 2
def baseEnd_5049205 : Nat := 2592669088085022695916635

theorem tailTrace_5049205 : CollatzResearch.WordTrace tailWord_5049205 prefixEnd_5049205 2592669088085022695916635 := by
  unfold tailWord_5049205
  simp only [CollatzResearch.WordTrace]
  refine ⟨184159635672600095405069069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122773090448400063603379379 184159635672600095405069069)
  ·
    refine ⟨69059863377225035776900901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184159635672600095405069069 69059863377225035776900901)
    ·
      refine ⟨12948724383229694208168919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69059863377225035776900901 12948724383229694208168919)
      ·
        refine ⟨19423086574844541312253379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12948724383229694208168919 19423086574844541312253379)
        ·
          refine ⟨29134629862266811968380069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19423086574844541312253379 29134629862266811968380069)
          ·
            refine ⟨5462743099175027244071263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29134629862266811968380069 5462743099175027244071263)
            ·
              refine ⟨8194114648762540866106895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5462743099175027244071263 8194114648762540866106895)
              ·
                refine ⟨12291171973143811299160343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8194114648762540866106895 12291171973143811299160343)
                ·
                  refine ⟨18436757959715716948740515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12291171973143811299160343 18436757959715716948740515)
                  ·
                    refine ⟨27655136939573575423110773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18436757959715716948740515 27655136939573575423110773)
                    ·
                      refine ⟨2592669088085022695916635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27655136939573575423110773 2592669088085022695916635)
                      ·
                        rfl

theorem cell23_5049205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_5049205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049205 prefixEnd_5049205 := by exact prefixLift 5049205
  have htrace : WordTrace (prefixWord ++ tailWord_5049205) baseStart_5049205 baseEnd_5049205 := by
    simpa [prefixWord, tailWord_5049205, baseEnd_5049205] using wordTrace_append hprefix tailTrace_5049205
  have hstable : (prefixWord ++ tailWord_5049205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049205).length < 2 ^ (prefixWord ++ tailWord_5049205).sum := by decide
  have hdescent : baseEnd_5049205 < baseStart_5049205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049221 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 2, 7]
def baseStart_5049221 : Nat := 118140960795 + 5049221 * 2 ^ 59
def prefixEnd_5049221 : Nat := 4983230072969 + 3 ^ 40 * 5049221 * 2
def baseEnd_5049221 : Nat := 864225767925164877772187

theorem tailTrace_5049221 : CollatzResearch.WordTrace tailWord_5049221 prefixEnd_5049221 864225767925164877772187 := by
  unfold tailWord_5049221
  simp only [CollatzResearch.WordTrace]
  refine ⟨184160219240542130137651517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122773479493694753425101011 184160219240542130137651517)
  ·
    refine ⟨69060082215203298801619319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184160219240542130137651517 69060082215203298801619319)
    ·
      refine ⟨103590123322804948202428979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69060082215203298801619319 103590123322804948202428979)
      ·
        refine ⟨155385184984207422303643469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103590123322804948202428979 155385184984207422303643469)
        ·
          refine ⟨58269444369077783363866301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155385184984207422303643469 58269444369077783363866301)
          ·
            refine ⟨21851041638404168761449863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58269444369077783363866301 21851041638404168761449863)
            ·
              refine ⟨32776562457606253142174795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21851041638404168761449863 32776562457606253142174795)
              ·
                refine ⟨49164843686409379713262193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32776562457606253142174795 49164843686409379713262193)
                ·
                  refine ⟨36873632764807034784946645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49164843686409379713262193 36873632764807034784946645)
                  ·
                    refine ⟨864225767925164877772187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36873632764807034784946645 864225767925164877772187)
                    ·
                      rfl

theorem cell23_5049221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_5049221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049221 prefixEnd_5049221 := by exact prefixLift 5049221
  have htrace : WordTrace (prefixWord ++ tailWord_5049221) baseStart_5049221 baseEnd_5049221 := by
    simpa [prefixWord, tailWord_5049221, baseEnd_5049221] using wordTrace_append hprefix tailTrace_5049221
  have hstable : (prefixWord ++ tailWord_5049221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049221).length < 2 ^ (prefixWord ++ tailWord_5049221).sum := by decide
  have hdescent : baseEnd_5049221 < baseStart_5049221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049241 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 4, 3, 4]
def baseStart_5049241 : Nat := 118140960795 + 5049241 * 2 ^ 59
def prefixEnd_5049241 : Nat := 4983230072969 + 3 ^ 40 * 5049241 * 2
def baseEnd_5049241 : Nat := 2592687573388584555066469

theorem tailTrace_5049241 : CollatzResearch.WordTrace tailWord_5049241 prefixEnd_5049241 2592687573388584555066469 := by
  unfold tailWord_5049241
  simp only [CollatzResearch.WordTrace]
  refine ⟨184160948700469673553379577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122773965800313115702253051 184160948700469673553379577)
  ·
    refine ⟨138120711525352255165034683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184160948700469673553379577 138120711525352255165034683)
    ·
      refine ⟨207181067288028382747552025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138120711525352255165034683 207181067288028382747552025)
      ·
        refine ⟨155385800466021287060664019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207181067288028382747552025 155385800466021287060664019)
        ·
          refine ⟨233078700699031930590996029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155385800466021287060664019 233078700699031930590996029)
          ·
            refine ⟨87404512762136973971623511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233078700699031930590996029 87404512762136973971623511)
            ·
              refine ⟨131106769143205460957435267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87404512762136973971623511 131106769143205460957435267)
              ·
                refine ⟨196660153714808191436152901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131106769143205460957435267 196660153714808191436152901)
                ·
                  refine ⟨36873778821526535894278669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 196660153714808191436152901 36873778821526535894278669)
                  ·
                    refine ⟨13827667058072450960354501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36873778821526535894278669 13827667058072450960354501)
                    ·
                      refine ⟨2592687573388584555066469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13827667058072450960354501 2592687573388584555066469)
                      ·
                        rfl

theorem cell23_5049241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_5049241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049241 prefixEnd_5049241 := by exact prefixLift 5049241
  have htrace : WordTrace (prefixWord ++ tailWord_5049241) baseStart_5049241 baseEnd_5049241 := by
    simpa [prefixWord, tailWord_5049241, baseEnd_5049241] using wordTrace_append hprefix tailTrace_5049241
  have hstable : (prefixWord ++ tailWord_5049241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049241).length < 2 ^ (prefixWord ++ tailWord_5049241).sum := by decide
  have hdescent : baseEnd_5049241 < baseStart_5049241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049245 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 3, 3, 2]
def baseStart_5049245 : Nat := 118140960795 + 5049245 * 2 ^ 59
def prefixEnd_5049245 : Nat := 4983230072969 + 3 ^ 40 * 5049245 * 2
def baseEnd_5049245 : Nat := 2592689627311202539416451

theorem tailTrace_5049245 : CollatzResearch.WordTrace tailWord_5049245 prefixEnd_5049245 2592689627311202539416451 := by
  unfold tailWord_5049245
  simp only [CollatzResearch.WordTrace]
  refine ⟨184161094592455182236525189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122774063061636788157683459 184161094592455182236525189)
  ·
    refine ⟨34530205236085346669348473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184161094592455182236525189 34530205236085346669348473)
    ·
      refine ⟨25897653927064010002011355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34530205236085346669348473 25897653927064010002011355)
      ·
        refine ⟨38846480890596015003017033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25897653927064010002011355 38846480890596015003017033)
        ·
          refine ⟨29134860667947011252262775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38846480890596015003017033 29134860667947011252262775)
          ·
            refine ⟨43702291001920516878394163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29134860667947011252262775 43702291001920516878394163)
            ·
              refine ⟨65553436502880775317591245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43702291001920516878394163 65553436502880775317591245)
              ·
                refine ⟨24582538688580290744096717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65553436502880775317591245 24582538688580290744096717)
                ·
                  refine ⟨9218452008217609029036269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24582538688580290744096717 9218452008217609029036269)
                  ·
                    refine ⟨3456919503081603385888601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9218452008217609029036269 3456919503081603385888601)
                    ·
                      refine ⟨2592689627311202539416451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3456919503081603385888601 2592689627311202539416451)
                      ·
                        rfl

theorem cell23_5049245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_5049245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049245 prefixEnd_5049245 := by exact prefixLift 5049245
  have htrace : WordTrace (prefixWord ++ tailWord_5049245) baseStart_5049245 baseEnd_5049245 := by
    simpa [prefixWord, tailWord_5049245, baseEnd_5049245] using wordTrace_append hprefix tailTrace_5049245
  have hstable : (prefixWord ++ tailWord_5049245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049245).length < 2 ^ (prefixWord ++ tailWord_5049245).sum := by decide
  have hdescent : baseEnd_5049245 < baseStart_5049245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049321 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 7]
def baseStart_5049321 : Nat := 118140960795 + 5049321 * 2 ^ 59
def prefixEnd_5049321 : Nat := 4983230072969 + 3 ^ 40 * 5049321 * 2
def baseEnd_5049321 : Nat := 2592728651840944242066101

theorem tailTrace_5049321 : CollatzResearch.WordTrace tailWord_5049321 prefixEnd_5049321 2592728651840944242066101 := by
  unfold tailWord_5049321
  simp only [CollatzResearch.WordTrace]
  refine ⟨184163866540179847216291817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122775911026786564810861211 184163866540179847216291817)
  ·
    refine ⟨138122899905134885412218863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184163866540179847216291817 138122899905134885412218863)
    ·
      refine ⟨207184349857702328118328295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138122899905134885412218863 207184349857702328118328295)
      ·
        refine ⟨310776524786553492177492443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207184349857702328118328295 310776524786553492177492443)
        ·
          refine ⟨466164787179830238266238665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310776524786553492177492443 466164787179830238266238665)
          ·
            refine ⟨349623590384872678699678999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 466164787179830238266238665 349623590384872678699678999)
            ·
              refine ⟨524435385577309018049518499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349623590384872678699678999 524435385577309018049518499)
              ·
                refine ⟨786653078365963527074277749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524435385577309018049518499 786653078365963527074277749)
                ·
                  refine ⟨73748726096809080663213539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 786653078365963527074277749 73748726096809080663213539)
                  ·
                    refine ⟨110623089145213620994820309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73748726096809080663213539 110623089145213620994820309)
                    ·
                      refine ⟨2592728651840944242066101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110623089145213620994820309 2592728651840944242066101)
                      ·
                        rfl

theorem cell23_5049321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_5049321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049321 prefixEnd_5049321 := by exact prefixLift 5049321
  have htrace : WordTrace (prefixWord ++ tailWord_5049321) baseStart_5049321 baseEnd_5049321 := by
    simpa [prefixWord, tailWord_5049321, baseEnd_5049321] using wordTrace_append hprefix tailTrace_5049321
  have hstable : (prefixWord ++ tailWord_5049321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049321).length < 2 ^ (prefixWord ++ tailWord_5049321).sum := by decide
  have hdescent : baseEnd_5049321 < baseStart_5049321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049331 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 8]
def baseStart_5049331 : Nat := 118140960795 + 5049331 * 2 ^ 59
def prefixEnd_5049331 : Nat := 4983230072969 + 3 ^ 40 * 5049331 * 2
def baseEnd_5049331 : Nat := 2592733786647489202941055

theorem tailTrace_5049331 : CollatzResearch.WordTrace tailWord_5049331 prefixEnd_5049331 2592733786647489202941055 := by
  unfold tailWord_5049331
  simp only [CollatzResearch.WordTrace]
  refine ⟨184164231270143618924155847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122776154180095745949437231 184164231270143618924155847)
  ·
    refine ⟨276246346905215428386233771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184164231270143618924155847 276246346905215428386233771)
    ·
      refine ⟨414369520357823142579350657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276246346905215428386233771 414369520357823142579350657)
      ·
        refine ⟨310777140268367356934512993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414369520357823142579350657 310777140268367356934512993)
        ·
          refine ⟨233082855201275517700884745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310777140268367356934512993 233082855201275517700884745)
          ·
            refine ⟨174812141400956638275663559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233082855201275517700884745 174812141400956638275663559)
            ·
              refine ⟨262218212101434957413495339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174812141400956638275663559 262218212101434957413495339)
              ·
                refine ⟨393327318152152436120243009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262218212101434957413495339 393327318152152436120243009)
                ·
                  refine ⟨294995488614114327090182257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393327318152152436120243009 294995488614114327090182257)
                  ·
                    refine ⟨221246616460585745317636693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 294995488614114327090182257 221246616460585745317636693)
                    ·
                      refine ⟨2592733786647489202941055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 221246616460585745317636693 2592733786647489202941055)
                      ·
                        rfl

theorem cell23_5049331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_5049331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049331 prefixEnd_5049331 := by exact prefixLift 5049331
  have htrace : WordTrace (prefixWord ++ tailWord_5049331) baseStart_5049331 baseEnd_5049331 := by
    simpa [prefixWord, tailWord_5049331, baseEnd_5049331] using wordTrace_append hprefix tailTrace_5049331
  have hstable : (prefixWord ++ tailWord_5049331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049331).length < 2 ^ (prefixWord ++ tailWord_5049331).sum := by decide
  have hdescent : baseEnd_5049331 < baseStart_5049331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049365 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_5049365 : Nat := 118140960795 + 5049365 * 2 ^ 59
def prefixEnd_5049365 : Nat := 4983230072969 + 3 ^ 40 * 5049365 * 2
def baseEnd_5049365 : Nat := 2592751244989742069915899

theorem tailTrace_5049365 : CollatzResearch.WordTrace tailWord_5049365 prefixEnd_5049365 2592751244989742069915899 := by
  unfold tailWord_5049365
  simp only [CollatzResearch.WordTrace]
  refine ⟨184165471352020442730893549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122776980901346961820595699 184165471352020442730893549)
  ·
    refine ⟨69062051757007666024085081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184165471352020442730893549 69062051757007666024085081)
    ·
      refine ⟨51796538817755749518063811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69062051757007666024085081 51796538817755749518063811)
      ·
        refine ⟨77694808226633624277095717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51796538817755749518063811 77694808226633624277095717)
        ·
          refine ⟨14567776542493804551955447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77694808226633624277095717 14567776542493804551955447)
          ·
            refine ⟨21851664813740706827933171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14567776542493804551955447 21851664813740706827933171)
            ·
              refine ⟨32777497220611060241899757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21851664813740706827933171 32777497220611060241899757)
              ·
                refine ⟨12291561457729147590712409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32777497220611060241899757 12291561457729147590712409)
                ·
                  refine ⟨9218671093296860693034307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12291561457729147590712409 9218671093296860693034307)
                  ·
                    refine ⟨13828006639945291039551461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9218671093296860693034307 13828006639945291039551461)
                    ·
                      refine ⟨2592751244989742069915899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13828006639945291039551461 2592751244989742069915899)
                      ·
                        rfl

theorem cell23_5049365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_5049365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049365 prefixEnd_5049365 := by exact prefixLift 5049365
  have htrace : WordTrace (prefixWord ++ tailWord_5049365) baseStart_5049365 baseEnd_5049365 := by
    simpa [prefixWord, tailWord_5049365, baseEnd_5049365] using wordTrace_append hprefix tailTrace_5049365
  have hstable : (prefixWord ++ tailWord_5049365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049365).length < 2 ^ (prefixWord ++ tailWord_5049365).sum := by decide
  have hdescent : baseEnd_5049365 < baseStart_5049365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049392 : List Nat := [2, 1, 1, 1, 2, 4, 3, 4, 1, 4]
def baseStart_5049392 : Nat := 118140960795 + 5049392 * 2 ^ 59
def prefixEnd_5049392 : Nat := 4983230072969 + 3 ^ 40 * 5049392 * 2
def baseEnd_5049392 : Nat := 864255036322471154759425

theorem tailTrace_5049392 : CollatzResearch.WordTrace tailWord_5049392 prefixEnd_5049392 864255036322471154759425 := by
  unfold tailWord_5049392
  simp only [CollatzResearch.WordTrace]
  refine ⟨92083228061461313171063215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122777637415281750894750953 92083228061461313171063215)
  ·
    refine ⟨138124842092191969756594823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92083228061461313171063215 138124842092191969756594823)
    ·
      refine ⟨207187263138287954634892235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138124842092191969756594823 207187263138287954634892235)
      ·
        refine ⟨310780894707431931952338353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207187263138287954634892235 310780894707431931952338353)
        ·
          refine ⟨233085671030573948964253765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310780894707431931952338353 233085671030573948964253765)
          ·
            refine ⟨43703563318232615430797581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 233085671030573948964253765 43703563318232615430797581)
            ·
              refine ⟨16388836244337230786549093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43703563318232615430797581 16388836244337230786549093)
              ·
                refine ⟨3072906795813230772477955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16388836244337230786549093 3072906795813230772477955)
                ·
                  refine ⟨4609360193719846158716933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072906795813230772477955 4609360193719846158716933)
                  ·
                    refine ⟨864255036322471154759425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4609360193719846158716933 864255036322471154759425)
                    ·
                      rfl

theorem cell23_5049392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 1, 4].length) (baseStart_5049392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049392 prefixEnd_5049392 := by exact prefixLift 5049392
  have htrace : WordTrace (prefixWord ++ tailWord_5049392) baseStart_5049392 baseEnd_5049392 := by
    simpa [prefixWord, tailWord_5049392, baseEnd_5049392] using wordTrace_append hprefix tailTrace_5049392
  have hstable : (prefixWord ++ tailWord_5049392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049392).length < 2 ^ (prefixWord ++ tailWord_5049392).sum := by decide
  have hdescent : baseEnd_5049392 < baseStart_5049392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049405 : List Nat := [1, 4, 1, 3, 1, 2, 2, 3, 6]
def baseStart_5049405 : Nat := 118140960795 + 5049405 * 2 ^ 59
def prefixEnd_5049405 : Nat := 4983230072969 + 3 ^ 40 * 5049405 * 2
def baseEnd_5049405 : Nat := 288085753801769101490635

theorem tailTrace_5049405 : CollatzResearch.WordTrace tailWord_5049405 prefixEnd_5049405 288085753801769101490635 := by
  unfold tailWord_5049405
  simp only [CollatzResearch.WordTrace]
  refine ⟨184166930271875529562349669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122777953514583686374899779 184166930271875529562349669)
  ·
    refine ⟨34531299425976661792940563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184166930271875529562349669 34531299425976661792940563)
    ·
      refine ⟨51796949138964992689410845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34531299425976661792940563 51796949138964992689410845)
      ·
        refine ⟨19423855927111872258529067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51796949138964992689410845 19423855927111872258529067)
        ·
          refine ⟨29135783890667808387793601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19423855927111872258529067 29135783890667808387793601)
          ·
            refine ⟨21851837918000856290845201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29135783890667808387793601 21851837918000856290845201)
            ·
              refine ⟨16388878438500642218133901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21851837918000856290845201 16388878438500642218133901)
              ·
                refine ⟨6145829414437740831800213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16388878438500642218133901 6145829414437740831800213)
                ·
                  refine ⟨288085753801769101490635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6145829414437740831800213 288085753801769101490635)
                  ·
                    rfl

theorem cell23_5049405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_5049405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049405 prefixEnd_5049405 := by exact prefixLift 5049405
  have htrace : WordTrace (prefixWord ++ tailWord_5049405) baseStart_5049405 baseEnd_5049405 := by
    simpa [prefixWord, tailWord_5049405, baseEnd_5049405] using wordTrace_append hprefix tailTrace_5049405
  have hstable : (prefixWord ++ tailWord_5049405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049405).length < 2 ^ (prefixWord ++ tailWord_5049405).sum := by decide
  have hdescent : baseEnd_5049405 < baseStart_5049405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049449 : List Nat := [1, 2, 1, 1, 1, 6, 2, 4, 1, 1, 3]
def baseStart_5049449 : Nat := 118140960795 + 5049449 * 2 ^ 59
def prefixEnd_5049449 : Nat := 4983230072969 + 3 ^ 40 * 5049449 * 2
def baseEnd_5049449 : Nat := 2592794377364719741265513

theorem tailTrace_5049449 : CollatzResearch.WordTrace tailWord_5049449 prefixEnd_5049449 2592794377364719741265513 := by
  unfold tailWord_5049449
  simp only [CollatzResearch.WordTrace]
  refine ⟨184168535083716125076951401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122779023389144083384634267 184168535083716125076951401)
  ·
    refine ⟨138126401312787093807713551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184168535083716125076951401 138126401312787093807713551)
    ·
      refine ⟨207189601969180640711570327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138126401312787093807713551 207189601969180640711570327)
      ·
        refine ⟨310784402953770961067355491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207189601969180640711570327 310784402953770961067355491)
        ·
          refine ⟨466176604430656441601033237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310784402953770961067355491 466176604430656441601033237)
          ·
            refine ⟨21852028332687020700048433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 466176604430656441601033237 21852028332687020700048433)
            ·
              refine ⟨16389021249515265525036325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21852028332687020700048433 16389021249515265525036325)
              ·
                refine ⟨3072941484284112285944311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16389021249515265525036325 3072941484284112285944311)
                ·
                  refine ⟨4609412226426168428916467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072941484284112285944311 4609412226426168428916467)
                  ·
                    refine ⟨6914118339639252643374701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4609412226426168428916467 6914118339639252643374701)
                    ·
                      refine ⟨2592794377364719741265513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6914118339639252643374701 2592794377364719741265513)
                      ·
                        rfl

theorem cell23_5049449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 1, 1, 3].length) (baseStart_5049449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049449 prefixEnd_5049449 := by exact prefixLift 5049449
  have htrace : WordTrace (prefixWord ++ tailWord_5049449) baseStart_5049449 baseEnd_5049449 := by
    simpa [prefixWord, tailWord_5049449, baseEnd_5049449] using wordTrace_append hprefix tailTrace_5049449
  have hstable : (prefixWord ++ tailWord_5049449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049449).length < 2 ^ (prefixWord ++ tailWord_5049449).sum := by decide
  have hdescent : baseEnd_5049449 < baseStart_5049449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049495 : List Nat := [1, 1, 3, 3, 3, 3, 9]
def baseStart_5049495 : Nat := 118140960795 + 5049495 * 2 ^ 59
def prefixEnd_5049495 : Nat := 4983230072969 + 3 ^ 40 * 5049495 * 2
def baseEnd_5049495 : Nat := 32010098734257118040621

theorem tailTrace_5049495 : CollatzResearch.WordTrace tailWord_5049495 prefixEnd_5049495 32010098734257118040621 := by
  unfold tailWord_5049495
  simp only [CollatzResearch.WordTrace]
  refine ⟨184170212841549474933125939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122780141894366316622083959 184170212841549474933125939)
  ·
    refine ⟨276255319262324212399688909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184170212841549474933125939 276255319262324212399688909)
    ·
      refine ⟨103595744723371579649883341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276255319262324212399688909 103595744723371579649883341)
      ·
        refine ⟨38848404271264342368706253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103595744723371579649883341 38848404271264342368706253)
        ·
          refine ⟨14568151601724128388264845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38848404271264342368706253 14568151601724128388264845)
          ·
            refine ⟨5463056850646548145599317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14568151601724128388264845 5463056850646548145599317)
            ·
              refine ⟨32010098734257118040621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5463056850646548145599317 32010098734257118040621)
              ·
                rfl

theorem cell23_5049495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 9].length) (baseStart_5049495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049495 prefixEnd_5049495 := by exact prefixLift 5049495
  have htrace : WordTrace (prefixWord ++ tailWord_5049495) baseStart_5049495 baseEnd_5049495 := by
    simpa [prefixWord, tailWord_5049495, baseEnd_5049495] using wordTrace_append hprefix tailTrace_5049495
  have hstable : (prefixWord ++ tailWord_5049495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049495).length < 2 ^ (prefixWord ++ tailWord_5049495).sum := by decide
  have hdescent : baseEnd_5049495 < baseStart_5049495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049502 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_5049502 : Nat := 118140960795 + 5049502 * 2 ^ 59
def prefixEnd_5049502 : Nat := 4983230072969 + 3 ^ 40 * 5049502 * 2
def baseEnd_5049502 : Nat := 2592821591839408033902769

theorem tailTrace_5049502 : CollatzResearch.WordTrace tailWord_5049502 prefixEnd_5049502 2592821591839408033902769 := by
  unfold tailWord_5049502
  simp only [CollatzResearch.WordTrace]
  refine ⟨23021308519065514391078845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122780312101682743419087173 23021308519065514391078845)
  ·
    refine ⟨8632990694649567896654567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23021308519065514391078845 8632990694649567896654567)
    ·
      refine ⟨12949486041974351844981851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8632990694649567896654567 12949486041974351844981851)
      ·
        refine ⟨19424229062961527767472777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12949486041974351844981851 19424229062961527767472777)
        ·
          refine ⟨14568171797221145825604583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19424229062961527767472777 14568171797221145825604583)
          ·
            refine ⟨21852257695831718738406875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14568171797221145825604583 21852257695831718738406875)
            ·
              refine ⟨32778386543747578107610313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21852257695831718738406875 32778386543747578107610313)
              ·
                refine ⟨24583789907810683580707735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32778386543747578107610313 24583789907810683580707735)
                ·
                  refine ⟨36875684861716025371061603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24583789907810683580707735 36875684861716025371061603)
                  ·
                    refine ⟨55313527292574038056592405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36875684861716025371061603 55313527292574038056592405)
                    ·
                      refine ⟨2592821591839408033902769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55313527292574038056592405 2592821591839408033902769)
                      ·
                        rfl

theorem cell23_5049502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_5049502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049502 prefixEnd_5049502 := by exact prefixLift 5049502
  have htrace : WordTrace (prefixWord ++ tailWord_5049502) baseStart_5049502 baseEnd_5049502 := by
    simpa [prefixWord, tailWord_5049502, baseEnd_5049502] using wordTrace_append hprefix tailTrace_5049502
  have hstable : (prefixWord ++ tailWord_5049502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049502).length < 2 ^ (prefixWord ++ tailWord_5049502).sum := by decide
  have hdescent : baseEnd_5049502 < baseStart_5049502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049562 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2]
def baseStart_5049562 : Nat := 118140960795 + 5049562 * 2 ^ 59
def prefixEnd_5049562 : Nat := 4983230072969 + 3 ^ 40 * 5049562 * 2
def baseEnd_5049562 : Nat := 2592852400678677799152493

theorem tailTrace_5049562 : CollatzResearch.WordTrace tailWord_5049562 prefixEnd_5049562 2592852400678677799152493 := by
  unfold tailWord_5049562
  simp only [CollatzResearch.WordTrace]
  refine ⟨46043164133076686343953735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122781771021537830250543293 46043164133076686343953735)
  ·
    refine ⟨69064746199615029515930603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46043164133076686343953735 69064746199615029515930603)
    ·
      refine ⟨103597119299422544273895905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69064746199615029515930603 103597119299422544273895905)
      ·
        refine ⟨77697839474566908205421929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103597119299422544273895905 77697839474566908205421929)
        ·
          refine ⟨58273379605925181154066447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77697839474566908205421929 58273379605925181154066447)
          ·
            refine ⟨87410069408887771731099671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58273379605925181154066447 87410069408887771731099671)
            ·
              refine ⟨131115104113331657596649507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87410069408887771731099671 131115104113331657596649507)
              ·
                refine ⟨196672656169997486394974261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131115104113331657596649507 196672656169997486394974261)
                ·
                  refine ⟨18438061515937264349528837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 196672656169997486394974261 18438061515937264349528837)
                  ·
                    refine ⟨3457136534238237065536657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18438061515937264349528837 3457136534238237065536657)
                    ·
                      refine ⟨2592852400678677799152493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3457136534238237065536657 2592852400678677799152493)
                      ·
                        rfl

theorem cell23_5049562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_5049562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049562 prefixEnd_5049562 := by exact prefixLift 5049562
  have htrace : WordTrace (prefixWord ++ tailWord_5049562) baseStart_5049562 baseEnd_5049562 := by
    simpa [prefixWord, tailWord_5049562, baseEnd_5049562] using wordTrace_append hprefix tailTrace_5049562
  have hstable : (prefixWord ++ tailWord_5049562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049562).length < 2 ^ (prefixWord ++ tailWord_5049562).sum := by decide
  have hdescent : baseEnd_5049562 < baseStart_5049562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049579 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 1, 4, 2]
def baseStart_5049579 : Nat := 118140960795 + 5049579 * 2 ^ 59
def prefixEnd_5049579 : Nat := 4983230072969 + 3 ^ 40 * 5049579 * 2
def baseEnd_5049579 : Nat := 2592861129849804232639915

theorem tailTrace_5049579 : CollatzResearch.WordTrace tailWord_5049579 prefixEnd_5049579 2592861129849804232639915 := by
  unfold tailWord_5049579
  simp only [CollatzResearch.WordTrace]
  refine ⟨184173276573245157279183791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122782184382163438186122527 184173276573245157279183791)
  ·
    refine ⟨276259914859867735918775687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184173276573245157279183791 276259914859867735918775687)
    ·
      refine ⟨414389872289801603878163531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276259914859867735918775687 414389872289801603878163531)
      ·
        refine ⟨621584808434702405817245297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414389872289801603878163531 621584808434702405817245297)
        ·
          refine ⟨466188606326026804362933973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 621584808434702405817245297 466188606326026804362933973)
          ·
            refine ⟨10926295460766253227256265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 466188606326026804362933973 10926295460766253227256265)
            ·
              refine ⟨8194721595574689920442199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10926295460766253227256265 8194721595574689920442199)
              ·
                refine ⟨12292082393362034880663299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8194721595574689920442199 12292082393362034880663299)
                ·
                  refine ⟨18438123590043052320994949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12292082393362034880663299 18438123590043052320994949)
                  ·
                    refine ⟨3457148173133072310186553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18438123590043052320994949 3457148173133072310186553)
                    ·
                      refine ⟨2592861129849804232639915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3457148173133072310186553 2592861129849804232639915)
                      ·
                        rfl

theorem cell23_5049579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 4, 2].length) (baseStart_5049579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049579 prefixEnd_5049579 := by exact prefixLift 5049579
  have htrace : WordTrace (prefixWord ++ tailWord_5049579) baseStart_5049579 baseEnd_5049579 := by
    simpa [prefixWord, tailWord_5049579, baseEnd_5049579] using wordTrace_append hprefix tailTrace_5049579
  have hstable : (prefixWord ++ tailWord_5049579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049579).length < 2 ^ (prefixWord ++ tailWord_5049579).sum := by decide
  have hdescent : baseEnd_5049579 < baseStart_5049579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049612 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 2, 3, 3]
def baseStart_5049612 : Nat := 118140960795 + 5049612 * 2 ^ 59
def prefixEnd_5049612 : Nat := 4983230072969 + 3 ^ 40 * 5049612 * 2
def baseEnd_5049612 : Nat := 2592878074711402603527263

theorem tailTrace_5049612 : CollatzResearch.WordTrace tailWord_5049612 prefixEnd_5049612 2592878074711402603527263 := by
  unfold tailWord_5049612
  simp only [CollatzResearch.WordTrace]
  refine ⟨92087240091062801957567545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122782986788083735943423393 92087240091062801957567545)
  ·
    refine ⟨69065430068297101468175659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92087240091062801957567545 69065430068297101468175659)
    ·
      refine ⟨103598145102445652202263489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69065430068297101468175659 103598145102445652202263489)
      ·
        refine ⟨77698608826834239151697617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103598145102445652202263489 77698608826834239151697617)
        ·
          refine ⟨58273956620125679363773213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77698608826834239151697617 58273956620125679363773213)
          ·
            refine ⟨21852733732547129761414955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58273956620125679363773213 21852733732547129761414955)
            ·
              refine ⟨32779100598820694642122433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21852733732547129761414955 32779100598820694642122433)
              ·
                refine ⟨24584325449115520981591825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32779100598820694642122433 24584325449115520981591825)
                ·
                  refine ⟨18438244086836640736193869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24584325449115520981591825 18438244086836640736193869)
                  ·
                    refine ⟨6914341532563740276072701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18438244086836640736193869 6914341532563740276072701)
                    ·
                      refine ⟨2592878074711402603527263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6914341532563740276072701 2592878074711402603527263)
                      ·
                        rfl

theorem cell23_5049612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_5049612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049612 prefixEnd_5049612 := by exact prefixLift 5049612
  have htrace : WordTrace (prefixWord ++ tailWord_5049612) baseStart_5049612 baseEnd_5049612 := by
    simpa [prefixWord, tailWord_5049612, baseEnd_5049612] using wordTrace_append hprefix tailTrace_5049612
  have hstable : (prefixWord ++ tailWord_5049612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049612).length < 2 ^ (prefixWord ++ tailWord_5049612).sum := by decide
  have hdescent : baseEnd_5049612 < baseStart_5049612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049629 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_5049629 : Nat := 118140960795 + 5049629 * 2 ^ 59
def prefixEnd_5049629 : Nat := 4983230072969 + 3 ^ 40 * 5049629 * 2
def baseEnd_5049629 : Nat := 2592886803882529037014685

theorem tailTrace_5049629 : CollatzResearch.WordTrace tailWord_5049629 prefixEnd_5049629 2592886803882529037014685 := by
  unfold tailWord_5049629
  simp only [CollatzResearch.WordTrace]
  refine ⟨184175100223064015818503941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122783400148709343879002627 184175100223064015818503941)
  ·
    refine ⟨34532831291824502965969489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184175100223064015818503941 34532831291824502965969489)
    ·
      refine ⟨25899623468868377224477117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34532831291824502965969489 25899623468868377224477117)
      ·
        refine ⟨9712358800825641459178919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25899623468868377224477117 9712358800825641459178919)
        ·
          refine ⟨14568538201238462188768379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9712358800825641459178919 14568538201238462188768379)
          ·
            refine ⟨21852807301857693283152569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14568538201238462188768379 21852807301857693283152569)
            ·
              refine ⟨16389605476393269962364427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21852807301857693283152569 16389605476393269962364427)
              ·
                refine ⟨24584408214589904943546641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16389605476393269962364427 24584408214589904943546641)
                ·
                  refine ⟨18438306160942428707659981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24584408214589904943546641 18438306160942428707659981)
                  ·
                    refine ⟨6914364810353410765372493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18438306160942428707659981 6914364810353410765372493)
                    ·
                      refine ⟨2592886803882529037014685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6914364810353410765372493 2592886803882529037014685)
                      ·
                        rfl

theorem cell23_5049629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_5049629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049629 prefixEnd_5049629 := by exact prefixLift 5049629
  have htrace : WordTrace (prefixWord ++ tailWord_5049629) baseStart_5049629 baseEnd_5049629 := by
    simpa [prefixWord, tailWord_5049629, baseEnd_5049629] using wordTrace_append hprefix tailTrace_5049629
  have hstable : (prefixWord ++ tailWord_5049629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049629).length < 2 ^ (prefixWord ++ tailWord_5049629).sum := by decide
  have hdescent : baseEnd_5049629 < baseStart_5049629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049630 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_5049630 : Nat := 118140960795 + 5049630 * 2 ^ 59
def prefixEnd_5049630 : Nat := 4983230072969 + 3 ^ 40 * 5049630 * 2
def baseEnd_5049630 : Nat := 2592887317363183533102181

theorem tailTrace_5049630 : CollatzResearch.WordTrace tailWord_5049630 prefixEnd_5049630 2592887317363183533102181 := by
  unfold tailWord_5049630
  simp only [CollatzResearch.WordTrace]
  refine ⟨23021892087007549123661293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122783424464040261992860229 23021892087007549123661293)
  ·
    refine ⟨8633209532627830921372985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23021892087007549123661293 8633209532627830921372985)
    ·
      refine ⟨6474907149470873191029739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8633209532627830921372985 6474907149470873191029739)
      ·
        refine ⟨9712360724206309786544609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6474907149470873191029739 9712360724206309786544609)
        ·
          refine ⟨7284270543154732339908457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9712360724206309786544609 7284270543154732339908457)
          ·
            refine ⟨5463202907366049254931343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7284270543154732339908457 5463202907366049254931343)
            ·
              refine ⟨8194804361049073882397015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5463202907366049254931343 8194804361049073882397015)
              ·
                refine ⟨12292206541573610823595523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8194804361049073882397015 12292206541573610823595523)
                ·
                  refine ⟨18438309812360416235393285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12292206541573610823595523 18438309812360416235393285)
                  ·
                    refine ⟨3457183089817578044136241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18438309812360416235393285 3457183089817578044136241)
                    ·
                      refine ⟨2592887317363183533102181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3457183089817578044136241 2592887317363183533102181)
                      ·
                        rfl

theorem cell23_5049630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_5049630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049630 prefixEnd_5049630 := by exact prefixLift 5049630
  have htrace : WordTrace (prefixWord ++ tailWord_5049630) baseStart_5049630 baseEnd_5049630 := by
    simpa [prefixWord, tailWord_5049630, baseEnd_5049630] using wordTrace_append hprefix tailTrace_5049630
  have hstable : (prefixWord ++ tailWord_5049630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049630).length < 2 ^ (prefixWord ++ tailWord_5049630).sum := by decide
  have hdescent : baseEnd_5049630 < baseStart_5049630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049655 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 5]
def baseStart_5049655 : Nat := 118140960795 + 5049655 * 2 ^ 59
def prefixEnd_5049655 : Nat := 4983230072969 + 3 ^ 40 * 5049655 * 2
def baseEnd_5049655 : Nat := 2592900154379545935289565

theorem tailTrace_5049655 : CollatzResearch.WordTrace tailWord_5049655 prefixEnd_5049655 2592900154379545935289565 := by
  unfold tailWord_5049655
  simp only [CollatzResearch.WordTrace]
  refine ⟨184176048520969822258950419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122784032347313214839300279 184176048520969822258950419)
  ·
    refine ⟨276264072781454733388425629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184176048520969822258950419 276264072781454733388425629)
    ·
      refine ⟨103599027293045525020659611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276264072781454733388425629 103599027293045525020659611)
      ·
        refine ⟨155398540939568287530989417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103599027293045525020659611 155398540939568287530989417)
        ·
          refine ⟨116548905704676215648242063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155398540939568287530989417 116548905704676215648242063)
          ·
            refine ⟨174823358557014323472363095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116548905704676215648242063 174823358557014323472363095)
            ·
              refine ⟨262235037835521485208544643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174823358557014323472363095 262235037835521485208544643)
              ·
                refine ⟨393352556753282227812816965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262235037835521485208544643 393352556753282227812816965)
                ·
                  refine ⟨73753604391240417714903181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 393352556753282227812816965 73753604391240417714903181)
                  ·
                    refine ⟨27657601646715156643088693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73753604391240417714903181 27657601646715156643088693)
                    ·
                      refine ⟨2592900154379545935289565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27657601646715156643088693 2592900154379545935289565)
                      ·
                        rfl

theorem cell23_5049655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_5049655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049655 prefixEnd_5049655 := by exact prefixLift 5049655
  have htrace : WordTrace (prefixWord ++ tailWord_5049655) baseStart_5049655 baseEnd_5049655 := by
    simpa [prefixWord, tailWord_5049655, baseEnd_5049655] using wordTrace_append hprefix tailTrace_5049655
  have hstable : (prefixWord ++ tailWord_5049655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049655).length < 2 ^ (prefixWord ++ tailWord_5049655).sum := by decide
  have hdescent : baseEnd_5049655 < baseStart_5049655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049670 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_5049670 : Nat := 118140960795 + 5049670 * 2 ^ 59
def prefixEnd_5049670 : Nat := 4983230072969 + 3 ^ 40 * 5049670 * 2
def baseEnd_5049670 : Nat := 288100872954373708511333

theorem tailTrace_5049670 : CollatzResearch.WordTrace tailWord_5049670 prefixEnd_5049670 288100872954373708511333 := by
  unfold tailWord_5049670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5755518612997358744398327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122784397077276986547164309 5755518612997358744398327)
  ·
    refine ⟨8633277919496038116597491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5755518612997358744398327 8633277919496038116597491)
    ·
      refine ⟨12949916879244057174896237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8633277919496038116597491 12949916879244057174896237)
      ·
        refine ⟨4856218829716521440586089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12949916879244057174896237 4856218829716521440586089)
        ·
          refine ⟨3642164122287391080439567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4856218829716521440586089 3642164122287391080439567)
          ·
            refine ⟨5463246183431086620659351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642164122287391080439567 5463246183431086620659351)
            ·
              refine ⟨8194869275146629930989027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5463246183431086620659351 8194869275146629930989027)
              ·
                refine ⟨12292303912719944896483541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8194869275146629930989027 12292303912719944896483541)
                ·
                  refine ⟨288100872954373708511333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12292303912719944896483541 288100872954373708511333)
                  ·
                    rfl

theorem cell23_5049670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_5049670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049670 prefixEnd_5049670 := by exact prefixLift 5049670
  have htrace : WordTrace (prefixWord ++ tailWord_5049670) baseStart_5049670 baseEnd_5049670 := by
    simpa [prefixWord, tailWord_5049670, baseEnd_5049670] using wordTrace_append hprefix tailTrace_5049670
  have hstable : (prefixWord ++ tailWord_5049670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049670).length < 2 ^ (prefixWord ++ tailWord_5049670).sum := by decide
  have hdescent : baseEnd_5049670 < baseStart_5049670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049730 : List Nat := [3, 4, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_5049730 : Nat := 118140960795 + 5049730 * 2 ^ 59
def prefixEnd_5049730 : Nat := 4983230072969 + 3 ^ 40 * 5049730 * 2
def baseEnd_5049730 : Nat := 864312888476211047283907

theorem tailTrace_5049730 : CollatzResearch.WordTrace tailWord_5049730 prefixEnd_5049730 864312888476211047283907 := by
  unfold tailWord_5049730
  simp only [CollatzResearch.WordTrace]
  refine ⟨46044695998924527516982661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122785855997132073378620429 46044695998924527516982661)
  ·
    refine ⟨8633380499798348909434249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46044695998924527516982661 8633380499798348909434249)
    ·
      refine ⟨6475035374848761682075687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8633380499798348909434249 6475035374848761682075687)
      ·
        refine ⟨9712553062273142523113531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6475035374848761682075687 9712553062273142523113531)
        ·
          refine ⟨14568829593409713784670297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9712553062273142523113531 14568829593409713784670297)
          ·
            refine ⟨10926622195057285338502723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14568829593409713784670297 10926622195057285338502723)
            ·
              refine ⟨16389933292585928007754085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10926622195057285338502723 16389933292585928007754085)
              ·
                refine ⟨3073112492359861501453891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16389933292585928007754085 3073112492359861501453891)
                ·
                  refine ⟨4609668738539792252180837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073112492359861501453891 4609668738539792252180837)
                  ·
                    refine ⟨864312888476211047283907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4609668738539792252180837 864312888476211047283907)
                    ·
                      rfl

theorem cell23_5049730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_5049730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049730 prefixEnd_5049730 := by exact prefixLift 5049730
  have htrace : WordTrace (prefixWord ++ tailWord_5049730) baseStart_5049730 baseEnd_5049730 := by
    simpa [prefixWord, tailWord_5049730, baseEnd_5049730] using wordTrace_append hprefix tailTrace_5049730
  have hstable : (prefixWord ++ tailWord_5049730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049730).length < 2 ^ (prefixWord ++ tailWord_5049730).sum := by decide
  have hdescent : baseEnd_5049730 < baseStart_5049730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049759 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 4]
def baseStart_5049759 : Nat := 118140960795 + 5049759 * 2 ^ 59
def prefixEnd_5049759 : Nat := 4983230072969 + 3 ^ 40 * 5049759 * 2
def baseEnd_5049759 : Nat := 2592953556367613528389087

theorem tailTrace_5049759 : CollatzResearch.WordTrace tailWord_5049759 prefixEnd_5049759 2592953556367613528389087 := by
  unfold tailWord_5049759
  simp only [CollatzResearch.WordTrace]
  refine ⟨184179841712593048020736331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122786561141728698680490887 184179841712593048020736331)
  ·
    refine ⟨276269762568889572031104497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184179841712593048020736331 276269762568889572031104497)
    ·
      refine ⟨207202321926667179023328373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276269762568889572031104497 207202321926667179023328373)
      ·
        refine ⟨19425217680625048033437035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 207202321926667179023328373 19425217680625048033437035)
        ·
          refine ⟨29137826520937572050155553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19425217680625048033437035 29137826520937572050155553)
          ·
            refine ⟨21853369890703179037616665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29137826520937572050155553 21853369890703179037616665)
            ·
              refine ⟨16390027418027384278212499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21853369890703179037616665 16390027418027384278212499)
              ·
                refine ⟨24585041127041076417318749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16390027418027384278212499 24585041127041076417318749)
                ·
                  refine ⟨9219390422640403656494531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24585041127041076417318749 9219390422640403656494531)
                  ·
                    refine ⟨13829085633960605484741797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9219390422640403656494531 13829085633960605484741797)
                    ·
                      refine ⟨2592953556367613528389087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13829085633960605484741797 2592953556367613528389087)
                      ·
                        rfl

theorem cell23_5049759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_5049759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049759 prefixEnd_5049759 := by exact prefixLift 5049759
  have htrace : WordTrace (prefixWord ++ tailWord_5049759) baseStart_5049759 baseEnd_5049759 := by
    simpa [prefixWord, tailWord_5049759, baseEnd_5049759] using wordTrace_append hprefix tailTrace_5049759
  have hstable : (prefixWord ++ tailWord_5049759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049759).length < 2 ^ (prefixWord ++ tailWord_5049759).sum := by decide
  have hdescent : baseEnd_5049759 < baseStart_5049759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049773 : List Nat := [1, 5, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_5049773 : Nat := 118140960795 + 5049773 * 2 ^ 59
def prefixEnd_5049773 : Nat := 4983230072969 + 3 ^ 40 * 5049773 * 2
def baseEnd_5049773 : Nat := 864320248365592157871341

theorem tailTrace_5049773 : CollatzResearch.WordTrace tailWord_5049773 prefixEnd_5049773 864320248365592157871341 := by
  unfold tailWord_5049773
  simp only [CollatzResearch.WordTrace]
  refine ⟨184180352334542328411745973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122786901556361552274497315 184180352334542328411745973)
  ·
    refine ⟨17266908031363343288601185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184180352334542328411745973 17266908031363343288601185)
    ·
      refine ⟨12950181023522507466450889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17266908031363343288601185 12950181023522507466450889)
      ·
        refine ⟨9712635767641880599838167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12950181023522507466450889 9712635767641880599838167)
        ·
          refine ⟨14568953651462820899757251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9712635767641880599838167 14568953651462820899757251)
          ·
            refine ⟨21853430477194231349635877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14568953651462820899757251 21853430477194231349635877)
            ·
              refine ⟨4097518214473918378056727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21853430477194231349635877 4097518214473918378056727)
              ·
                refine ⟨6146277321710877567085091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4097518214473918378056727 6146277321710877567085091)
                ·
                  refine ⟨9219415982566316350627637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6146277321710877567085091 9219415982566316350627637)
                  ·
                    refine ⟨864320248365592157871341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9219415982566316350627637 864320248365592157871341)
                    ·
                      rfl

theorem cell23_5049773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_5049773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049773 prefixEnd_5049773 := by exact prefixLift 5049773
  have htrace : WordTrace (prefixWord ++ tailWord_5049773) baseStart_5049773 baseEnd_5049773 := by
    simpa [prefixWord, tailWord_5049773, baseEnd_5049773] using wordTrace_append hprefix tailTrace_5049773
  have hstable : (prefixWord ++ tailWord_5049773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049773).length < 2 ^ (prefixWord ++ tailWord_5049773).sum := by decide
  have hdescent : baseEnd_5049773 < baseStart_5049773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049796 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_5049796 : Nat := 118140960795 + 5049796 * 2 ^ 59
def prefixEnd_5049796 : Nat := 4983230072969 + 3 ^ 40 * 5049796 * 2
def baseEnd_5049796 : Nat := 2592972555151829883626417

theorem tailTrace_5049796 : CollatzResearch.WordTrace tailWord_5049796 prefixEnd_5049796 2592972555151829883626417 := by
  unfold tailWord_5049796
  simp only [CollatzResearch.WordTrace]
  refine ⟨92090595606729501669916621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122787460808972668893222161 92090595606729501669916621)
  ·
    refine ⟨34533973352523563126218733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92090595606729501669916621 34533973352523563126218733)
    ·
      refine ⟨12950240007196336172332025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34533973352523563126218733 12950240007196336172332025)
      ·
        refine ⟨9712680005397252129249019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12950240007196336172332025 9712680005397252129249019)
        ·
          refine ⟨14569020008095878193873529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9712680005397252129249019 14569020008095878193873529)
          ·
            refine ⟨10926765006071908645405147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14569020008095878193873529 10926765006071908645405147)
            ·
              refine ⟨16390147509107862968107721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10926765006071908645405147 16390147509107862968107721)
              ·
                refine ⟨12292610631830897226080791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16390147509107862968107721 12292610631830897226080791)
                ·
                  refine ⟨18438915947746345839121187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12292610631830897226080791 18438915947746345839121187)
                  ·
                    refine ⟨27658373921619518758681781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18438915947746345839121187 27658373921619518758681781)
                    ·
                      refine ⟨2592972555151829883626417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27658373921619518758681781 2592972555151829883626417)
                      ·
                        rfl

theorem cell23_5049796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_5049796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049796 prefixEnd_5049796 := by exact prefixLift 5049796
  have htrace : WordTrace (prefixWord ++ tailWord_5049796) baseStart_5049796 baseEnd_5049796 := by
    simpa [prefixWord, tailWord_5049796, baseEnd_5049796] using wordTrace_append hprefix tailTrace_5049796
  have hstable : (prefixWord ++ tailWord_5049796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049796).length < 2 ^ (prefixWord ++ tailWord_5049796).sum := by decide
  have hdescent : baseEnd_5049796 < baseStart_5049796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049827 : List Nat := [1, 1, 1, 6, 2, 3, 1, 3, 1, 2, 2]
def baseStart_5049827 : Nat := 118140960795 + 5049827 * 2 ^ 59
def prefixEnd_5049827 : Nat := 4983230072969 + 3 ^ 40 * 5049827 * 2
def baseEnd_5049827 : Nat := 2592988473052119262338775

theorem tailTrace_5049827 : CollatzResearch.WordTrace tailWord_5049827 prefixEnd_5049827 2592988473052119262338775 := by
  unfold tailWord_5049827
  simp only [CollatzResearch.WordTrace]
  refine ⟨184182321876346695634211735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122788214584231130422807823 184182321876346695634211735)
  ·
    refine ⟨276273482814520043451317603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184182321876346695634211735 276273482814520043451317603)
    ·
      refine ⟨414410224221780065176976405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276273482814520043451317603 414410224221780065176976405)
      ·
        refine ⟨19425479260395940555170769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 414410224221780065176976405 19425479260395940555170769)
        ·
          refine ⟨14569109445296955416378077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19425479260395940555170769 14569109445296955416378077)
          ·
            refine ⟨5463416041986358281141779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14569109445296955416378077 5463416041986358281141779)
            ·
              refine ⟨8195124062979537421712669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5463416041986358281141779 8195124062979537421712669)
              ·
                refine ⟨3073171523617326533142251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8195124062979537421712669 3073171523617326533142251)
                ·
                  refine ⟨4609757285425989799713377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073171523617326533142251 4609757285425989799713377)
                  ·
                    refine ⟨3457317964069492349785033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4609757285425989799713377 3457317964069492349785033)
                    ·
                      refine ⟨2592988473052119262338775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3457317964069492349785033 2592988473052119262338775)
                      ·
                        rfl

theorem cell23_5049827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_5049827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049827 prefixEnd_5049827 := by exact prefixLift 5049827
  have htrace : WordTrace (prefixWord ++ tailWord_5049827) baseStart_5049827 baseEnd_5049827 := by
    simpa [prefixWord, tailWord_5049827, baseEnd_5049827] using wordTrace_append hprefix tailTrace_5049827
  have hstable : (prefixWord ++ tailWord_5049827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049827).length < 2 ^ (prefixWord ++ tailWord_5049827).sum := by decide
  have hdescent : baseEnd_5049827 < baseStart_5049827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049854 : List Nat := [4, 2, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_5049854 : Nat := 118140960795 + 5049854 * 2 ^ 59
def prefixEnd_5049854 : Nat := 4983230072969 + 3 ^ 40 * 5049854 * 2
def baseEnd_5049854 : Nat := 864334112343263552233717

theorem tailTrace_5049854 : CollatzResearch.WordTrace tailWord_5049854 prefixEnd_5049854 864334112343263552233717 := by
  unfold tailWord_5049854
  simp only [CollatzResearch.WordTrace]
  refine ⟨23022913330906109905680577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122788871098165919496963077 23022913330906109905680577)
  ·
    refine ⟨17267184998179582429260433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23022913330906109905680577 17267184998179582429260433)
    ·
      refine ⟨12950388748634686821945325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17267184998179582429260433 12950388748634686821945325)
      ·
        refine ⟨4856395780738007558229497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12950388748634686821945325 4856395780738007558229497)
        ·
          refine ⟨3642296835553505668672123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4856395780738007558229497 3642296835553505668672123)
          ·
            refine ⟨5463445253330258503008185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642296835553505668672123 5463445253330258503008185)
            ·
              refine ⟨4097583939997693877256139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5463445253330258503008185 4097583939997693877256139)
              ·
                refine ⟨6146375909996540815884209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4097583939997693877256139 6146375909996540815884209)
                ·
                  refine ⟨4609781932497405611913157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6146375909996540815884209 4609781932497405611913157)
                  ·
                    refine ⟨864334112343263552233717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4609781932497405611913157 864334112343263552233717)
                    ·
                      rfl

theorem cell23_5049854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_5049854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049854 prefixEnd_5049854 := by exact prefixLift 5049854
  have htrace : WordTrace (prefixWord ++ tailWord_5049854) baseStart_5049854 baseEnd_5049854 := by
    simpa [prefixWord, tailWord_5049854, baseEnd_5049854] using wordTrace_append hprefix tailTrace_5049854
  have hstable : (prefixWord ++ tailWord_5049854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049854).length < 2 ^ (prefixWord ++ tailWord_5049854).sum := by decide
  have hdescent : baseEnd_5049854 < baseStart_5049854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049860 : List Nat := [2, 3, 2, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_5049860 : Nat := 118140960795 + 5049860 * 2 ^ 59
def prefixEnd_5049860 : Nat := 4983230072969 + 3 ^ 40 * 5049860 * 2
def baseEnd_5049860 : Nat := 2593005417913717633226123

theorem tailTrace_5049860 : CollatzResearch.WordTrace tailWord_5049860 prefixEnd_5049860 2593005417913717633226123 := by
  unfold tailWord_5049860
  simp only [CollatzResearch.WordTrace]
  refine ⟨92091762742613571135081517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122789016990151428180108689 92091762742613571135081517)
  ·
    refine ⟨34534411028480089175655569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92091762742613571135081517 34534411028480089175655569)
    ·
      refine ⟨25900808271360066881741677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34534411028480089175655569 25900808271360066881741677)
      ·
        refine ⟨9712803101760025080653129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25900808271360066881741677 9712803101760025080653129)
        ·
          refine ⟨7284602326320018810489847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9712803101760025080653129 7284602326320018810489847)
          ·
            refine ⟨10926903489480028215734771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7284602326320018810489847 10926903489480028215734771)
            ·
              refine ⟨16390355234220042323602157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10926903489480028215734771 16390355234220042323602157)
              ·
                refine ⟨6146383212832515871350809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16390355234220042323602157 6146383212832515871350809)
                ·
                  refine ⟨4609787409624386903513107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6146383212832515871350809 4609787409624386903513107)
                  ·
                    refine ⟨6914681114436580355269661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4609787409624386903513107 6914681114436580355269661)
                    ·
                      refine ⟨2593005417913717633226123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6914681114436580355269661 2593005417913717633226123)
                      ·
                        rfl

theorem cell23_5049860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_5049860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049860 prefixEnd_5049860 := by exact prefixLift 5049860
  have htrace : WordTrace (prefixWord ++ tailWord_5049860) baseStart_5049860 baseEnd_5049860 := by
    simpa [prefixWord, tailWord_5049860, baseEnd_5049860] using wordTrace_append hprefix tailTrace_5049860
  have hstable : (prefixWord ++ tailWord_5049860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049860).length < 2 ^ (prefixWord ++ tailWord_5049860).sum := by decide
  have hdescent : baseEnd_5049860 < baseStart_5049860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049939 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 4]
def baseStart_5049939 : Nat := 118140960795 + 5049939 * 2 ^ 59
def prefixEnd_5049939 : Nat := 4983230072969 + 3 ^ 40 * 5049939 * 2
def baseEnd_5049939 : Nat := 2593045982885422824138259

theorem tailTrace_5049939 : CollatzResearch.WordTrace tailWord_5049939 prefixEnd_5049939 2593045982885422824138259 := by
  unfold tailWord_5049939
  simp only [CollatzResearch.WordTrace]
  refine ⟨184186406851940938762288871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122790937901293959174859247 184186406851940938762288871)
  ·
    refine ⟨276279610277911408143433307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184186406851940938762288871 276279610277911408143433307)
    ·
      refine ⟨414419415416867112215149961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276279610277911408143433307 414419415416867112215149961)
      ·
        refine ⟨310814561562650334161362471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414419415416867112215149961 310814561562650334161362471)
        ·
          refine ⟨466221842343975501242043707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310814561562650334161362471 466221842343975501242043707)
          ·
            refine ⟨699332763515963251863065561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466221842343975501242043707 699332763515963251863065561)
            ·
              refine ⟨524499572636972438897299171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699332763515963251863065561 524499572636972438897299171)
              ·
                refine ⟨786749358955458658345948757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524499572636972438897299171 786749358955458658345948757)
                ·
                  refine ⟨9219719050259281152491587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 786749358955458658345948757 9219719050259281152491587)
                  ·
                    refine ⟨13829578575388921728737381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9219719050259281152491587 13829578575388921728737381)
                    ·
                      refine ⟨2593045982885422824138259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13829578575388921728737381 2593045982885422824138259)
                      ·
                        rfl

theorem cell23_5049939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 4].length) (baseStart_5049939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049939 prefixEnd_5049939 := by exact prefixLift 5049939
  have htrace : WordTrace (prefixWord ++ tailWord_5049939) baseStart_5049939 baseEnd_5049939 := by
    simpa [prefixWord, tailWord_5049939, baseEnd_5049939] using wordTrace_append hprefix tailTrace_5049939
  have hstable : (prefixWord ++ tailWord_5049939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049939).length < 2 ^ (prefixWord ++ tailWord_5049939).sum := by decide
  have hdescent : baseEnd_5049939 < baseStart_5049939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5049959 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_5049959 : Nat := 118140960795 + 5049959 * 2 ^ 59
def prefixEnd_5049959 : Nat := 4983230072969 + 3 ^ 40 * 5049959 * 2
def baseEnd_5049959 : Nat := 2593056252498512745888167

theorem tailTrace_5049959 : CollatzResearch.WordTrace tailWord_5049959 prefixEnd_5049959 2593056252498512745888167 := by
  unfold tailWord_5049959
  simp only [CollatzResearch.WordTrace]
  refine ⟨184187136311868482178016931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122791424207912321452011287 184187136311868482178016931)
  ·
    refine ⟨276280704467802723267025397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184187136311868482178016931 276280704467802723267025397)
    ·
      refine ⟨25901316043856505306283631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 276280704467802723267025397 25901316043856505306283631)
      ·
        refine ⟨38851974065784757959425447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25901316043856505306283631 38851974065784757959425447)
        ·
          refine ⟨58277961098677136939138171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38851974065784757959425447 58277961098677136939138171)
          ·
            refine ⟨87416941648015705408707257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58277961098677136939138171 87416941648015705408707257)
            ·
              refine ⟨65562706236011779056530443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87416941648015705408707257 65562706236011779056530443)
              ·
                refine ⟨98344059354017668584795665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65562706236011779056530443 98344059354017668584795665)
                ·
                  refine ⟨73758044515513251438596749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98344059354017668584795665 73758044515513251438596749)
                  ·
                    refine ⟨27659266693317469289473781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73758044515513251438596749 27659266693317469289473781)
                    ·
                      refine ⟨2593056252498512745888167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27659266693317469289473781 2593056252498512745888167)
                      ·
                        rfl

theorem cell23_5049959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_5049959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5049959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5049959 prefixEnd_5049959 := by exact prefixLift 5049959
  have htrace : WordTrace (prefixWord ++ tailWord_5049959) baseStart_5049959 baseEnd_5049959 := by
    simpa [prefixWord, tailWord_5049959, baseEnd_5049959] using wordTrace_append hprefix tailTrace_5049959
  have hstable : (prefixWord ++ tailWord_5049959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5049959).length < 2 ^ (prefixWord ++ tailWord_5049959).sum := by decide
  have hdescent : baseEnd_5049959 < baseStart_5049959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5049959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050017 : List Nat := [1, 2, 3, 3, 2, 2, 3, 2, 1, 4]
def baseStart_5050017 : Nat := 118140960795 + 5050017 * 2 ^ 59
def prefixEnd_5050017 : Nat := 4983230072969 + 3 ^ 40 * 5050017 * 2
def baseEnd_5050017 : Nat := 864362011458824506320967

theorem tailTrace_5050017 : CollatzResearch.WordTrace tailWord_5050017 prefixEnd_5050017 864362011458824506320967 := by
  unfold tailWord_5050017
  simp only [CollatzResearch.WordTrace]
  refine ⟨184189251745658358083628305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122792834497105572055752203 184189251745658358083628305)
  ·
    refine ⟨138141938809243768562721229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184189251745658358083628305 138141938809243768562721229)
    ·
      refine ⟨51803227053466413211020461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138141938809243768562721229 51803227053466413211020461)
      ·
        refine ⟨19426210145049904954132673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51803227053466413211020461 19426210145049904954132673)
        ·
          refine ⟨14569657608787428715599505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19426210145049904954132673 14569657608787428715599505)
          ·
            refine ⟨10927243206590571536699629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14569657608787428715599505 10927243206590571536699629)
            ·
              refine ⟨4097716202471464326262361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10927243206590571536699629 4097716202471464326262361)
              ·
                refine ⟨3073287151853598244696771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4097716202471464326262361 3073287151853598244696771)
                ·
                  refine ⟨4609930727780397367045157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073287151853598244696771 4609930727780397367045157)
                  ·
                    refine ⟨864362011458824506320967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4609930727780397367045157 864362011458824506320967)
                    ·
                      rfl

theorem cell23_5050017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_5050017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050017 prefixEnd_5050017 := by exact prefixLift 5050017
  have htrace : WordTrace (prefixWord ++ tailWord_5050017) baseStart_5050017 baseEnd_5050017 := by
    simpa [prefixWord, tailWord_5050017, baseEnd_5050017] using wordTrace_append hprefix tailTrace_5050017
  have hstable : (prefixWord ++ tailWord_5050017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050017).length < 2 ^ (prefixWord ++ tailWord_5050017).sum := by decide
  have hdescent : baseEnd_5050017 < baseStart_5050017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050030 : List Nat := [4, 1, 4, 1, 2, 1, 1, 3, 6]
def baseStart_5050030 : Nat := 118140960795 + 5050030 * 2 ^ 59
def prefixEnd_5050030 : Nat := 4983230072969 + 3 ^ 40 * 5050030 * 2
def baseEnd_5050030 : Nat := 288121412180553552011149

theorem tailTrace_5050030 : CollatzResearch.WordTrace tailWord_5050030 prefixEnd_5050030 288121412180553552011149 := by
  unfold tailWord_5050030
  simp only [CollatzResearch.WordTrace]
  refine ⟨23023715736826407662981443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122793150596407507535901029 23023715736826407662981443)
  ·
    refine ⟨34535573605239611494472165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23023715736826407662981443 34535573605239611494472165)
    ·
      refine ⟨6475420050982427155213531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34535573605239611494472165 6475420050982427155213531)
      ·
        refine ⟨9713130076473640732820297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6475420050982427155213531 9713130076473640732820297)
        ·
          refine ⟨7284847557355230549615223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9713130076473640732820297 7284847557355230549615223)
          ·
            refine ⟨10927271336032845824422835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7284847557355230549615223 10927271336032845824422835)
            ·
              refine ⟨16390907004049268736634253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10927271336032845824422835 16390907004049268736634253)
              ·
                refine ⟨6146590126518475776237845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16390907004049268736634253 6146590126518475776237845)
                ·
                  refine ⟨288121412180553552011149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6146590126518475776237845 288121412180553552011149)
                  ·
                    rfl

theorem cell23_5050030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_5050030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050030 prefixEnd_5050030 := by exact prefixLift 5050030
  have htrace : WordTrace (prefixWord ++ tailWord_5050030) baseStart_5050030 baseEnd_5050030 := by
    simpa [prefixWord, tailWord_5050030, baseEnd_5050030] using wordTrace_append hprefix tailTrace_5050030
  have hstable : (prefixWord ++ tailWord_5050030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050030).length < 2 ^ (prefixWord ++ tailWord_5050030).sum := by decide
  have hdescent : baseEnd_5050030 < baseStart_5050030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050056 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 1, 6]
def baseStart_5050056 : Nat := 118140960795 + 5050056 * 2 ^ 59
def prefixEnd_5050056 : Nat := 4983230072969 + 3 ^ 40 * 5050056 * 2
def baseEnd_5050056 : Nat := 864368686707332955458407

theorem tailTrace_5050056 : CollatzResearch.WordTrace tailWord_5050056 prefixEnd_5050056 864368686707332955458407 := by
  unfold tailWord_5050056
  simp only [CollatzResearch.WordTrace]
  refine ⟨92095337096258533872149011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122793782795011378496198681 92095337096258533872149011)
  ·
    refine ⟨138143005644387800808223517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92095337096258533872149011 138143005644387800808223517)
    ·
      refine ⟨51803627116645425303083819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138143005644387800808223517 51803627116645425303083819)
      ·
        refine ⟨77705440674968137954625729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51803627116645425303083819 77705440674968137954625729)
        ·
          refine ⟨58279080506226103465969297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77705440674968137954625729 58279080506226103465969297)
          ·
            refine ⟨43709310379669577599476973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58279080506226103465969297 43709310379669577599476973)
            ·
              refine ⟨16390991392376091599803865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43709310379669577599476973 16390991392376091599803865)
              ·
                refine ⟨12293243544282068699852899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16390991392376091599803865 12293243544282068699852899)
                ·
                  refine ⟨18439865316423103049779349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12293243544282068699852899 18439865316423103049779349)
                  ·
                    refine ⟨864368686707332955458407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18439865316423103049779349 864368686707332955458407)
                    ·
                      rfl

theorem cell23_5050056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_5050056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050056 prefixEnd_5050056 := by exact prefixLift 5050056
  have htrace : WordTrace (prefixWord ++ tailWord_5050056) baseStart_5050056 baseEnd_5050056 := by
    simpa [prefixWord, tailWord_5050056, baseEnd_5050056] using wordTrace_append hprefix tailTrace_5050056
  have hstable : (prefixWord ++ tailWord_5050056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050056).length < 2 ^ (prefixWord ++ tailWord_5050056).sum := by decide
  have hdescent : baseEnd_5050056 < baseStart_5050056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050069 : List Nat := [1, 3, 2, 17]
def baseStart_5050069 : Nat := 118140960795 + 5050069 * 2 ^ 59
def prefixEnd_5050069 : Nat := 4983230072969 + 3 ^ 40 * 5050069 * 2
def baseEnd_5050069 : Nat := 1185693980507776550303

theorem tailTrace_5050069 : CollatzResearch.WordTrace tailWord_5050069 prefixEnd_5050069 1185693980507776550303 := by
  unfold tailWord_5050069
  simp only [CollatzResearch.WordTrace]
  refine ⟨184191148341469970964521261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122794098894313313976347507 184191148341469970964521261)
  ·
    refine ⟨69071680628051239111695473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184191148341469970964521261 69071680628051239111695473)
    ·
      refine ⟨51803760471038429333771605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69071680628051239111695473 51803760471038429333771605)
      ·
        refine ⟨1185693980507776550303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 51803760471038429333771605 1185693980507776550303)
        ·
          rfl

theorem cell23_5050069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 17].length) (baseStart_5050069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050069 prefixEnd_5050069 := by exact prefixLift 5050069
  have htrace : WordTrace (prefixWord ++ tailWord_5050069) baseStart_5050069 baseEnd_5050069 := by
    simpa [prefixWord, tailWord_5050069, baseEnd_5050069] using wordTrace_append hprefix tailTrace_5050069
  have hstable : (prefixWord ++ tailWord_5050069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050069).length < 2 ^ (prefixWord ++ tailWord_5050069).sum := by decide
  have hdescent : baseEnd_5050069 < baseStart_5050069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050073 : List Nat := [1, 2, 1, 2, 3, 3, 1, 4, 2, 4]
def baseStart_5050073 : Nat := 118140960795 + 5050073 * 2 ^ 59
def prefixEnd_5050073 : Nat := 4983230072969 + 3 ^ 40 * 5050073 * 2
def baseEnd_5050073 : Nat := 864371596431041766620881

theorem tailTrace_5050073 : CollatzResearch.WordTrace tailWord_5050073 prefixEnd_5050073 864371596431041766620881 := by
  unfold tailWord_5050073
  simp only [CollatzResearch.WordTrace]
  refine ⟨184191294233455479647666873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122794196155636986431777915 184191294233455479647666873)
  ·
    refine ⟨138143470675091609735750155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184191294233455479647666873 138143470675091609735750155)
    ·
      refine ⟨207215206012637414603625233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138143470675091609735750155 207215206012637414603625233)
      ·
        refine ⟨155411404509478060952718925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207215206012637414603625233 155411404509478060952718925)
        ·
          refine ⟨58279276691054272857269597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155411404509478060952718925 58279276691054272857269597)
          ·
            refine ⟨21854728759145352321476099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58279276691054272857269597 21854728759145352321476099)
            ·
              refine ⟨32782093138718028482214149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21854728759145352321476099 32782093138718028482214149)
              ·
                refine ⟨6146642463509630340415153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32782093138718028482214149 6146642463509630340415153)
                ·
                  refine ⟨4609981847632222755311365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6146642463509630340415153 4609981847632222755311365)
                  ·
                    refine ⟨864371596431041766620881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4609981847632222755311365 864371596431041766620881)
                    ·
                      rfl

theorem cell23_5050073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 4].length) (baseStart_5050073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050073 prefixEnd_5050073 := by exact prefixLift 5050073
  have htrace : WordTrace (prefixWord ++ tailWord_5050073) baseStart_5050073 baseEnd_5050073 := by
    simpa [prefixWord, tailWord_5050073, baseEnd_5050073] using wordTrace_append hprefix tailTrace_5050073
  have hstable : (prefixWord ++ tailWord_5050073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050073).length < 2 ^ (prefixWord ++ tailWord_5050073).sum := by decide
  have hdescent : baseEnd_5050073 < baseStart_5050073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050074 : List Nat := [3, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3]
def baseStart_5050074 : Nat := 118140960795 + 5050074 * 2 ^ 59
def prefixEnd_5050074 : Nat := 4983230072969 + 3 ^ 40 * 5050074 * 2
def baseEnd_5050074 : Nat := 2593115302773779795950139

theorem tailTrace_5050074 : CollatzResearch.WordTrace tailWord_5050074 prefixEnd_5050074 2593115302773779795950139 := by
  unfold tailWord_5050074
  simp only [CollatzResearch.WordTrace]
  refine ⟨46047832676612964204613319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122794220470967904545635517 46047832676612964204613319)
  ·
    refine ⟨69071749014919446306919979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46047832676612964204613319 69071749014919446306919979)
    ·
      refine ⟨103607623522379169460379969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69071749014919446306919979 103607623522379169460379969)
      ·
        refine ⟨77705717641784377095284977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103607623522379169460379969 77705717641784377095284977)
        ·
          refine ⟨58279288231338282821463733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77705717641784377095284977 58279288231338282821463733)
          ·
            refine ⟨5463683271687964014512225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58279288231338282821463733 5463683271687964014512225)
            ·
              refine ⟨4097762453765973010884169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5463683271687964014512225 4097762453765973010884169)
              ·
                refine ⟨3073321840324479758163127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4097762453765973010884169 3073321840324479758163127)
                ·
                  refine ⟨4609982760486719637244691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073321840324479758163127 4609982760486719637244691)
                  ·
                    refine ⟨6914974140730079455867037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4609982760486719637244691 6914974140730079455867037)
                    ·
                      refine ⟨2593115302773779795950139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6914974140730079455867037 2593115302773779795950139)
                      ·
                        rfl

theorem cell23_5050074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_5050074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050074 prefixEnd_5050074 := by exact prefixLift 5050074
  have htrace : WordTrace (prefixWord ++ tailWord_5050074) baseStart_5050074 baseEnd_5050074 := by
    simpa [prefixWord, tailWord_5050074, baseEnd_5050074] using wordTrace_append hprefix tailTrace_5050074
  have hstable : (prefixWord ++ tailWord_5050074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050074).length < 2 ^ (prefixWord ++ tailWord_5050074).sum := by decide
  have hdescent : baseEnd_5050074 < baseStart_5050074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050093 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_5050093 : Nat := 118140960795 + 5050093 * 2 ^ 59
def prefixEnd_5050093 : Nat := 4983230072969 + 3 ^ 40 * 5050093 * 2
def baseEnd_5050093 : Nat := 2593125058906215221612551

theorem tailTrace_5050093 : CollatzResearch.WordTrace tailWord_5050093 prefixEnd_5050093 2593125058906215221612551 := by
  unfold tailWord_5050093
  simp only [CollatzResearch.WordTrace]
  refine ⟨184192023693383023063394933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122794682462255348708929955 184192023693383023063394933)
  ·
    refine ⟨17268002221254658412193275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184192023693383023063394933 17268002221254658412193275)
    ·
      refine ⟨25902003331881987618289913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17268002221254658412193275 25902003331881987618289913)
      ·
        refine ⟨19426502498911490713717435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25902003331881987618289913 19426502498911490713717435)
        ·
          refine ⟨29139753748367236070576153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19426502498911490713717435 29139753748367236070576153)
          ·
            refine ⟨21854815311275427052932115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29139753748367236070576153 21854815311275427052932115)
            ·
              refine ⟨32782222966913140579398173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21854815311275427052932115 32782222966913140579398173)
              ·
                refine ⟨12293333612592427717274315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32782222966913140579398173 12293333612592427717274315)
                ·
                  refine ⟨18440000418888641575911473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12293333612592427717274315 18440000418888641575911473)
                  ·
                    refine ⟨13830000314166481181933605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18440000418888641575911473 13830000314166481181933605)
                    ·
                      refine ⟨2593125058906215221612551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13830000314166481181933605 2593125058906215221612551)
                      ·
                        rfl

theorem cell23_5050093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_5050093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050093 prefixEnd_5050093 := by exact prefixLift 5050093
  have htrace : WordTrace (prefixWord ++ tailWord_5050093) baseStart_5050093 baseEnd_5050093 := by
    simpa [prefixWord, tailWord_5050093, baseEnd_5050093] using wordTrace_append hprefix tailTrace_5050093
  have hstable : (prefixWord ++ tailWord_5050093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050093).length < 2 ^ (prefixWord ++ tailWord_5050093).sum := by decide
  have hdescent : baseEnd_5050093 < baseStart_5050093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050113 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_5050113 : Nat := 118140960795 + 5050113 * 2 ^ 59
def prefixEnd_5050113 : Nat := 4983230072969 + 3 ^ 40 * 5050113 * 2
def baseEnd_5050113 : Nat := 2593135328519305143362459

theorem tailTrace_5050113 : CollatzResearch.WordTrace tailWord_5050113 prefixEnd_5050113 2593135328519305143362459 := by
  unfold tailWord_5050113
  simp only [CollatzResearch.WordTrace]
  refine ⟨184192753153310566479122993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122795168768873710986081995 184192753153310566479122993)
  ·
    refine ⟨138144564864982924859342245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184192753153310566479122993 138144564864982924859342245)
    ·
      refine ⟨25902105912184298411126671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138144564864982924859342245 25902105912184298411126671)
      ·
        refine ⟨38853158868276447616690007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25902105912184298411126671 38853158868276447616690007)
        ·
          refine ⟨58279738302414671425035011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38853158868276447616690007 58279738302414671425035011)
          ·
            refine ⟨87419607453622007137552517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58279738302414671425035011 87419607453622007137552517)
            ·
              refine ⟨16391176397554126338291097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87419607453622007137552517 16391176397554126338291097)
              ·
                refine ⟨12293382298165594753718323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16391176397554126338291097 12293382298165594753718323)
                ·
                  refine ⟨18440073447248392130577485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12293382298165594753718323 18440073447248392130577485)
                  ·
                    refine ⟨6915027542718147048966557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18440073447248392130577485 6915027542718147048966557)
                    ·
                      refine ⟨2593135328519305143362459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6915027542718147048966557 2593135328519305143362459)
                      ·
                        rfl

theorem cell23_5050113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_5050113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050113 prefixEnd_5050113 := by exact prefixLift 5050113
  have htrace : WordTrace (prefixWord ++ tailWord_5050113) baseStart_5050113 baseEnd_5050113 := by
    simpa [prefixWord, tailWord_5050113, baseEnd_5050113] using wordTrace_append hprefix tailTrace_5050113
  have hstable : (prefixWord ++ tailWord_5050113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050113).length < 2 ^ (prefixWord ++ tailWord_5050113).sum := by decide
  have hdescent : baseEnd_5050113 < baseStart_5050113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050136 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 1, 5, 4]
def baseStart_5050136 : Nat := 118140960795 + 5050136 * 2 ^ 59
def prefixEnd_5050136 : Nat := 4983230072969 + 3 ^ 40 * 5050136 * 2
def baseEnd_5050136 : Nat := 2593147138574358553374853

theorem tailTrace_5050136 : CollatzResearch.WordTrace tailWord_5050136 prefixEnd_5050136 2593147138574358553374853 := by
  unfold tailWord_5050136
  simp only [CollatzResearch.WordTrace]
  refine ⟨92096796016113620703605131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122795728021484827604806841 92096796016113620703605131)
  ·
    refine ⟨138145194024170431055407697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92096796016113620703605131 138145194024170431055407697)
    ·
      refine ⟨103608895518127823291555773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138145194024170431055407697 103608895518127823291555773)
      ·
        refine ⟨38853335819297933734333415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103608895518127823291555773 38853335819297933734333415)
        ·
          refine ⟨58280003728946900601500123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38853335819297933734333415 58280003728946900601500123)
          ·
            refine ⟨87420005593420350902250185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58280003728946900601500123 87420005593420350902250185)
            ·
              refine ⟨65565004195065263176687639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87420005593420350902250185 65565004195065263176687639)
              ·
                refine ⟨98347506292597894765031459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65565004195065263176687639 98347506292597894765031459)
                ·
                  refine ⟨147521259438896842147547189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98347506292597894765031459 147521259438896842147547189)
                  ·
                    refine ⟨13830118072396578951332549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 147521259438896842147547189 13830118072396578951332549)
                    ·
                      refine ⟨2593147138574358553374853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13830118072396578951332549 2593147138574358553374853)
                      ·
                        rfl

theorem cell23_5050136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_5050136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050136 prefixEnd_5050136 := by exact prefixLift 5050136
  have htrace : WordTrace (prefixWord ++ tailWord_5050136) baseStart_5050136 baseEnd_5050136 := by
    simpa [prefixWord, tailWord_5050136, baseEnd_5050136] using wordTrace_append hprefix tailTrace_5050136
  have hstable : (prefixWord ++ tailWord_5050136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050136).length < 2 ^ (prefixWord ++ tailWord_5050136).sum := by decide
  have hdescent : baseEnd_5050136 < baseStart_5050136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050173 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_5050173 : Nat := 118140960795 + 5050173 * 2 ^ 59
def prefixEnd_5050173 : Nat := 4983230072969 + 3 ^ 40 * 5050173 * 2
def baseEnd_5050173 : Nat := 2593166137358574908612183

theorem tailTrace_5050173 : CollatzResearch.WordTrace tailWord_5050173 prefixEnd_5050173 2593166137358574908612183 := by
  unfold tailWord_5050173
  simp only [CollatzResearch.WordTrace]
  refine ⟨184194941533093196726307173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122796627688728797817538115 184194941533093196726307173)
  ·
    refine ⟨34536551537454974386182595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184194941533093196726307173 34536551537454974386182595)
    ·
      refine ⟨51804827306182461579273893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34536551537454974386182595 51804827306182461579273893)
      ·
        refine ⟨9713405119909211546113855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51804827306182461579273893 9713405119909211546113855)
        ·
          refine ⟨14570107679863817319170783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9713405119909211546113855 14570107679863817319170783)
          ·
            refine ⟨21855161519795725978756175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14570107679863817319170783 21855161519795725978756175)
            ·
              refine ⟨32782742279693588968134263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21855161519795725978756175 32782742279693588968134263)
              ·
                refine ⟨49174113419540383452201395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32782742279693588968134263 49174113419540383452201395)
                ·
                  refine ⟨73761170129310575178302093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49174113419540383452201395 73761170129310575178302093)
                  ·
                    refine ⟨27660438798491465691863285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73761170129310575178302093 27660438798491465691863285)
                    ·
                      refine ⟨2593166137358574908612183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27660438798491465691863285 2593166137358574908612183)
                      ·
                        rfl

theorem cell23_5050173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_5050173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050173 prefixEnd_5050173 := by exact prefixLift 5050173
  have htrace : WordTrace (prefixWord ++ tailWord_5050173) baseStart_5050173 baseEnd_5050173 := by
    simpa [prefixWord, tailWord_5050173, baseEnd_5050173] using wordTrace_append hprefix tailTrace_5050173
  have hstable : (prefixWord ++ tailWord_5050173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050173).length < 2 ^ (prefixWord ++ tailWord_5050173).sum := by decide
  have hdescent : baseEnd_5050173 < baseStart_5050173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050186 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_5050186 : Nat := 118140960795 + 5050186 * 2 ^ 59
def prefixEnd_5050186 : Nat := 4983230072969 + 3 ^ 40 * 5050186 * 2
def baseEnd_5050186 : Nat := 2593172812607083357749623

theorem tailTrace_5050186 : CollatzResearch.WordTrace tailWord_5050186 prefixEnd_5050186 2593172812607083357749623 := by
  unfold tailWord_5050186
  simp only [CollatzResearch.WordTrace]
  refine ⟨46048853920511524986632603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122796943788030733297686941 46048853920511524986632603)
  ·
    refine ⟨69073280880767287479948905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46048853920511524986632603 69073280880767287479948905)
    ·
      refine ⟨51804960660575465609961679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69073280880767287479948905 51804960660575465609961679)
      ·
        refine ⟨77707440990863198414942519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51804960660575465609961679 77707440990863198414942519)
        ·
          refine ⟨116561161486294797622413779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77707440990863198414942519 116561161486294797622413779)
          ·
            refine ⟨174841742229442196433620669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116561161486294797622413779 174841742229442196433620669)
            ·
              refine ⟨65565653336040823662607751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174841742229442196433620669 65565653336040823662607751)
              ·
                refine ⟨98348480004061235493911627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65565653336040823662607751 98348480004061235493911627)
                ·
                  refine ⟨147522720006091853240867441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98348480004061235493911627 147522720006091853240867441)
                  ·
                    refine ⟨110642040004568889930650581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 147522720006091853240867441 110642040004568889930650581)
                    ·
                      refine ⟨2593172812607083357749623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110642040004568889930650581 2593172812607083357749623)
                      ·
                        rfl

theorem cell23_5050186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_5050186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050186 prefixEnd_5050186 := by exact prefixLift 5050186
  have htrace : WordTrace (prefixWord ++ tailWord_5050186) baseStart_5050186 baseEnd_5050186 := by
    simpa [prefixWord, tailWord_5050186, baseEnd_5050186] using wordTrace_append hprefix tailTrace_5050186
  have hstable : (prefixWord ++ tailWord_5050186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050186).length < 2 ^ (prefixWord ++ tailWord_5050186).sum := by decide
  have hdescent : baseEnd_5050186 < baseStart_5050186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050193 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 7]
def baseStart_5050193 : Nat := 118140960795 + 5050193 * 2 ^ 59
def prefixEnd_5050193 : Nat := 4983230072969 + 3 ^ 40 * 5050193 * 2
def baseEnd_5050193 : Nat := 288130711885740536706899

theorem tailTrace_5050193 : CollatzResearch.WordTrace tailWord_5050193 prefixEnd_5050193 288130711885740536706899 := by
  unfold tailWord_5050193
  simp only [CollatzResearch.WordTrace]
  refine ⟨184195670993020740142035233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122797113995347160094690155 184195670993020740142035233)
  ·
    refine ⟨138146753244765555106526425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184195670993020740142035233 138146753244765555106526425)
    ·
      refine ⟨103610064933574166329894819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138146753244765555106526425 103610064933574166329894819)
      ·
        refine ⟨155415097400361249494842229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103610064933574166329894819 155415097400361249494842229)
        ·
          refine ⟨14570165381283867140141459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155415097400361249494842229 14570165381283867140141459)
          ·
            refine ⟨21855248071925800710212189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14570165381283867140141459 21855248071925800710212189)
            ·
              refine ⟨8195718026972175266329571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21855248071925800710212189 8195718026972175266329571)
              ·
                refine ⟨12293577040458262899494357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8195718026972175266329571 12293577040458262899494357)
                ·
                  refine ⟨288130711885740536706899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12293577040458262899494357 288130711885740536706899)
                  ·
                    rfl

theorem cell23_5050193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 7].length) (baseStart_5050193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050193 prefixEnd_5050193 := by exact prefixLift 5050193
  have htrace : WordTrace (prefixWord ++ tailWord_5050193) baseStart_5050193 baseEnd_5050193 := by
    simpa [prefixWord, tailWord_5050193, baseEnd_5050193] using wordTrace_append hprefix tailTrace_5050193
  have hstable : (prefixWord ++ tailWord_5050193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050193).length < 2 ^ (prefixWord ++ tailWord_5050193).sum := by decide
  have hdescent : baseEnd_5050193 < baseStart_5050193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050274 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_5050274 : Nat := 118140960795 + 5050274 * 2 ^ 59
def prefixEnd_5050274 : Nat := 4983230072969 + 3 ^ 40 * 5050274 * 2
def baseEnd_5050274 : Nat := 864405999634893004483073

theorem tailTrace_5050274 : CollatzResearch.WordTrace tailWord_5050274 prefixEnd_5050274 864405999634893004483073 := by
  unfold tailWord_5050274
  simp only [CollatzResearch.WordTrace]
  refine ⟨46049656326431822743933469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122799083537151527317155917 46049656326431822743933469)
  ·
    refine ⟨17268621122411933528975051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46049656326431822743933469 17268621122411933528975051)
    ·
      refine ⟨25902931683617900293462577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17268621122411933528975051 25902931683617900293462577)
      ·
        refine ⟨19427198762713425220096933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25902931683617900293462577 19427198762713425220096933)
        ·
          refine ⟨3642599768008767228768175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19427198762713425220096933 3642599768008767228768175)
          ·
            refine ⟨5463899652013150843152263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642599768008767228768175 5463899652013150843152263)
            ·
              refine ⟨8195849478019726264728395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5463899652013150843152263 8195849478019726264728395)
              ·
                refine ⟨12293774217029589397092593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8195849478019726264728395 12293774217029589397092593)
                ·
                  refine ⟨9220330662772192047819445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12293774217029589397092593 9220330662772192047819445)
                  ·
                    refine ⟨864405999634893004483073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9220330662772192047819445 864405999634893004483073)
                    ·
                      rfl

theorem cell23_5050274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_5050274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050274 prefixEnd_5050274 := by exact prefixLift 5050274
  have htrace : WordTrace (prefixWord ++ tailWord_5050274) baseStart_5050274 baseEnd_5050274 := by
    simpa [prefixWord, tailWord_5050274, baseEnd_5050274] using wordTrace_append hprefix tailTrace_5050274
  have hstable : (prefixWord ++ tailWord_5050274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050274).length < 2 ^ (prefixWord ++ tailWord_5050274).sum := by decide
  have hdescent : baseEnd_5050274 < baseStart_5050274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050287 : List Nat := [1, 1, 2, 1, 2, 2, 6, 3, 1, 4]
def baseStart_5050287 : Nat := 118140960795 + 5050287 * 2 ^ 59
def prefixEnd_5050287 : Nat := 4983230072969 + 3 ^ 40 * 5050287 * 2
def baseEnd_5050287 : Nat := 864408224717729154195553

theorem tailTrace_5050287 : CollatzResearch.WordTrace tailWord_5050287 prefixEnd_5050287 864408224717729154195553 := by
  unfold tailWord_5050287
  simp only [CollatzResearch.WordTrace]
  refine ⟨184199099454680194195957115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122799399636453462797304743 184199099454680194195957115)
  ·
    refine ⟨276298649182020291293935673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184199099454680194195957115 276298649182020291293935673)
    ·
      refine ⟨207223986886515218470451755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276298649182020291293935673 207223986886515218470451755)
      ·
        refine ⟨310835980329772827705677633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207223986886515218470451755 310835980329772827705677633)
        ·
          refine ⟨233126985247329620779258225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310835980329772827705677633 233126985247329620779258225)
          ·
            refine ⟨174845238935497215584443669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233126985247329620779258225 174845238935497215584443669)
            ·
              refine ⟨8195870575101431980520797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 174845238935497215584443669 8195870575101431980520797)
              ·
                refine ⟨3073451465663036992695299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8195870575101431980520797 3073451465663036992695299)
                ·
                  refine ⟨4610177198494555489042949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073451465663036992695299 4610177198494555489042949)
                  ·
                    refine ⟨864408224717729154195553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4610177198494555489042949 864408224717729154195553)
                    ·
                      rfl

theorem cell23_5050287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 1, 4].length) (baseStart_5050287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050287 prefixEnd_5050287 := by exact prefixLift 5050287
  have htrace : WordTrace (prefixWord ++ tailWord_5050287) baseStart_5050287 baseEnd_5050287 := by
    simpa [prefixWord, tailWord_5050287, baseEnd_5050287] using wordTrace_append hprefix tailTrace_5050287
  have hstable : (prefixWord ++ tailWord_5050287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050287).length < 2 ^ (prefixWord ++ tailWord_5050287).sum := by decide
  have hdescent : baseEnd_5050287 < baseStart_5050287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050320 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 1, 5, 2]
def baseStart_5050320 : Nat := 118140960795 + 5050320 * 2 ^ 59
def prefixEnd_5050320 : Nat := 4983230072969 + 3 ^ 40 * 5050320 * 2
def baseEnd_5050320 : Nat := 2593241619014785833474007

theorem tailTrace_5050320 : CollatzResearch.WordTrace tailWord_5050320 prefixEnd_5050320 2593241619014785833474007 := by
  unfold tailWord_5050320
  simp only [CollatzResearch.WordTrace]
  refine ⟨92100151531780320415954207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122800202042373760554605609 92100151531780320415954207)
  ·
    refine ⟨138150227297670480623931311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92100151531780320415954207 138150227297670480623931311)
    ·
      refine ⟨207225340946505720935896967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138150227297670480623931311 207225340946505720935896967)
      ·
        refine ⟨310838011419758581403845451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207225340946505720935896967 310838011419758581403845451)
        ·
          refine ⟨466257017129637872105768177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310838011419758581403845451 466257017129637872105768177)
          ·
            refine ⟨349692762847228404079326133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 466257017129637872105768177 349692762847228404079326133)
            ·
              refine ⟨32783696516927662882436825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 349692762847228404079326133 32783696516927662882436825)
              ·
                refine ⟨24587772387695747161827619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32783696516927662882436825 24587772387695747161827619)
                ·
                  refine ⟨36881658581543620742741429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24587772387695747161827619 36881658581543620742741429)
                  ·
                    refine ⟨3457655492019714444632009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36881658581543620742741429 3457655492019714444632009)
                    ·
                      refine ⟨2593241619014785833474007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3457655492019714444632009 2593241619014785833474007)
                      ·
                        rfl

theorem cell23_5050320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 1, 5, 2].length) (baseStart_5050320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050320 prefixEnd_5050320 := by exact prefixLift 5050320
  have htrace : WordTrace (prefixWord ++ tailWord_5050320) baseStart_5050320 baseEnd_5050320 := by
    simpa [prefixWord, tailWord_5050320, baseEnd_5050320] using wordTrace_append hprefix tailTrace_5050320
  have hstable : (prefixWord ++ tailWord_5050320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050320).length < 2 ^ (prefixWord ++ tailWord_5050320).sum := by decide
  have hdescent : baseEnd_5050320 < baseStart_5050320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050338 : List Nat := [3, 3, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_5050338 : Nat := 118140960795 + 5050338 * 2 ^ 59
def prefixEnd_5050338 : Nat := 4983230072969 + 3 ^ 40 * 5050338 * 2
def baseEnd_5050338 : Nat := 864416953888855587682975

theorem tailTrace_5050338 : CollatzResearch.WordTrace tailWord_5050338 prefixEnd_5050338 864416953888855587682975 := by
  unfold tailWord_5050338
  simp only [CollatzResearch.WordTrace]
  refine ⟨46050239894373857476515917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122800639718330286604042445 46050239894373857476515917)
  ·
    refine ⟨17268839960390196553693469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46050239894373857476515917 17268839960390196553693469)
    ·
      refine ⟨6475814985146323707635051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17268839960390196553693469 6475814985146323707635051)
      ·
        refine ⟨9713722477719485561452577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6475814985146323707635051 9713722477719485561452577)
        ·
          refine ⟨7285291858289614171089433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9713722477719485561452577 7285291858289614171089433)
          ·
            refine ⟨5463968893717210628317075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7285291858289614171089433 5463968893717210628317075)
            ·
              refine ⟨8195953340575815942475613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5463968893717210628317075 8195953340575815942475613)
              ·
                refine ⟨3073482502715930978428355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8195953340575815942475613 3073482502715930978428355)
                ·
                  refine ⟨4610223754073896467642533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073482502715930978428355 4610223754073896467642533)
                  ·
                    refine ⟨864416953888855587682975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4610223754073896467642533 864416953888855587682975)
                    ·
                      rfl

theorem cell23_5050338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_5050338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050338 prefixEnd_5050338 := by exact prefixLift 5050338
  have htrace : WordTrace (prefixWord ++ tailWord_5050338) baseStart_5050338 baseEnd_5050338 := by
    simpa [prefixWord, tailWord_5050338, baseEnd_5050338] using wordTrace_append hprefix tailTrace_5050338
  have hstable : (prefixWord ++ tailWord_5050338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050338).length < 2 ^ (prefixWord ++ tailWord_5050338).sum := by decide
  have hdescent : baseEnd_5050338 < baseStart_5050338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050360 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 4, 4]
def baseStart_5050360 : Nat := 118140960795 + 5050360 * 2 ^ 59
def prefixEnd_5050360 : Nat := 4983230072969 + 3 ^ 40 * 5050360 * 2
def baseEnd_5050360 : Nat := 864420719413655225657941

theorem tailTrace_5050360 : CollatzResearch.WordTrace tailWord_5050360 prefixEnd_5050360 864420719413655225657941 := by
  unfold tailWord_5050360
  simp only [CollatzResearch.WordTrace]
  refine ⟨92100880991707863831682267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122801174655610485108909689 92100880991707863831682267)
  ·
    refine ⟨138151321487561795747523401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92100880991707863831682267 138151321487561795747523401)
    ·
      refine ⟨103613491115671346810642551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138151321487561795747523401 103613491115671346810642551)
      ·
        refine ⟨155420236673507020215963827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103613491115671346810642551 155420236673507020215963827)
        ·
          refine ⟨233130355010260530323945741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155420236673507020215963827 233130355010260530323945741)
          ·
            refine ⟨87423883128847698871479653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233130355010260530323945741 87423883128847698871479653)
            ·
              refine ⟨16391978086658943538402435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87423883128847698871479653 16391978086658943538402435)
              ·
                refine ⟨24587967129988415307603653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16391978086658943538402435 24587967129988415307603653)
                ·
                  refine ⟨4610243836872827870175685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24587967129988415307603653 4610243836872827870175685)
                  ·
                    refine ⟨864420719413655225657941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4610243836872827870175685 864420719413655225657941)
                    ·
                      rfl

theorem cell23_5050360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_5050360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050360 prefixEnd_5050360 := by exact prefixLift 5050360
  have htrace : WordTrace (prefixWord ++ tailWord_5050360) baseStart_5050360 baseEnd_5050360 := by
    simpa [prefixWord, tailWord_5050360, baseEnd_5050360] using wordTrace_append hprefix tailTrace_5050360
  have hstable : (prefixWord ++ tailWord_5050360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050360).length < 2 ^ (prefixWord ++ tailWord_5050360).sum := by decide
  have hdescent : baseEnd_5050360 < baseStart_5050360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050361 : List Nat := [1, 2, 1, 3, 1, 5, 3, 2, 1, 1, 3]
def baseStart_5050361 : Nat := 118140960795 + 5050361 * 2 ^ 59
def prefixEnd_5050361 : Nat := 4983230072969 + 3 ^ 40 * 5050361 * 2
def baseEnd_5050361 : Nat := 2593262671721620173061319

theorem tailTrace_5050361 : CollatzResearch.WordTrace tailWord_5050361 prefixEnd_5050361 2593262671721620173061319 := by
  unfold tailWord_5050361
  simp only [CollatzResearch.WordTrace]
  refine ⟨184201798456412104834150937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122801198970941403222767291 184201798456412104834150937)
  ·
    refine ⟨138151348842309078625613203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184201798456412104834150937 138151348842309078625613203)
    ·
      refine ⟨207227023263463617938419805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138151348842309078625613203 207227023263463617938419805)
      ·
        refine ⟨77710133723798856726907427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207227023263463617938419805 77710133723798856726907427)
        ·
          refine ⟨116565200585698285090361141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77710133723798856726907427 116565200585698285090361141)
          ·
            refine ⟨10927987554909214227221357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116565200585698285090361141 10927987554909214227221357)
            ·
              refine ⟨4097995333090955335208009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10927987554909214227221357 4097995333090955335208009)
              ·
                refine ⟨3073496499818216501406007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4097995333090955335208009 3073496499818216501406007)
                ·
                  refine ⟨4610244749727324752109011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073496499818216501406007 4610244749727324752109011)
                  ·
                    refine ⟨6915367124590987128163517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4610244749727324752109011 6915367124590987128163517)
                    ·
                      refine ⟨2593262671721620173061319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6915367124590987128163517 2593262671721620173061319)
                      ·
                        rfl

theorem cell23_5050361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_5050361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050361 prefixEnd_5050361 := by exact prefixLift 5050361
  have htrace : WordTrace (prefixWord ++ tailWord_5050361) baseStart_5050361 baseEnd_5050361 := by
    simpa [prefixWord, tailWord_5050361, baseEnd_5050361] using wordTrace_append hprefix tailTrace_5050361
  have hstable : (prefixWord ++ tailWord_5050361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050361).length < 2 ^ (prefixWord ++ tailWord_5050361).sum := by decide
  have hdescent : baseEnd_5050361 < baseStart_5050361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050363 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 6]
def baseStart_5050363 : Nat := 118140960795 + 5050363 * 2 ^ 59
def prefixEnd_5050363 : Nat := 4983230072969 + 3 ^ 40 * 5050363 * 2
def baseEnd_5050363 : Nat := 2593263698682929165236309

theorem tailTrace_5050363 : CollatzResearch.WordTrace tailWord_5050363 prefixEnd_5050363 2593263698682929165236309 := by
  unfold tailWord_5050363
  simp only [CollatzResearch.WordTrace]
  refine ⟨184201871402404859175723743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122801247601603239450482495 184201871402404859175723743)
  ·
    refine ⟨276302807103607288763585615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184201871402404859175723743 276302807103607288763585615)
    ·
      refine ⟨414454210655410933145378423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276302807103607288763585615 414454210655410933145378423)
      ·
        refine ⟨621681315983116399718067635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414454210655410933145378423 621681315983116399718067635)
        ·
          refine ⟨932521973974674599577101453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621681315983116399718067635 932521973974674599577101453)
          ·
            refine ⟨349695740240502974841413045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 932521973974674599577101453 349695740240502974841413045)
            ·
              refine ⟨32783975647547153891382473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 349695740240502974841413045 32783975647547153891382473)
              ·
                refine ⟨24587981735660365418536855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32783975647547153891382473 24587981735660365418536855)
                ·
                  refine ⟨36881972603490548127805283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24587981735660365418536855 36881972603490548127805283)
                  ·
                    refine ⟨55322958905235822191707925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36881972603490548127805283 55322958905235822191707925)
                    ·
                      refine ⟨2593263698682929165236309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55322958905235822191707925 2593263698682929165236309)
                      ·
                        rfl

theorem cell23_5050363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 6].length) (baseStart_5050363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050363 prefixEnd_5050363 := by exact prefixLift 5050363
  have htrace : WordTrace (prefixWord ++ tailWord_5050363) baseStart_5050363 baseEnd_5050363 := by
    simpa [prefixWord, tailWord_5050363, baseEnd_5050363] using wordTrace_append hprefix tailTrace_5050363
  have hstable : (prefixWord ++ tailWord_5050363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050363).length < 2 ^ (prefixWord ++ tailWord_5050363).sum := by decide
  have hdescent : baseEnd_5050363 < baseStart_5050363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050373 : List Nat := [1, 3, 1, 1, 2, 4, 1, 10]
def baseStart_5050373 : Nat := 118140960795 + 5050373 * 2 ^ 59
def prefixEnd_5050373 : Nat := 4983230072969 + 3 ^ 40 * 5050373 * 2
def baseEnd_5050373 : Nat := 96046993832943486152269

theorem tailTrace_5050373 : CollatzResearch.WordTrace tailWord_5050373 prefixEnd_5050373 96046993832943486152269 := by
  unfold tailWord_5050373
  simp only [CollatzResearch.WordTrace]
  refine ⟨184202236132368630883587773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122801490754912420589058515 184202236132368630883587773)
  ·
    refine ⟨69075838549638236581345415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184202236132368630883587773 69075838549638236581345415)
    ·
      refine ⟨103613757824457354872018123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69075838549638236581345415 103613757824457354872018123)
      ·
        refine ⟨155420636736686032308027185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103613757824457354872018123 155420636736686032308027185)
        ·
          refine ⟨116565477552514524231020389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155420636736686032308027185 116565477552514524231020389)
          ·
            refine ⟨21856027041096473293316323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116565477552514524231020389 21856027041096473293316323)
            ·
              refine ⟨32784040561644709939974485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21856027041096473293316323 32784040561644709939974485)
              ·
                refine ⟨96046993832943486152269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32784040561644709939974485 96046993832943486152269)
                ·
                  rfl

theorem cell23_5050373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 10].length) (baseStart_5050373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050373 prefixEnd_5050373 := by exact prefixLift 5050373
  have htrace : WordTrace (prefixWord ++ tailWord_5050373) baseStart_5050373 baseEnd_5050373 := by
    simpa [prefixWord, tailWord_5050373, baseEnd_5050373] using wordTrace_append hprefix tailTrace_5050373
  have hstable : (prefixWord ++ tailWord_5050373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050373).length < 2 ^ (prefixWord ++ tailWord_5050373).sum := by decide
  have hdescent : baseEnd_5050373 < baseStart_5050373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050380 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 1, 2, 4]
def baseStart_5050380 : Nat := 118140960795 + 5050380 * 2 ^ 59
def prefixEnd_5050380 : Nat := 4983230072969 + 3 ^ 40 * 5050380 * 2
def baseEnd_5050380 : Nat := 2593272427854055598723731

theorem tailTrace_5050380 : CollatzResearch.WordTrace tailWord_5050380 prefixEnd_5050380 2593272427854055598723731 := by
  unfold tailWord_5050380
  simp only [CollatzResearch.WordTrace]
  refine ⟨92101245721671635539546297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122801660962228847386061729 92101245721671635539546297)
  ·
    refine ⟨69075934291253726654659723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92101245721671635539546297 69075934291253726654659723)
    ·
      refine ⟨103613901436880589981989585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69075934291253726654659723 103613901436880589981989585)
      ·
        refine ⟨77710426077660442486492189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103613901436880589981989585 77710426077660442486492189)
        ·
          refine ⟨29141409779122665932434571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77710426077660442486492189 29141409779122665932434571)
          ·
            refine ⟨43712114668683998898651857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29141409779122665932434571 43712114668683998898651857)
            ·
              refine ⟨32784086001512999173988893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43712114668683998898651857 32784086001512999173988893)
              ·
                refine ⟨12294032250567374690245835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32784086001512999173988893 12294032250567374690245835)
                ·
                  refine ⟨18441048375851062035368753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12294032250567374690245835 18441048375851062035368753)
                  ·
                    refine ⟨13830786281888296526526565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18441048375851062035368753 13830786281888296526526565)
                    ·
                      refine ⟨2593272427854055598723731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13830786281888296526526565 2593272427854055598723731)
                      ·
                        rfl

theorem cell23_5050380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_5050380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050380 prefixEnd_5050380 := by exact prefixLift 5050380
  have htrace : WordTrace (prefixWord ++ tailWord_5050380) baseStart_5050380 baseEnd_5050380 := by
    simpa [prefixWord, tailWord_5050380, baseEnd_5050380] using wordTrace_append hprefix tailTrace_5050380
  have hstable : (prefixWord ++ tailWord_5050380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050380).length < 2 ^ (prefixWord ++ tailWord_5050380).sum := by decide
  have hdescent : baseEnd_5050380 < baseStart_5050380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050381 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_5050381 : Nat := 118140960795 + 5050381 * 2 ^ 59
def prefixEnd_5050381 : Nat := 4983230072969 + 3 ^ 40 * 5050381 * 2
def baseEnd_5050381 : Nat := 864424313778236698270409

theorem tailTrace_5050381 : CollatzResearch.WordTrace tailWord_5050381 prefixEnd_5050381 864424313778236698270409 := by
  unfold tailWord_5050381
  simp only [CollatzResearch.WordTrace]
  refine ⟨184202527916339648249878997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122801685277559765499919331 184202527916339648249878997)
  ·
    refine ⟨4317246748039210505856539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 184202527916339648249878997 4317246748039210505856539)
    ·
      refine ⟨6475870122058815758784809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4317246748039210505856539 6475870122058815758784809)
      ·
        refine ⟨4856902591544111819088607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6475870122058815758784809 4856902591544111819088607)
        ·
          refine ⟨7285353887316167728632911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4856902591544111819088607 7285353887316167728632911)
          ·
            refine ⟨10928030830974251592949367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7285353887316167728632911 10928030830974251592949367)
            ·
              refine ⟨16392046246461377389424051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10928030830974251592949367 16392046246461377389424051)
              ·
                refine ⟨24588069369692066084136077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16392046246461377389424051 24588069369692066084136077)
                ·
                  refine ⟨9220526013634524781551029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24588069369692066084136077 9220526013634524781551029)
                  ·
                    refine ⟨864424313778236698270409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9220526013634524781551029 864424313778236698270409)
                    ·
                      rfl

theorem cell23_5050381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_5050381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050381 prefixEnd_5050381 := by exact prefixLift 5050381
  have htrace : WordTrace (prefixWord ++ tailWord_5050381) baseStart_5050381 baseEnd_5050381 := by
    simpa [prefixWord, tailWord_5050381, baseEnd_5050381] using wordTrace_append hprefix tailTrace_5050381
  have hstable : (prefixWord ++ tailWord_5050381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050381).length < 2 ^ (prefixWord ++ tailWord_5050381).sum := by decide
  have hdescent : baseEnd_5050381 < baseStart_5050381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050387 : List Nat := [1, 1, 1, 2, 1, 4, 5, 2, 1, 2, 3]
def baseStart_5050387 : Nat := 118140960795 + 5050387 * 2 ^ 59
def prefixEnd_5050387 : Nat := 4983230072969 + 3 ^ 40 * 5050387 * 2
def baseEnd_5050387 : Nat := 2593276022218637071336199

theorem tailTrace_5050387 : CollatzResearch.WordTrace tailWord_5050387 prefixEnd_5050387 2593276022218637071336199 := by
  unfold tailWord_5050387
  simp only [CollatzResearch.WordTrace]
  refine ⟨184202746754317911274597415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122801831169545274183064943 184202746754317911274597415)
  ·
    refine ⟨276304120131476866911896123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184202746754317911274597415 276304120131476866911896123)
    ·
      refine ⟨414456180197215300367844185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276304120131476866911896123 414456180197215300367844185)
      ·
        refine ⟨310842135147911475275883139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414456180197215300367844185 310842135147911475275883139)
        ·
          refine ⟨466263202721867212913824709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310842135147911475275883139 466263202721867212913824709)
          ·
            refine ⟨87424350510350102421342133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 466263202721867212913824709 87424350510350102421342133)
            ·
              refine ⟨8196032860345322102000825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87424350510350102421342133 8196032860345322102000825)
              ·
                refine ⟨6147024645258991576500619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8196032860345322102000825 6147024645258991576500619)
                ·
                  refine ⟨9220536967888487364750929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6147024645258991576500619 9220536967888487364750929)
                  ·
                    refine ⟨6915402725916365523563197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9220536967888487364750929 6915402725916365523563197)
                    ·
                      refine ⟨2593276022218637071336199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6915402725916365523563197 2593276022218637071336199)
                      ·
                        rfl

theorem cell23_5050387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 2, 3].length) (baseStart_5050387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050387 prefixEnd_5050387 := by exact prefixLift 5050387
  have htrace : WordTrace (prefixWord ++ tailWord_5050387) baseStart_5050387 baseEnd_5050387 := by
    simpa [prefixWord, tailWord_5050387, baseEnd_5050387] using wordTrace_append hprefix tailTrace_5050387
  have hstable : (prefixWord ++ tailWord_5050387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050387).length < 2 ^ (prefixWord ++ tailWord_5050387).sum := by decide
  have hdescent : baseEnd_5050387 < baseStart_5050387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050388 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_5050388 : Nat := 118140960795 + 5050388 * 2 ^ 59
def prefixEnd_5050388 : Nat := 4983230072969 + 3 ^ 40 * 5050388 * 2
def baseEnd_5050388 : Nat := 2593276535699291567423695

theorem tailTrace_5050388 : CollatzResearch.WordTrace tailWord_5050388 prefixEnd_5050388 2593276535699291567423695 := by
  unfold tailWord_5050388
  simp only [CollatzResearch.WordTrace]
  refine ⟨92101391613657144222691909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122801855484876192296922545 92101391613657144222691909)
  ·
    refine ⟨17269010927560714541754733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92101391613657144222691909 17269010927560714541754733)
    ·
      refine ⟨6475879097835267953158025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17269010927560714541754733 6475879097835267953158025)
      ·
        refine ⟨4856909323376450964868519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6475879097835267953158025 4856909323376450964868519)
        ·
          refine ⟨7285363985064676447302779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4856909323376450964868519 7285363985064676447302779)
          ·
            refine ⟨10928045977597014670954169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7285363985064676447302779 10928045977597014670954169)
            ·
              refine ⟨8196034483197761003215627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10928045977597014670954169 8196034483197761003215627)
              ·
                refine ⟨12294051724796641504823441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8196034483197761003215627 12294051724796641504823441)
                ·
                  refine ⟨9220538793597481128617581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12294051724796641504823441 9220538793597481128617581)
                  ·
                    refine ⟨3457702047599055423231593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9220538793597481128617581 3457702047599055423231593)
                    ·
                      refine ⟨2593276535699291567423695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3457702047599055423231593 2593276535699291567423695)
                      ·
                        rfl

theorem cell23_5050388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_5050388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050388 prefixEnd_5050388 := by exact prefixLift 5050388
  have htrace : WordTrace (prefixWord ++ tailWord_5050388) baseStart_5050388 baseEnd_5050388 := by
    simpa [prefixWord, tailWord_5050388, baseEnd_5050388] using wordTrace_append hprefix tailTrace_5050388
  have hstable : (prefixWord ++ tailWord_5050388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050388).length < 2 ^ (prefixWord ++ tailWord_5050388).sum := by decide
  have hdescent : baseEnd_5050388 < baseStart_5050388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050397 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_5050397 : Nat := 118140960795 + 5050397 * 2 ^ 59
def prefixEnd_5050397 : Nat := 4983230072969 + 3 ^ 40 * 5050397 * 2
def baseEnd_5050397 : Nat := 2593281157025182032211153

theorem tailTrace_5050397 : CollatzResearch.WordTrace tailWord_5050397 prefixEnd_5050397 2593281157025182032211153 := by
  unfold tailWord_5050397
  simp only [CollatzResearch.WordTrace]
  refine ⟨184203111484281682982461445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122802074322854455321640963 184203111484281682982461445)
  ·
    refine ⟨34538083403302815559211521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184203111484281682982461445 34538083403302815559211521)
    ·
      refine ⟨25903562552477111669408641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34538083403302815559211521 25903562552477111669408641)
      ·
        refine ⟨19427671914357833752056481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25903562552477111669408641 19427671914357833752056481)
        ·
          refine ⟨14570753935768375314042361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19427671914357833752056481 14570753935768375314042361)
          ·
            refine ⟨10928065451826281485531771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14570753935768375314042361 10928065451826281485531771)
            ·
              refine ⟨16392098177739422228297657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10928065451826281485531771 16392098177739422228297657)
              ·
                refine ⟨12294073633304566671223243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16392098177739422228297657 12294073633304566671223243)
                ·
                  refine ⟨18441110449956850006834865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12294073633304566671223243 18441110449956850006834865)
                  ·
                    refine ⟨13830832837467637505126149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18441110449956850006834865 13830832837467637505126149)
                    ·
                      refine ⟨2593281157025182032211153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13830832837467637505126149 2593281157025182032211153)
                      ·
                        rfl

theorem cell23_5050397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_5050397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050397 prefixEnd_5050397 := by exact prefixLift 5050397
  have htrace : WordTrace (prefixWord ++ tailWord_5050397) baseStart_5050397 baseEnd_5050397 := by
    simpa [prefixWord, tailWord_5050397, baseEnd_5050397] using wordTrace_append hprefix tailTrace_5050397
  have hstable : (prefixWord ++ tailWord_5050397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050397).length < 2 ^ (prefixWord ++ tailWord_5050397).sum := by decide
  have hdescent : baseEnd_5050397 < baseStart_5050397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050404 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 1, 1, 5]
def baseStart_5050404 : Nat := 118140960795 + 5050404 * 2 ^ 59
def prefixEnd_5050404 : Nat := 4983230072969 + 3 ^ 40 * 5050404 * 2
def baseEnd_5050404 : Nat := 2593284751389763504823621

theorem tailTrace_5050404 : CollatzResearch.WordTrace tailWord_5050404 prefixEnd_5050404 2593284751389763504823621 := by
  unfold tailWord_5050404
  simp only [CollatzResearch.WordTrace]
  refine ⟨92101683397628161588983133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122802244530170882118644177 92101683397628161588983133)
  ·
    refine ⟨34538131274110560595868675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92101683397628161588983133 34538131274110560595868675)
    ·
      refine ⟨51807196911165840893803013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34538131274110560595868675 51807196911165840893803013)
      ·
        refine ⟨9713849420843595167588065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51807196911165840893803013 9713849420843595167588065)
        ·
          refine ⟨7285387065632696375691049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9713849420843595167588065 7285387065632696375691049)
          ·
            refine ⟨5464040299224522281768287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7285387065632696375691049 5464040299224522281768287)
            ·
              refine ⟨8196060448836783422652431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5464040299224522281768287 8196060448836783422652431)
              ·
                refine ⟨12294090673255175133978647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8196060448836783422652431 12294090673255175133978647)
                ·
                  refine ⟨18441136009882762700967971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12294090673255175133978647 18441136009882762700967971)
                  ·
                    refine ⟨27661704014824144051451957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18441136009882762700967971 27661704014824144051451957)
                    ·
                      refine ⟨2593284751389763504823621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27661704014824144051451957 2593284751389763504823621)
                      ·
                        rfl

theorem cell23_5050404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_5050404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050404 prefixEnd_5050404 := by exact prefixLift 5050404
  have htrace : WordTrace (prefixWord ++ tailWord_5050404) baseStart_5050404 baseEnd_5050404 := by
    simpa [prefixWord, tailWord_5050404, baseEnd_5050404] using wordTrace_append hprefix tailTrace_5050404
  have hstable : (prefixWord ++ tailWord_5050404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050404).length < 2 ^ (prefixWord ++ tailWord_5050404).sum := by decide
  have hdescent : baseEnd_5050404 < baseStart_5050404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050407 : List Nat := [1, 1, 7, 1, 3, 10]
def baseStart_5050407 : Nat := 118140960795 + 5050407 * 2 ^ 59
def prefixEnd_5050407 : Nat := 4983230072969 + 3 ^ 40 * 5050407 * 2
def baseEnd_5050407 : Nat := 10671960048690234539449

theorem tailTrace_5050407 : CollatzResearch.WordTrace tailWord_5050407 prefixEnd_5050407 10671960048690234539449 := by
  unfold tailWord_5050407
  simp only [CollatzResearch.WordTrace]
  refine ⟨184203476214245454690325475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122802317476163636460216983 184203476214245454690325475)
  ·
    refine ⟨276305214321368182035488213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184203476214245454690325475 276305214321368182035488213)
    ·
      refine ⟨6475903460657066766456755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 276305214321368182035488213 6475903460657066766456755)
      ·
        refine ⟨9713855190985600149685133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6475903460657066766456755 9713855190985600149685133)
        ·
          refine ⟨3642695696619600056131925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9713855190985600149685133 3642695696619600056131925)
          ·
            refine ⟨10671960048690234539449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3642695696619600056131925 10671960048690234539449)
            ·
              rfl

theorem cell23_5050407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 10].length) (baseStart_5050407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050407 prefixEnd_5050407 := by exact prefixLift 5050407
  have htrace : WordTrace (prefixWord ++ tailWord_5050407) baseStart_5050407 baseEnd_5050407 := by
    simpa [prefixWord, tailWord_5050407, baseEnd_5050407] using wordTrace_append hprefix tailTrace_5050407
  have hstable : (prefixWord ++ tailWord_5050407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050407).length < 2 ^ (prefixWord ++ tailWord_5050407).sum := by decide
  have hdescent : baseEnd_5050407 < baseStart_5050407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050418 : List Nat := [3, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2]
def baseStart_5050418 : Nat := 118140960795 + 5050418 * 2 ^ 59
def prefixEnd_5050418 : Nat := 4983230072969 + 3 ^ 40 * 5050418 * 2
def baseEnd_5050418 : Nat := 2593291940118926450048557

theorem tailTrace_5050418 : CollatzResearch.WordTrace tailWord_5050418 prefixEnd_5050418 2593291940118926450048557 := by
  unfold tailWord_5050418
  simp only [CollatzResearch.WordTrace]
  refine ⟨46050969354301400892243977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122802584944803735712650605 46050969354301400892243977)
  ·
    refine ⟨34538227015726050669182983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46050969354301400892243977 34538227015726050669182983)
    ·
      refine ⟨51807340523589076003774475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34538227015726050669182983 51807340523589076003774475)
      ·
        refine ⟨77711010785383614005661713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51807340523589076003774475 77711010785383614005661713)
        ·
          refine ⟨58283258089037710504246285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77711010785383614005661713 58283258089037710504246285)
          ·
            refine ⟨21856221783389141439092357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58283258089037710504246285 21856221783389141439092357)
            ·
              refine ⟨4098041584385464019829817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21856221783389141439092357 4098041584385464019829817)
              ·
                refine ⟨3073531188289098014872363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4098041584385464019829817 3073531188289098014872363)
                ·
                  refine ⟨4610296782433647022308545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073531188289098014872363 4610296782433647022308545)
                  ·
                    refine ⟨3457722586825235266731409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4610296782433647022308545 3457722586825235266731409)
                    ·
                      refine ⟨2593291940118926450048557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3457722586825235266731409 2593291940118926450048557)
                      ·
                        rfl

theorem cell23_5050418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_5050418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050418 prefixEnd_5050418 := by exact prefixLift 5050418
  have htrace : WordTrace (prefixWord ++ tailWord_5050418) baseStart_5050418 baseEnd_5050418 := by
    simpa [prefixWord, tailWord_5050418, baseEnd_5050418] using wordTrace_append hprefix tailTrace_5050418
  have hstable : (prefixWord ++ tailWord_5050418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050418).length < 2 ^ (prefixWord ++ tailWord_5050418).sum := by decide
  have hdescent : baseEnd_5050418 < baseStart_5050418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050457 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 1, 4, 2]
def baseStart_5050457 : Nat := 118140960795 + 5050457 * 2 ^ 59
def prefixEnd_5050457 : Nat := 4983230072969 + 3 ^ 40 * 5050457 * 2
def baseEnd_5050457 : Nat := 2593311965864451797460877

theorem tailTrace_5050457 : CollatzResearch.WordTrace tailWord_5050457 prefixEnd_5050457 2593311965864451797460877 := by
  unfold tailWord_5050457
  simp only [CollatzResearch.WordTrace]
  refine ⟨184205299864064313229645625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122803533242709542153097083 184205299864064313229645625)
  ·
    refine ⟨138153974898048234922234219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184205299864064313229645625 138153974898048234922234219)
    ·
      refine ⟨207230962347072352383351329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138153974898048234922234219 207230962347072352383351329)
      ·
        refine ⟨155423221760304264287513497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207230962347072352383351329 155423221760304264287513497)
        ·
          refine ⟨116567416320228198215635123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155423221760304264287513497 116567416320228198215635123)
          ·
            refine ⟨174851124480342297323452685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116567416320228198215635123 174851124480342297323452685)
            ·
              refine ⟨65569171680128361496294757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174851124480342297323452685 65569171680128361496294757)
              ·
                refine ⟨12294219690024067780555267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65569171680128361496294757 12294219690024067780555267)
                ·
                  refine ⟨18441329535036101670832901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12294219690024067780555267 18441329535036101670832901)
                  ·
                    refine ⟨3457749287819269063281169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18441329535036101670832901 3457749287819269063281169)
                    ·
                      refine ⟨2593311965864451797460877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3457749287819269063281169 2593311965864451797460877)
                      ·
                        rfl

theorem cell23_5050457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 4, 2].length) (baseStart_5050457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050457 prefixEnd_5050457 := by exact prefixLift 5050457
  have htrace : WordTrace (prefixWord ++ tailWord_5050457) baseStart_5050457 baseEnd_5050457 := by
    simpa [prefixWord, tailWord_5050457, baseEnd_5050457] using wordTrace_append hprefix tailTrace_5050457
  have hstable : (prefixWord ++ tailWord_5050457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050457).length < 2 ^ (prefixWord ++ tailWord_5050457).sum := by decide
  have hdescent : baseEnd_5050457 < baseStart_5050457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050480 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 7]
def baseStart_5050480 : Nat := 118140960795 + 5050480 * 2 ^ 59
def prefixEnd_5050480 : Nat := 4983230072969 + 3 ^ 40 * 5050480 * 2
def baseEnd_5050480 : Nat := 288147086213278356385919

theorem tailTrace_5050480 : CollatzResearch.WordTrace tailWord_5050480 prefixEnd_5050480 288147086213278356385919 := by
  unfold tailWord_5050480
  simp only [CollatzResearch.WordTrace]
  refine ⟨92103069371490494078866447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122804092495320658771821929 92103069371490494078866447)
  ·
    refine ⟨138154604057235741118299671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92103069371490494078866447 138154604057235741118299671)
    ·
      refine ⟨207231906085853611677449507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138154604057235741118299671 207231906085853611677449507)
      ·
        refine ⟨310847859128780417516174261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207231906085853611677449507 310847859128780417516174261)
        ·
          refine ⟨29141986793323164142141337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 310847859128780417516174261 29141986793323164142141337)
          ·
            refine ⟨21856490094992373106606003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29141986793323164142141337 21856490094992373106606003)
            ·
              refine ⟨32784735142488559659909005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21856490094992373106606003 32784735142488559659909005)
              ·
                refine ⟨12294275678433209872465877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32784735142488559659909005 12294275678433209872465877)
                ·
                  refine ⟨288147086213278356385919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12294275678433209872465877 288147086213278356385919)
                  ·
                    rfl

theorem cell23_5050480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 7].length) (baseStart_5050480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050480 prefixEnd_5050480 := by exact prefixLift 5050480
  have htrace : WordTrace (prefixWord ++ tailWord_5050480) baseStart_5050480 baseEnd_5050480 := by
    simpa [prefixWord, tailWord_5050480, baseEnd_5050480] using wordTrace_append hprefix tailTrace_5050480
  have hstable : (prefixWord ++ tailWord_5050480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050480).length < 2 ^ (prefixWord ++ tailWord_5050480).sum := by decide
  have hdescent : baseEnd_5050480 < baseStart_5050480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050527 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 4, 5]
def baseStart_5050527 : Nat := 118140960795 + 5050527 * 2 ^ 59
def prefixEnd_5050527 : Nat := 4983230072969 + 3 ^ 40 * 5050527 * 2
def baseEnd_5050527 : Nat := 864449303170088841195185

theorem tailTrace_5050527 : CollatzResearch.WordTrace tailWord_5050527 prefixEnd_5050527 864449303170088841195185 := by
  unfold tailWord_5050527
  simp only [CollatzResearch.WordTrace]
  refine ⟨184207852973810715184693835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122805235315873810123129223 184207852973810715184693835)
  ·
    refine ⟨276311779460716072777040753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184207852973810715184693835 276311779460716072777040753)
    ·
      refine ⟨207233834595537054582780565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276311779460716072777040753 207233834595537054582780565)
      ·
        refine ⟨9714085996665799433567839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 207233834595537054582780565 9714085996665799433567839)
        ·
          refine ⟨14571128994998699150351759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9714085996665799433567839 14571128994998699150351759)
          ·
            refine ⟨21856693492498048725527639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14571128994998699150351759 21856693492498048725527639)
            ·
              refine ⟨32785040238747073088291459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21856693492498048725527639 32785040238747073088291459)
              ·
                refine ⟨49177560358120609632437189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32785040238747073088291459 49177560358120609632437189)
                ·
                  refine ⟨9220792567147614306081973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49177560358120609632437189 9220792567147614306081973)
                  ·
                    refine ⟨864449303170088841195185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9220792567147614306081973 864449303170088841195185)
                    ·
                      rfl

theorem cell23_5050527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 5].length) (baseStart_5050527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050527 prefixEnd_5050527 := by exact prefixLift 5050527
  have htrace : WordTrace (prefixWord ++ tailWord_5050527) baseStart_5050527 baseEnd_5050527 := by
    simpa [prefixWord, tailWord_5050527, baseEnd_5050527] using wordTrace_append hprefix tailTrace_5050527
  have hstable : (prefixWord ++ tailWord_5050527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050527).length < 2 ^ (prefixWord ++ tailWord_5050527).sum := by decide
  have hdescent : baseEnd_5050527 < baseStart_5050527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050547 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 1, 6, 2]
def baseStart_5050547 : Nat := 118140960795 + 5050547 * 2 ^ 59
def prefixEnd_5050547 : Nat := 4983230072969 + 3 ^ 40 * 5050547 * 2
def baseEnd_5050547 : Nat := 2593358179123356445335463

theorem tailTrace_5050547 : CollatzResearch.WordTrace tailWord_5050547 prefixEnd_5050547 2593358179123356445335463 := by
  unfold tailWord_5050547
  simp only [CollatzResearch.WordTrace]
  refine ⟨184208582433738258600421895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122805721622492172400281263 184208582433738258600421895)
  ·
    refine ⟨276312873650607387900632843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184208582433738258600421895 276312873650607387900632843)
    ·
      refine ⟨414469310475911081850949265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276312873650607387900632843 414469310475911081850949265)
      ·
        refine ⟨310851982856933311388211949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414469310475911081850949265 310851982856933311388211949)
        ·
          refine ⟨116569493571349991770579481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310851982856933311388211949 116569493571349991770579481)
          ·
            refine ⟨87427120178512493827934611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116569493571349991770579481 87427120178512493827934611)
            ·
              refine ⟨131140680267768740741901917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87427120178512493827934611 131140680267768740741901917)
              ·
                refine ⟨49177755100413277778213219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131140680267768740741901917 49177755100413277778213219)
                ·
                  refine ⟨73766632650619916667319829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49177755100413277778213219 73766632650619916667319829)
                  ·
                    refine ⟨3457810905497808593780617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73766632650619916667319829 3457810905497808593780617)
                    ·
                      refine ⟨2593358179123356445335463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3457810905497808593780617 2593358179123356445335463)
                      ·
                        rfl

theorem cell23_5050547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 6, 2].length) (baseStart_5050547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050547 prefixEnd_5050547 := by exact prefixLift 5050547
  have htrace : WordTrace (prefixWord ++ tailWord_5050547) baseStart_5050547 baseEnd_5050547 := by
    simpa [prefixWord, tailWord_5050547, baseEnd_5050547] using wordTrace_append hprefix tailTrace_5050547
  have hstable : (prefixWord ++ tailWord_5050547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050547).length < 2 ^ (prefixWord ++ tailWord_5050547).sum := by decide
  have hdescent : baseEnd_5050547 < baseStart_5050547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050557 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 5, 4]
def baseStart_5050557 : Nat := 118140960795 + 5050557 * 2 ^ 59
def prefixEnd_5050557 : Nat := 4983230072969 + 3 ^ 40 * 5050557 * 2
def baseEnd_5050557 : Nat := 864454437976633802070139

theorem tailTrace_5050557 : CollatzResearch.WordTrace tailWord_5050557 prefixEnd_5050557 864454437976633802070139 := by
  unfold tailWord_5050557
  simp only [CollatzResearch.WordTrace]
  refine ⟨184208947163702030308285925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122805964775801353538857283 184208947163702030308285925)
  ·
    refine ⟨34539177593194130682803611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184208947163702030308285925 34539177593194130682803611)
    ·
      refine ⟨51808766389791196024205417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34539177593194130682803611 51808766389791196024205417)
      ·
        refine ⟨38856574792343397018154063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51808766389791196024205417 38856574792343397018154063)
        ·
          refine ⟨58284862188515095527231095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38856574792343397018154063 58284862188515095527231095)
          ·
            refine ⟨87427293282772643290846643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58284862188515095527231095 87427293282772643290846643)
            ·
              refine ⟨131140939924158964936269965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87427293282772643290846643 131140939924158964936269965)
              ·
                refine ⟨49177852471559611851101237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131140939924158964936269965 49177852471559611851101237)
                ·
                  refine ⟨4610423669208713611040741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49177852471559611851101237 4610423669208713611040741)
                  ·
                    refine ⟨864454437976633802070139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4610423669208713611040741 864454437976633802070139)
                    ·
                      rfl

theorem cell23_5050557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_5050557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050557 prefixEnd_5050557 := by exact prefixLift 5050557
  have htrace : WordTrace (prefixWord ++ tailWord_5050557) baseStart_5050557 baseEnd_5050557 := by
    simpa [prefixWord, tailWord_5050557, baseEnd_5050557] using wordTrace_append hprefix tailTrace_5050557
  have hstable : (prefixWord ++ tailWord_5050557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050557).length < 2 ^ (prefixWord ++ tailWord_5050557).sum := by decide
  have hdescent : baseEnd_5050557 < baseStart_5050557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050561 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 2, 5]
def baseStart_5050561 : Nat := 118140960795 + 5050561 * 2 ^ 59
def prefixEnd_5050561 : Nat := 4983230072969 + 3 ^ 40 * 5050561 * 2
def baseEnd_5050561 : Nat := 864455122617506463520133

theorem tailTrace_5050561 : CollatzResearch.WordTrace tailWord_5050561 prefixEnd_5050561 864455122617506463520133 := by
  unfold tailWord_5050561
  simp only [CollatzResearch.WordTrace]
  refine ⟨184209093055687538991431537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122806062037125025994287691 184209093055687538991431537)
  ·
    refine ⟨138156819791765654243573653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184209093055687538991431537 138156819791765654243573653)
    ·
      refine ⟨6476100927739015042667515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 138156819791765654243573653 6476100927739015042667515)
      ·
        refine ⟨9714151391608522564001273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6476100927739015042667515 9714151391608522564001273)
        ·
          refine ⟨7285613543706391923000955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9714151391608522564001273 7285613543706391923000955)
          ·
            refine ⟨10928420315559587884501433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7285613543706391923000955 10928420315559587884501433)
            ·
              refine ⟨8196315236669690913376075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10928420315559587884501433 8196315236669690913376075)
              ·
                refine ⟨12294472855004536370064113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8196315236669690913376075 12294472855004536370064113)
                ·
                  refine ⟨9220854641253402277548085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12294472855004536370064113 9220854641253402277548085)
                  ·
                    refine ⟨864455122617506463520133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9220854641253402277548085 864455122617506463520133)
                    ·
                      rfl

theorem cell23_5050561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_5050561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050561 prefixEnd_5050561 := by exact prefixLift 5050561
  have htrace : WordTrace (prefixWord ++ tailWord_5050561) baseStart_5050561 baseEnd_5050561 := by
    simpa [prefixWord, tailWord_5050561, baseEnd_5050561] using wordTrace_append hprefix tailTrace_5050561
  have hstable : (prefixWord ++ tailWord_5050561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050561).length < 2 ^ (prefixWord ++ tailWord_5050561).sum := by decide
  have hdescent : baseEnd_5050561 < baseStart_5050561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050564 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_5050564 : Nat := 118140960795 + 5050564 * 2 ^ 59
def prefixEnd_5050564 : Nat := 4983230072969 + 3 ^ 40 * 5050564 * 2
def baseEnd_5050564 : Nat := 2593366908294482878822885

theorem tailTrace_5050564 : CollatzResearch.WordTrace tailWord_5050564 prefixEnd_5050564 2593366908294482878822885 := by
  unfold tailWord_5050564
  simp only [CollatzResearch.WordTrace]
  refine ⟨92104601237338335251895373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122806134983117780335860497 92104601237338335251895373)
  ·
    refine ⟨34539225464001875719460765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92104601237338335251895373 34539225464001875719460765)
    ·
      refine ⟨12952209549000703394797787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34539225464001875719460765 12952209549000703394797787)
      ·
        refine ⟨19428314323501055092196681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12952209549000703394797787 19428314323501055092196681)
        ·
          refine ⟨14571235742625791319147511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19428314323501055092196681 14571235742625791319147511)
          ·
            refine ⟨21856853613938686978721267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14571235742625791319147511 21856853613938686978721267)
            ·
              refine ⟨32785280420908030468081901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21856853613938686978721267 32785280420908030468081901)
              ·
                refine ⟨12294480157840511425530713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32785280420908030468081901 12294480157840511425530713)
                ·
                  refine ⟨9220860118380383569148035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12294480157840511425530713 9220860118380383569148035)
                  ·
                    refine ⟨13831290177570575353722053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9220860118380383569148035 13831290177570575353722053)
                    ·
                      refine ⟨2593366908294482878822885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13831290177570575353722053 2593366908294482878822885)
                      ·
                        rfl

theorem cell23_5050564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_5050564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050564 prefixEnd_5050564 := by exact prefixLift 5050564
  have htrace : WordTrace (prefixWord ++ tailWord_5050564) baseStart_5050564 baseEnd_5050564 := by
    simpa [prefixWord, tailWord_5050564, baseEnd_5050564] using wordTrace_append hprefix tailTrace_5050564
  have hstable : (prefixWord ++ tailWord_5050564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050564).length < 2 ^ (prefixWord ++ tailWord_5050564).sum := by decide
  have hdescent : baseEnd_5050564 < baseStart_5050564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050584 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 2, 2, 3]
def baseStart_5050584 : Nat := 118140960795 + 5050584 * 2 ^ 59
def prefixEnd_5050584 : Nat := 4983230072969 + 3 ^ 40 * 5050584 * 2
def baseEnd_5050584 : Nat := 2593377177907572800572793

theorem tailTrace_5050584 : CollatzResearch.WordTrace tailWord_5050584 prefixEnd_5050584 2593377177907572800572793 := by
  unfold tailWord_5050584
  simp only [CollatzResearch.WordTrace]
  refine ⟨92104965967302106959759403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122806621289736142613012537 92104965967302106959759403)
  ·
    refine ⟨138157448950953160439639105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92104965967302106959759403 138157448950953160439639105)
    ·
      refine ⟨103618086713214870329729329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138157448950953160439639105 103618086713214870329729329)
      ·
        refine ⟨77713565034911152747296997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103618086713214870329729329 77713565034911152747296997)
        ·
          refine ⟨14571293444045841140118187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77713565034911152747296997 14571293444045841140118187)
          ·
            refine ⟨21856940166068761710177281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14571293444045841140118187 21856940166068761710177281)
            ·
              refine ⟨16392705124551571282632961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21856940166068761710177281 16392705124551571282632961)
              ·
                refine ⟨12294528843413678461974721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16392705124551571282632961 12294528843413678461974721)
                ·
                  refine ⟨9220896632560258846481041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12294528843413678461974721 9220896632560258846481041)
                  ·
                    refine ⟨6915672474420194134860781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9220896632560258846481041 6915672474420194134860781)
                    ·
                      refine ⟨2593377177907572800572793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6915672474420194134860781 2593377177907572800572793)
                      ·
                        rfl

theorem cell23_5050584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_5050584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050584 prefixEnd_5050584 := by exact prefixLift 5050584
  have htrace : WordTrace (prefixWord ++ tailWord_5050584) baseStart_5050584 baseEnd_5050584 := by
    simpa [prefixWord, tailWord_5050584, baseEnd_5050584] using wordTrace_append hprefix tailTrace_5050584
  have hstable : (prefixWord ++ tailWord_5050584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050584).length < 2 ^ (prefixWord ++ tailWord_5050584).sum := by decide
  have hdescent : baseEnd_5050584 < baseStart_5050584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050657 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_5050657 : Nat := 118140960795 + 5050657 * 2 ^ 59
def prefixEnd_5050657 : Nat := 4983230072969 + 3 ^ 40 * 5050657 * 2
def baseEnd_5050657 : Nat := 2593414661995351014959957

theorem tailTrace_5050657 : CollatzResearch.WordTrace tailWord_5050657 prefixEnd_5050657 2593414661995351014959957 := by
  unfold tailWord_5050657
  simp only [CollatzResearch.WordTrace]
  refine ⟨184212594463339747386926225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122808396308893164924617483 184212594463339747386926225)
  ·
    refine ⟨138159445847504810540194669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184212594463339747386926225 138159445847504810540194669)
    ·
      refine ⟨51809792192814303952573001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138159445847504810540194669 51809792192814303952573001)
      ·
        refine ⟨38857344144610727964429751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51809792192814303952573001 38857344144610727964429751)
        ·
          refine ⟨58286016216916091946644627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38857344144610727964429751 58286016216916091946644627)
          ·
            refine ⟨87429024325374137919966941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58286016216916091946644627 87429024325374137919966941)
            ·
              refine ⟨32785884122015301719987603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87429024325374137919966941 32785884122015301719987603)
              ·
                refine ⟨49178826183022952579981405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32785884122015301719987603 49178826183022952579981405)
                ·
                  refine ⟨18442059818633607217493027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49178826183022952579981405 18442059818633607217493027)
                  ·
                    refine ⟨27663089727950410826239541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18442059818633607217493027 27663089727950410826239541)
                    ·
                      refine ⟨2593414661995351014959957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27663089727950410826239541 2593414661995351014959957)
                      ·
                        rfl

theorem cell23_5050657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_5050657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050657 prefixEnd_5050657 := by exact prefixLift 5050657
  have htrace : WordTrace (prefixWord ++ tailWord_5050657) baseStart_5050657 baseEnd_5050657 := by
    simpa [prefixWord, tailWord_5050657, baseEnd_5050657] using wordTrace_append hprefix tailTrace_5050657
  have hstable : (prefixWord ++ tailWord_5050657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050657).length < 2 ^ (prefixWord ++ tailWord_5050657).sum := by decide
  have hdescent : baseEnd_5050657 < baseStart_5050657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050671 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 3, 2, 2]
def baseStart_5050671 : Nat := 118140960795 + 5050671 * 2 ^ 59
def prefixEnd_5050671 : Nat := 4983230072969 + 3 ^ 40 * 5050671 * 2
def baseEnd_5050671 : Nat := 2593421850724513960184893

theorem tailTrace_5050671 : CollatzResearch.WordTrace tailWord_5050671 prefixEnd_5050671 2593421850724513960184893 := by
  unfold tailWord_5050671
  simp only [CollatzResearch.WordTrace]
  refine ⟨184213105085289027777935867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122808736723526018518623911 184213105085289027777935867)
  ·
    refine ⟨276319657627933541666903801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184213105085289027777935867 276319657627933541666903801)
    ·
      refine ⟨207239743220950156250177851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276319657627933541666903801 207239743220950156250177851)
      ·
        refine ⟨310859614831425234375266777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207239743220950156250177851 310859614831425234375266777)
        ·
          refine ⟨233144711123568925781450083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310859614831425234375266777 233144711123568925781450083)
          ·
            refine ⟨349717066685353388672175125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233144711123568925781450083 349717066685353388672175125)
            ·
              refine ⟨16392987500875940094008209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 349717066685353388672175125 16392987500875940094008209)
              ·
                refine ⟨12294740625656955070506157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16392987500875940094008209 12294740625656955070506157)
                ·
                  refine ⟨4610527734621358151439809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12294740625656955070506157 4610527734621358151439809)
                  ·
                    refine ⟨3457895800966018613579857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4610527734621358151439809 3457895800966018613579857)
                    ·
                      refine ⟨2593421850724513960184893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3457895800966018613579857 2593421850724513960184893)
                      ·
                        rfl

theorem cell23_5050671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 2, 2].length) (baseStart_5050671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050671 prefixEnd_5050671 := by exact prefixLift 5050671
  have htrace : WordTrace (prefixWord ++ tailWord_5050671) baseStart_5050671 baseEnd_5050671 := by
    simpa [prefixWord, tailWord_5050671, baseEnd_5050671] using wordTrace_append hprefix tailTrace_5050671
  have hstable : (prefixWord ++ tailWord_5050671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050671).length < 2 ^ (prefixWord ++ tailWord_5050671).sum := by decide
  have hdescent : baseEnd_5050671 < baseStart_5050671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050677 : List Nat := [1, 3, 3, 1, 2, 1, 3, 9]
def baseStart_5050677 : Nat := 118140960795 + 5050677 * 2 ^ 59
def prefixEnd_5050677 : Nat := 4983230072969 + 3 ^ 40 * 5050677 * 2
def baseEnd_5050677 : Nat := 96052775244757071729995

theorem tailTrace_5050677 : CollatzResearch.WordTrace tailWord_5050677 prefixEnd_5050677 96052775244757071729995 := by
  unfold tailWord_5050677
  simp only [CollatzResearch.WordTrace]
  refine ⟨184213323923267290802654285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122808882615511527201769523 184213323923267290802654285)
  ·
    refine ⟨69079996471225234050995357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184213323923267290802654285 69079996471225234050995357)
    ·
      refine ⟨25904998676709462769123259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69079996471225234050995357 25904998676709462769123259)
      ·
        refine ⟨38857498015064194153684889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25904998676709462769123259 38857498015064194153684889)
        ·
          refine ⟨29143123511298145615263667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38857498015064194153684889 29143123511298145615263667)
          ·
            refine ⟨43714685266947218422895501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29143123511298145615263667 43714685266947218422895501)
            ·
              refine ⟨16393006975105206908585813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43714685266947218422895501 16393006975105206908585813)
              ·
                refine ⟨96052775244757071729995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16393006975105206908585813 96052775244757071729995)
                ·
                  rfl

theorem cell23_5050677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 9].length) (baseStart_5050677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050677 prefixEnd_5050677 := by exact prefixLift 5050677
  have htrace : WordTrace (prefixWord ++ tailWord_5050677) baseStart_5050677 baseEnd_5050677 := by
    simpa [prefixWord, tailWord_5050677, baseEnd_5050677] using wordTrace_append hprefix tailTrace_5050677
  have hstable : (prefixWord ++ tailWord_5050677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050677).length < 2 ^ (prefixWord ++ tailWord_5050677).sum := by decide
  have hdescent : baseEnd_5050677 < baseStart_5050677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050688 : List Nat := [2, 1, 1, 2, 2, 1, 2, 7, 1, 2, 2]
def baseStart_5050688 : Nat := 118140960795 + 5050688 * 2 ^ 59
def prefixEnd_5050688 : Nat := 4983230072969 + 3 ^ 40 * 5050688 * 2
def baseEnd_5050688 : Nat := 2593430579895640393672315

theorem tailTrace_5050688 : CollatzResearch.WordTrace tailWord_5050688 prefixEnd_5050688 2593430579895640393672315 := by
  unfold tailWord_5050688
  simp only [CollatzResearch.WordTrace]
  refine ⟨92106862563113719840652359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122809150084151626454203145 92106862563113719840652359)
  ·
    refine ⟨138160293844670579760978539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92106862563113719840652359 138160293844670579760978539)
    ·
      refine ⟨207240440767005869641467809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138160293844670579760978539 207240440767005869641467809)
      ·
        refine ⟨155430330575254402231100857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207240440767005869641467809 155430330575254402231100857)
        ·
          refine ⟨116572747931440801673325643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155430330575254402231100857 116572747931440801673325643)
          ·
            refine ⟨174859121897161202509988465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116572747931440801673325643 174859121897161202509988465)
            ·
              refine ⟨131144341422870901882491349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174859121897161202509988465 131144341422870901882491349)
              ·
                refine ⟨3073695502098536762870891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 131144341422870901882491349 3073695502098536762870891)
                ·
                  refine ⟨4610543253147805144306337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073695502098536762870891 4610543253147805144306337)
                  ·
                    refine ⟨3457907439860853858229753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4610543253147805144306337 3457907439860853858229753)
                    ·
                      refine ⟨2593430579895640393672315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3457907439860853858229753 2593430579895640393672315)
                      ·
                        rfl

theorem cell23_5050688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 1, 2, 2].length) (baseStart_5050688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050688 prefixEnd_5050688 := by exact prefixLift 5050688
  have htrace : WordTrace (prefixWord ++ tailWord_5050688) baseStart_5050688 baseEnd_5050688 := by
    simpa [prefixWord, tailWord_5050688, baseEnd_5050688] using wordTrace_append hprefix tailTrace_5050688
  have hstable : (prefixWord ++ tailWord_5050688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050688).length < 2 ^ (prefixWord ++ tailWord_5050688).sum := by decide
  have hdescent : baseEnd_5050688 < baseStart_5050688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050714 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2]
def baseStart_5050714 : Nat := 118140960795 + 5050714 * 2 ^ 59
def prefixEnd_5050714 : Nat := 4983230072969 + 3 ^ 40 * 5050714 * 2
def baseEnd_5050714 : Nat := 2593443930392657291947195

theorem tailTrace_5050714 : CollatzResearch.WordTrace tailWord_5050714 prefixEnd_5050714 2593443930392657291947195 := by
  unfold tailWord_5050714
  simp only [CollatzResearch.WordTrace]
  refine ⟨46053668356033311530437799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122809782282755497414500797 46053668356033311530437799)
  ·
    refine ⟨69080502534049967295656699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46053668356033311530437799 69080502534049967295656699)
    ·
      refine ⟨103620753801074950943485049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69080502534049967295656699 103620753801074950943485049)
      ·
        refine ⟨77715565350806213207613787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103620753801074950943485049 77715565350806213207613787)
        ·
          refine ⟨116573348026209319811420681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77715565350806213207613787 116573348026209319811420681)
          ·
            refine ⟨87430011019656989858565511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116573348026209319811420681 87430011019656989858565511)
            ·
              refine ⟨131145016529485484787848267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87430011019656989858565511 131145016529485484787848267)
              ·
                refine ⟨196717524794228227181772401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131145016529485484787848267 196717524794228227181772401)
                ·
                  refine ⟨147538143595671170386329301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196717524794228227181772401 147538143595671170386329301)
                  ·
                    refine ⟨3457925240523543055929593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 147538143595671170386329301 3457925240523543055929593)
                    ·
                      refine ⟨2593443930392657291947195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3457925240523543055929593 2593443930392657291947195)
                      ·
                        rfl

theorem cell23_5050714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_5050714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050714 prefixEnd_5050714 := by exact prefixLift 5050714
  have htrace : WordTrace (prefixWord ++ tailWord_5050714) baseStart_5050714 baseEnd_5050714 := by
    simpa [prefixWord, tailWord_5050714, baseEnd_5050714] using wordTrace_append hprefix tailTrace_5050714
  have hstable : (prefixWord ++ tailWord_5050714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050714).length < 2 ^ (prefixWord ++ tailWord_5050714).sum := by decide
  have hdescent : baseEnd_5050714 < baseStart_5050714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050737 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 4, 6]
def baseStart_5050737 : Nat := 118140960795 + 5050737 * 2 ^ 59
def prefixEnd_5050737 : Nat := 4983230072969 + 3 ^ 40 * 5050737 * 2
def baseEnd_5050737 : Nat := 864485246815903567319863

theorem tailTrace_5050737 : CollatzResearch.WordTrace tailWord_5050737 prefixEnd_5050737 864485246815903567319863 := by
  unfold tailWord_5050737
  simp only [CollatzResearch.WordTrace]
  refine ⟨184215512303049921049838465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122810341535366614033225643 184215512303049921049838465)
  ·
    refine ⟨138161634227287440787378849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184215512303049921049838465 138161634227287440787378849)
    ·
      refine ⟨103621225670465580590534137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138161634227287440787378849 103621225670465580590534137)
      ·
        refine ⟨77715919252849185442900603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103621225670465580590534137 77715919252849185442900603)
        ·
          refine ⟨116573878879273778164350905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77715919252849185442900603 116573878879273778164350905)
          ·
            refine ⟨87430409159455333623263179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116573878879273778164350905 87430409159455333623263179)
            ·
              refine ⟨131145613739183000434894769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87430409159455333623263179 131145613739183000434894769)
              ·
                refine ⟨98359210304387250326171077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131145613739183000434894769 98359210304387250326171077)
                ·
                  refine ⟨18442351932072609436157077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98359210304387250326171077 18442351932072609436157077)
                  ·
                    refine ⟨864485246815903567319863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18442351932072609436157077 864485246815903567319863)
                    ·
                      rfl

theorem cell23_5050737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_5050737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050737 prefixEnd_5050737 := by exact prefixLift 5050737
  have htrace : WordTrace (prefixWord ++ tailWord_5050737) baseStart_5050737 baseEnd_5050737 := by
    simpa [prefixWord, tailWord_5050737, baseEnd_5050737] using wordTrace_append hprefix tailTrace_5050737
  have hstable : (prefixWord ++ tailWord_5050737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050737).length < 2 ^ (prefixWord ++ tailWord_5050737).sum := by decide
  have hdescent : baseEnd_5050737 < baseStart_5050737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050742 : List Nat := [5, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3]
def baseStart_5050742 : Nat := 118140960795 + 5050742 * 2 ^ 59
def prefixEnd_5050742 : Nat := 4983230072969 + 3 ^ 40 * 5050742 * 2
def baseEnd_5050742 : Nat := 2593458307850983182397067

theorem tailTrace_5050742 : CollatzResearch.WordTrace tailWord_5050742 prefixEnd_5050742 2593458307850983182397067 := by
  unfold tailWord_5050742
  simp only [CollatzResearch.WordTrace]
  refine ⟨11513480916751987931485655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122810463112021204602513653 11513480916751987931485655)
  ·
    refine ⟨17270221375127981897228483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11513480916751987931485655 17270221375127981897228483)
    ·
      refine ⟨25905332062691972845842725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17270221375127981897228483 25905332062691972845842725)
      ·
        refine ⟨4857249761754744908595511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25905332062691972845842725 4857249761754744908595511)
        ·
          refine ⟨7285874642632117362893267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4857249761754744908595511 7285874642632117362893267)
          ·
            refine ⟨10928811963948176044339901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7285874642632117362893267 10928811963948176044339901)
            ·
              refine ⟨4098304486480566016627463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10928811963948176044339901 4098304486480566016627463)
              ·
                refine ⟨6147456729720849024941195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4098304486480566016627463 6147456729720849024941195)
                ·
                  refine ⟨9221185094581273537411793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6147456729720849024941195 9221185094581273537411793)
                  ·
                    refine ⟨6915888820935955153058845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9221185094581273537411793 6915888820935955153058845)
                    ·
                      refine ⟨2593458307850983182397067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6915888820935955153058845 2593458307850983182397067)
                      ·
                        rfl

theorem cell23_5050742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_5050742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050742 prefixEnd_5050742 := by exact prefixLift 5050742
  have htrace : WordTrace (prefixWord ++ tailWord_5050742) baseStart_5050742 baseEnd_5050742 := by
    simpa [prefixWord, tailWord_5050742, baseEnd_5050742] using wordTrace_append hprefix tailTrace_5050742
  have hstable : (prefixWord ++ tailWord_5050742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050742).length < 2 ^ (prefixWord ++ tailWord_5050742).sum := by decide
  have hdescent : baseEnd_5050742 < baseStart_5050742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050757 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 2, 3, 6]
def baseStart_5050757 : Nat := 118140960795 + 5050757 * 2 ^ 59
def prefixEnd_5050757 : Nat := 4983230072969 + 3 ^ 40 * 5050757 * 2
def baseEnd_5050757 : Nat := 2593466010060800623709497

theorem tailTrace_5050757 : CollatzResearch.WordTrace tailWord_5050757 prefixEnd_5050757 2593466010060800623709497 := by
  unfold tailWord_5050757
  simp only [CollatzResearch.WordTrace]
  refine ⟨184216241762977464465566525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122810827841984976310377683 184216241762977464465566525)
  ·
    refine ⟨69081090661116549174587447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184216241762977464465566525 69081090661116549174587447)
    ·
      refine ⟨103621635991674823761881171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69081090661116549174587447 103621635991674823761881171)
      ·
        refine ⟨155432453987512235642821757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103621635991674823761881171 155432453987512235642821757)
        ·
          refine ⟨58287170245317088366058159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155432453987512235642821757 58287170245317088366058159)
          ·
            refine ⟨87430755367975632549087239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58287170245317088366058159 87430755367975632549087239)
            ·
              refine ⟨131146133051963448823630859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87430755367975632549087239 131146133051963448823630859)
              ·
                refine ⟨196719199577945173235446289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131146133051963448823630859 196719199577945173235446289)
                ·
                  refine ⟨147539399683458879926584717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196719199577945173235446289 147539399683458879926584717)
                  ·
                    refine ⟨55327274881297079972469269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 147539399683458879926584717 55327274881297079972469269)
                    ·
                      refine ⟨2593466010060800623709497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55327274881297079972469269 2593466010060800623709497)
                      ·
                        rfl

theorem cell23_5050757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_5050757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050757 prefixEnd_5050757 := by exact prefixLift 5050757
  have htrace : WordTrace (prefixWord ++ tailWord_5050757) baseStart_5050757 baseEnd_5050757 := by
    simpa [prefixWord, tailWord_5050757, baseEnd_5050757] using wordTrace_append hprefix tailTrace_5050757
  have hstable : (prefixWord ++ tailWord_5050757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050757).length < 2 ^ (prefixWord ++ tailWord_5050757).sum := by decide
  have hdescent : baseEnd_5050757 < baseStart_5050757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050764 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 2, 4, 3]
def baseStart_5050764 : Nat := 118140960795 + 5050764 * 2 ^ 59
def prefixEnd_5050764 : Nat := 4983230072969 + 3 ^ 40 * 5050764 * 2
def baseEnd_5050764 : Nat := 2593469604425382096321965

theorem tailTrace_5050764 : CollatzResearch.WordTrace tailWord_5050764 prefixEnd_5050764 2593469604425382096321965 := by
  unfold tailWord_5050764
  simp only [CollatzResearch.WordTrace]
  refine ⟨92108248536976052330535673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122810998049301403107380897 92108248536976052330535673)
  ·
    refine ⟨69081186402732039247901755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92108248536976052330535673 69081186402732039247901755)
    ·
      refine ⟨103621779604098058871852633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69081186402732039247901755 103621779604098058871852633)
      ·
        refine ⟨77716334703073544153889475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103621779604098058871852633 77716334703073544153889475)
        ·
          refine ⟨116574502054610316230834213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77716334703073544153889475 116574502054610316230834213)
          ·
            refine ⟨21857719135239434293281415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116574502054610316230834213 21857719135239434293281415)
            ·
              refine ⟨32786578702859151439922123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21857719135239434293281415 32786578702859151439922123)
              ·
                refine ⟨49179868054288727159883185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32786578702859151439922123 49179868054288727159883185)
                ·
                  refine ⟨36884901040716545369912389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49179868054288727159883185 36884901040716545369912389)
                  ·
                    refine ⟨6915918945134352256858573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36884901040716545369912389 6915918945134352256858573)
                    ·
                      refine ⟨2593469604425382096321965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6915918945134352256858573 2593469604425382096321965)
                      ·
                        rfl

theorem cell23_5050764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_5050764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050764 prefixEnd_5050764 := by exact prefixLift 5050764
  have htrace : WordTrace (prefixWord ++ tailWord_5050764) baseStart_5050764 baseEnd_5050764 := by
    simpa [prefixWord, tailWord_5050764, baseEnd_5050764] using wordTrace_append hprefix tailTrace_5050764
  have hstable : (prefixWord ++ tailWord_5050764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050764).length < 2 ^ (prefixWord ++ tailWord_5050764).sum := by decide
  have hdescent : baseEnd_5050764 < baseStart_5050764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050778 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2]
def baseStart_5050778 : Nat := 118140960795 + 5050778 * 2 ^ 59
def prefixEnd_5050778 : Nat := 4983230072969 + 3 ^ 40 * 5050778 * 2
def baseEnd_5050778 : Nat := 2593476793154545041546901

theorem tailTrace_5050778 : CollatzResearch.WordTrace tailWord_5050778 prefixEnd_5050778 2593476793154545041546901 := by
  unfold tailWord_5050778
  simp only [CollatzResearch.WordTrace]
  refine ⟨46054251923975346263020247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122811338463934256701387325 46054251923975346263020247)
  ·
    refine ⟨69081377885963019394530371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46054251923975346263020247 69081377885963019394530371)
    ·
      refine ⟨103622066828944529091795557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69081377885963019394530371 103622066828944529091795557)
      ·
        refine ⟨19429137530427099204711667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103622066828944529091795557 19429137530427099204711667)
        ·
          refine ⟨29143706295640648807067501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19429137530427099204711667 29143706295640648807067501)
          ·
            refine ⟨10928889860865243302650313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29143706295640648807067501 10928889860865243302650313)
            ·
              refine ⟨8196667395648932476987735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10928889860865243302650313 8196667395648932476987735)
              ·
                refine ⟨12295001093473398715481603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8196667395648932476987735 12295001093473398715481603)
                ·
                  refine ⟨18442501640210098073222405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12295001093473398715481603 18442501640210098073222405)
                  ·
                    refine ⟨3457969057539393388729201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18442501640210098073222405 3457969057539393388729201)
                    ·
                      refine ⟨2593476793154545041546901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3457969057539393388729201 2593476793154545041546901)
                      ·
                        rfl

theorem cell23_5050778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_5050778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050778 prefixEnd_5050778 := by exact prefixLift 5050778
  have htrace : WordTrace (prefixWord ++ tailWord_5050778) baseStart_5050778 baseEnd_5050778 := by
    simpa [prefixWord, tailWord_5050778, baseEnd_5050778] using wordTrace_append hprefix tailTrace_5050778
  have hstable : (prefixWord ++ tailWord_5050778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050778).length < 2 ^ (prefixWord ++ tailWord_5050778).sum := by decide
  have hdescent : baseEnd_5050778 < baseStart_5050778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050784 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 7]
def baseStart_5050784 : Nat := 118140960795 + 5050784 * 2 ^ 59
def prefixEnd_5050784 : Nat := 4983230072969 + 3 ^ 40 * 5050784 * 2
def baseEnd_5050784 : Nat := 288164430448719113119097

theorem tailTrace_5050784 : CollatzResearch.WordTrace tailWord_5050784 prefixEnd_5050784 288164430448719113119097 := by
  unfold tailWord_5050784
  simp only [CollatzResearch.WordTrace]
  refine ⟨92108613266939824038399703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122811484355919765384532937 92108613266939824038399703)
  ·
    refine ⟨138162919900409736057599555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92108613266939824038399703 138162919900409736057599555)
    ·
      refine ⟨207244379850614604086399333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138162919900409736057599555 207244379850614604086399333)
      ·
        refine ⟨38858321221990238266199875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207244379850614604086399333 38858321221990238266199875)
        ·
          refine ⟨58287481832985357399299813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38858321221990238266199875 58287481832985357399299813)
          ·
            refine ⟨10928902843684754512368715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58287481832985357399299813 10928902843684754512368715)
            ·
              refine ⟨16393354265527131768553073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10928902843684754512368715 16393354265527131768553073)
              ·
                refine ⟨12295015699145348826414805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16393354265527131768553073 12295015699145348826414805)
                ·
                  refine ⟨288164430448719113119097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12295015699145348826414805 288164430448719113119097)
                  ·
                    rfl

theorem cell23_5050784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 7].length) (baseStart_5050784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050784 prefixEnd_5050784 := by exact prefixLift 5050784
  have htrace : WordTrace (prefixWord ++ tailWord_5050784) baseStart_5050784 baseEnd_5050784 := by
    simpa [prefixWord, tailWord_5050784, baseEnd_5050784] using wordTrace_append hprefix tailTrace_5050784
  have hstable : (prefixWord ++ tailWord_5050784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050784).length < 2 ^ (prefixWord ++ tailWord_5050784).sum := by decide
  have hdescent : baseEnd_5050784 < baseStart_5050784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050801 : List Nat := [1, 2, 2, 4, 1, 2, 1, 5, 5]
def baseStart_5050801 : Nat := 118140960795 + 5050801 * 2 ^ 59
def prefixEnd_5050801 : Nat := 4983230072969 + 3 ^ 40 * 5050801 * 2
def baseEnd_5050801 : Nat := 288165400356622050173255

theorem tailTrace_5050801 : CollatzResearch.WordTrace tailWord_5050801 prefixEnd_5050801 288165400356622050173255 := by
  unfold tailWord_5050801
  simp only [CollatzResearch.WordTrace]
  refine ⟨184217846574818059980168257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122811897716545373320112171 184217846574818059980168257)
  ·
    refine ⟨138163384931113544985126193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184217846574818059980168257 138163384931113544985126193)
    ·
      refine ⟨103622538698335158738844645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138163384931113544985126193 103622538698335158738844645)
      ·
        refine ⟨19429226005937842263533371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103622538698335158738844645 19429226005937842263533371)
        ·
          refine ⟨29143839008906763395300057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19429226005937842263533371 29143839008906763395300057)
          ·
            refine ⟨21857879256680072546475043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29143839008906763395300057 21857879256680072546475043)
            ·
              refine ⟨32786818885020108819712565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21857879256680072546475043 32786818885020108819712565)
              ·
                refine ⟨3073764270470635201848053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32786818885020108819712565 3073764270470635201848053)
                ·
                  refine ⟨288165400356622050173255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3073764270470635201848053 288165400356622050173255)
                  ·
                    rfl

theorem cell23_5050801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 5].length) (baseStart_5050801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050801 prefixEnd_5050801 := by exact prefixLift 5050801
  have htrace : WordTrace (prefixWord ++ tailWord_5050801) baseStart_5050801 baseEnd_5050801 := by
    simpa [prefixWord, tailWord_5050801, baseEnd_5050801] using wordTrace_append hprefix tailTrace_5050801
  have hstable : (prefixWord ++ tailWord_5050801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050801).length < 2 ^ (prefixWord ++ tailWord_5050801).sum := by decide
  have hdescent : baseEnd_5050801 < baseStart_5050801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050812 : List Nat := [2, 2, 2, 4, 1, 3, 1, 2, 2, 2, 2]
def baseStart_5050812 : Nat := 118140960795 + 5050812 * 2 ^ 59
def prefixEnd_5050812 : Nat := 4983230072969 + 3 ^ 40 * 5050812 * 2
def baseEnd_5050812 : Nat := 2593494251496797908521745

theorem tailTrace_5050812 : CollatzResearch.WordTrace tailWord_5050812 prefixEnd_5050812 2593494251496797908521745 := by
  unfold tailWord_5050812
  simp only [CollatzResearch.WordTrace]
  refine ⟨92109123888889104429409345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122812165185185472572545793 92109123888889104429409345)
  ·
    refine ⟨69081842916666828322057009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92109123888889104429409345 69081842916666828322057009)
    ·
      refine ⟨51811382187500121241542757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69081842916666828322057009 51811382187500121241542757)
      ·
        refine ⟨9714634160156272732789267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51811382187500121241542757 9714634160156272732789267)
        ·
          refine ⟨14571951240234409099183901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9714634160156272732789267 14571951240234409099183901)
          ·
            refine ⟨5464481715087903412193963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14571951240234409099183901 5464481715087903412193963)
            ·
              refine ⟨8196722572631855118290945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5464481715087903412193963 8196722572631855118290945)
              ·
                refine ⟨6147541929473891338718209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8196722572631855118290945 6147541929473891338718209)
                ·
                  refine ⟨4610656447105418504038657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6147541929473891338718209 4610656447105418504038657)
                  ·
                    refine ⟨3457992335329063878028993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4610656447105418504038657 3457992335329063878028993)
                    ·
                      refine ⟨2593494251496797908521745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3457992335329063878028993 2593494251496797908521745)
                      ·
                        rfl

theorem cell23_5050812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_5050812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050812 prefixEnd_5050812 := by exact prefixLift 5050812
  have htrace : WordTrace (prefixWord ++ tailWord_5050812) baseStart_5050812 baseEnd_5050812 := by
    simpa [prefixWord, tailWord_5050812, baseEnd_5050812] using wordTrace_append hprefix tailTrace_5050812
  have hstable : (prefixWord ++ tailWord_5050812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050812).length < 2 ^ (prefixWord ++ tailWord_5050812).sum := by decide
  have hdescent : baseEnd_5050812 < baseStart_5050812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050891 : List Nat := [1, 1, 1, 1, 7, 2, 1, 3, 6]
def baseStart_5050891 : Nat := 118140960795 + 5050891 * 2 ^ 59
def prefixEnd_5050891 : Nat := 4983230072969 + 3 ^ 40 * 5050891 * 2
def baseEnd_5050891 : Nat := 288170535163167011048209

theorem tailTrace_5050891 : CollatzResearch.WordTrace tailWord_5050891 prefixEnd_5050891 288170535163167011048209 := by
  unfold tailWord_5050891
  simp only [CollatzResearch.WordTrace]
  refine ⟨184221129144492005350944527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122814086096328003567296351 184221129144492005350944527)
  ·
    refine ⟨276331693716738008026416791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184221129144492005350944527 276331693716738008026416791)
    ·
      refine ⟨414497540575107012039625187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276331693716738008026416791 414497540575107012039625187)
      ·
        refine ⟨621746310862660518059437781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414497540575107012039625187 621746310862660518059437781)
        ·
          refine ⟨14572179160843605892018073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 621746310862660518059437781 14572179160843605892018073)
          ·
            refine ⟨10929134370632704419013555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14572179160843605892018073 10929134370632704419013555)
            ·
              refine ⟨16393701555949056628520333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10929134370632704419013555 16393701555949056628520333)
              ·
                refine ⟨6147638083480896235695125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16393701555949056628520333 6147638083480896235695125)
                ·
                  refine ⟨288170535163167011048209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6147638083480896235695125 288170535163167011048209)
                  ·
                    rfl

theorem cell23_5050891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 6].length) (baseStart_5050891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050891 prefixEnd_5050891 := by exact prefixLift 5050891
  have htrace : WordTrace (prefixWord ++ tailWord_5050891) baseStart_5050891 baseEnd_5050891 := by
    simpa [prefixWord, tailWord_5050891, baseEnd_5050891] using wordTrace_append hprefix tailTrace_5050891
  have hstable : (prefixWord ++ tailWord_5050891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050891).length < 2 ^ (prefixWord ++ tailWord_5050891).sum := by decide
  have hdescent : baseEnd_5050891 < baseStart_5050891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050928 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 2, 3, 2]
def baseStart_5050928 : Nat := 118140960795 + 5050928 * 2 ^ 59
def prefixEnd_5050928 : Nat := 4983230072969 + 3 ^ 40 * 5050928 * 2
def baseEnd_5050928 : Nat := 2593553815252719454671211

theorem tailTrace_5050928 : CollatzResearch.WordTrace tailWord_5050928 prefixEnd_5050928 2593553815252719454671211 := by
  unfold tailWord_5050928
  simp only [CollatzResearch.WordTrace]
  refine ⟨92111239322678980335020719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122814985763571973780027625 92111239322678980335020719)
  ·
    refine ⟨138166858984018470502531079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92111239322678980335020719 138166858984018470502531079)
    ·
      refine ⟨207250288476027705753796619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138166858984018470502531079 207250288476027705753796619)
      ·
        refine ⟨310875432714041558630694929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207250288476027705753796619 310875432714041558630694929)
        ·
          refine ⟨233156574535531168973021197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310875432714041558630694929 233156574535531168973021197)
          ·
            refine ⟨87433715450824188364882949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233156574535531168973021197 87433715450824188364882949)
            ·
              refine ⟨16393821647029535318415553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87433715450824188364882949 16393821647029535318415553)
              ·
                refine ⟨12295366235272151488811665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16393821647029535318415553 12295366235272151488811665)
                ·
                  refine ⟨9221524676454113616608749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12295366235272151488811665 9221524676454113616608749)
                  ·
                    refine ⟨3458071753670292606228281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9221524676454113616608749 3458071753670292606228281)
                    ·
                      refine ⟨2593553815252719454671211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3458071753670292606228281 2593553815252719454671211)
                      ·
                        rfl

theorem cell23_5050928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 2, 3, 2].length) (baseStart_5050928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050928 prefixEnd_5050928 := by exact prefixLift 5050928
  have htrace : WordTrace (prefixWord ++ tailWord_5050928) baseStart_5050928 baseEnd_5050928 := by
    simpa [prefixWord, tailWord_5050928, baseEnd_5050928] using wordTrace_append hprefix tailTrace_5050928
  have hstable : (prefixWord ++ tailWord_5050928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050928).length < 2 ^ (prefixWord ++ tailWord_5050928).sum := by decide
  have hdescent : baseEnd_5050928 < baseStart_5050928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050935 : List Nat := [1, 1, 3, 1, 2, 3, 3, 4, 1, 1, 3]
def baseStart_5050935 : Nat := 118140960795 + 5050935 * 2 ^ 59
def prefixEnd_5050935 : Nat := 4983230072969 + 3 ^ 40 * 5050935 * 2
def baseEnd_5050935 : Nat := 2593557409617300927283679

theorem tailTrace_5050935 : CollatzResearch.WordTrace tailWord_5050935 prefixEnd_5050935 2593557409617300927283679 := by
  unfold tailWord_5050935
  simp only [CollatzResearch.WordTrace]
  refine ⟨184222733956332600865546259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122815155970888400577030839 184222733956332600865546259)
  ·
    refine ⟨276334100934498901298319389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184222733956332600865546259 276334100934498901298319389)
    ·
      refine ⟨103625287850437087986869771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276334100934498901298319389 103625287850437087986869771)
      ·
        refine ⟨155437931775655631980304657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103625287850437087986869771 155437931775655631980304657)
        ·
          refine ⟨116578448831741723985228493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155437931775655631980304657 116578448831741723985228493)
          ·
            refine ⟨43716918311903146494460685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116578448831741723985228493 43716918311903146494460685)
            ·
              refine ⟨16393844366963679935422757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43716918311903146494460685 16393844366963679935422757)
              ·
                refine ⟨3073845818805689987891767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16393844366963679935422757 3073845818805689987891767)
                ·
                  refine ⟨4610768728208534981837651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073845818805689987891767 4610768728208534981837651)
                  ·
                    refine ⟨6916153092312802472756477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4610768728208534981837651 6916153092312802472756477)
                    ·
                      refine ⟨2593557409617300927283679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6916153092312802472756477 2593557409617300927283679)
                      ·
                        rfl

theorem cell23_5050935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 1, 1, 3].length) (baseStart_5050935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050935 prefixEnd_5050935 := by exact prefixLift 5050935
  have htrace : WordTrace (prefixWord ++ tailWord_5050935) baseStart_5050935 baseEnd_5050935 := by
    simpa [prefixWord, tailWord_5050935, baseEnd_5050935] using wordTrace_append hprefix tailTrace_5050935
  have hstable : (prefixWord ++ tailWord_5050935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050935).length < 2 ^ (prefixWord ++ tailWord_5050935).sum := by decide
  have hdescent : baseEnd_5050935 < baseStart_5050935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050951 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 1, 6]
def baseStart_5050951 : Nat := 118140960795 + 5050951 * 2 ^ 59
def prefixEnd_5050951 : Nat := 4983230072969 + 3 ^ 40 * 5050951 * 2
def baseEnd_5050951 : Nat := 864521875102590954894535

theorem tailTrace_5050951 : CollatzResearch.WordTrace tailWord_5050951 prefixEnd_5050951 864521875102590954894535 := by
  unfold tailWord_5050951
  simp only [CollatzResearch.WordTrace]
  refine ⟨184223317524274635598128707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122815545016183090398752471 184223317524274635598128707)
  ·
    refine ⟨276334976286411953397193061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184223317524274635598128707 276334976286411953397193061)
    ·
      refine ⟨51812808053702241261973699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276334976286411953397193061 51812808053702241261973699)
      ·
        refine ⟨77719212080553361892960549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51812808053702241261973699 77719212080553361892960549)
        ·
          refine ⟨14572352265103755354930103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77719212080553361892960549 14572352265103755354930103)
          ·
            refine ⟨21858528397655633032395155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14572352265103755354930103 21858528397655633032395155)
            ·
              refine ⟨32787792596483449548592733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21858528397655633032395155 32787792596483449548592733)
              ·
                refine ⟨12295422223681293580722275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32787792596483449548592733 12295422223681293580722275)
                ·
                  refine ⟨18443133335521940371083413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12295422223681293580722275 18443133335521940371083413)
                  ·
                    refine ⟨864521875102590954894535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18443133335521940371083413 864521875102590954894535)
                    ·
                      rfl

theorem cell23_5050951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_5050951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050951 prefixEnd_5050951 := by exact prefixLift 5050951
  have htrace : WordTrace (prefixWord ++ tailWord_5050951) baseStart_5050951 baseEnd_5050951 := by
    simpa [prefixWord, tailWord_5050951, baseEnd_5050951] using wordTrace_append hprefix tailTrace_5050951
  have hstable : (prefixWord ++ tailWord_5050951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050951).length < 2 ^ (prefixWord ++ tailWord_5050951).sum := by decide
  have hdescent : baseEnd_5050951 < baseStart_5050951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050972 : List Nat := [2, 2, 4, 1, 3, 2, 2, 1, 1, 5]
def baseStart_5050972 : Nat := 118140960795 + 5050972 * 2 ^ 59
def prefixEnd_5050972 : Nat := 4983230072969 + 3 ^ 40 * 5050972 * 2
def baseEnd_5050972 : Nat := 864525469467172427507003

theorem tailTrace_5050972 : CollatzResearch.WordTrace tailWord_5050972 prefixEnd_5050972 864525469467172427507003 := by
  unfold tailWord_5050972
  simp only [CollatzResearch.WordTrace]
  refine ⟨92112041728599278092321585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122816055638132370789762113 92112041728599278092321585)
  ·
    refine ⟨69084031296449458569241189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92112041728599278092321585 69084031296449458569241189)
    ·
      refine ⟨12953255868084273481732723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69084031296449458569241189 12953255868084273481732723)
      ·
        refine ⟨19429883802126410222599085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12953255868084273481732723 19429883802126410222599085)
        ·
          refine ⟨7286206425797403833474657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19429883802126410222599085 7286206425797403833474657)
          ·
            refine ⟨5464654819348052875105993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7286206425797403833474657 5464654819348052875105993)
            ·
              refine ⟨4098491114511039656329495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5464654819348052875105993 4098491114511039656329495)
              ·
                refine ⟨6147736671766559484494243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4098491114511039656329495 6147736671766559484494243)
                ·
                  refine ⟨9221605007649839226741365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6147736671766559484494243 9221605007649839226741365)
                  ·
                    refine ⟨864525469467172427507003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9221605007649839226741365 864525469467172427507003)
                    ·
                      rfl

theorem cell23_5050972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_5050972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050972 prefixEnd_5050972 := by exact prefixLift 5050972
  have htrace : WordTrace (prefixWord ++ tailWord_5050972) baseStart_5050972 baseEnd_5050972 := by
    simpa [prefixWord, tailWord_5050972, baseEnd_5050972] using wordTrace_append hprefix tailTrace_5050972
  have hstable : (prefixWord ++ tailWord_5050972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050972).length < 2 ^ (prefixWord ++ tailWord_5050972).sum := by decide
  have hdescent : baseEnd_5050972 < baseStart_5050972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050981 : List Nat := [1, 3, 1, 3, 4, 1, 10]
def baseStart_5050981 : Nat := 118140960795 + 5050981 * 2 ^ 59
def prefixEnd_5050981 : Nat := 4983230072969 + 3 ^ 40 * 5050981 * 2
def baseEnd_5050981 : Nat := 32019518885523552435907

theorem tailTrace_5050981 : CollatzResearch.WordTrace tailWord_5050981 prefixEnd_5050981 32019518885523552435907 := by
  unfold tailWord_5050981
  simp only [CollatzResearch.WordTrace]
  refine ⟨184224411714165950721720797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122816274476110633814480531 184224411714165950721720797)
  ·
    refine ⟨69084154392812231520645299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184224411714165950721720797 69084154392812231520645299)
    ·
      refine ⟨103626231589218347280967949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69084154392812231520645299 103626231589218347280967949)
      ·
        refine ⟨38859836845956880230362981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103626231589218347280967949 38859836845956880230362981)
        ·
          refine ⟨7286219408616915043193059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38859836845956880230362981 7286219408616915043193059)
          ·
            refine ⟨10929329112925372564789589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7286219408616915043193059 10929329112925372564789589)
            ·
              refine ⟨32019518885523552435907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10929329112925372564789589 32019518885523552435907)
              ·
                rfl

theorem cell23_5050981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 10].length) (baseStart_5050981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050981 prefixEnd_5050981 := by exact prefixLift 5050981
  have htrace : WordTrace (prefixWord ++ tailWord_5050981) baseStart_5050981 baseEnd_5050981 := by
    simpa [prefixWord, tailWord_5050981, baseEnd_5050981] using wordTrace_append hprefix tailTrace_5050981
  have hstable : (prefixWord ++ tailWord_5050981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050981).length < 2 ^ (prefixWord ++ tailWord_5050981).sum := by decide
  have hdescent : baseEnd_5050981 < baseStart_5050981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050991 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 3]
def baseStart_5050991 : Nat := 118140960795 + 5050991 * 2 ^ 59
def prefixEnd_5050991 : Nat := 4983230072969 + 3 ^ 40 * 5050991 * 2
def baseEnd_5050991 : Nat := 2593586164533952708183421

theorem tailTrace_5050991 : CollatzResearch.WordTrace tailWord_5050991 prefixEnd_5050991 2593586164533952708183421 := by
  unfold tailWord_5050991
  simp only [CollatzResearch.WordTrace]
  refine ⟨184224776444129722429584827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122816517629419814953056551 184224776444129722429584827)
  ·
    refine ⟨276337164666194583644377241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184224776444129722429584827 276337164666194583644377241)
    ·
      refine ⟨207252873499645937733282931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276337164666194583644377241 207252873499645937733282931)
      ·
        refine ⟨310879310249468906599924397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207252873499645937733282931 310879310249468906599924397)
        ·
          refine ⟨116579741343550839974971649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310879310249468906599924397 116579741343550839974971649)
          ·
            refine ⟨87434806007663129981228737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116579741343550839974971649 87434806007663129981228737)
            ·
              refine ⟨65576104505747347485921553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87434806007663129981228737 65576104505747347485921553)
              ·
                refine ⟨49182078379310510614441165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65576104505747347485921553 49182078379310510614441165)
                ·
                  refine ⟨18443279392241441480415437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49182078379310510614441165 18443279392241441480415437)
                  ·
                    refine ⟨6916229772090540555155789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18443279392241441480415437 6916229772090540555155789)
                    ·
                      refine ⟨2593586164533952708183421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6916229772090540555155789 2593586164533952708183421)
                      ·
                        rfl

theorem cell23_5050991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 3].length) (baseStart_5050991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050991 prefixEnd_5050991 := by exact prefixLift 5050991
  have htrace : WordTrace (prefixWord ++ tailWord_5050991) baseStart_5050991 baseEnd_5050991 := by
    simpa [prefixWord, tailWord_5050991, baseEnd_5050991] using wordTrace_append hprefix tailTrace_5050991
  have hstable : (prefixWord ++ tailWord_5050991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050991).length < 2 ^ (prefixWord ++ tailWord_5050991).sum := by decide
  have hdescent : baseEnd_5050991 < baseStart_5050991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5050992 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 3, 2, 2]
def baseStart_5050992 : Nat := 118140960795 + 5050992 * 2 ^ 59
def prefixEnd_5050992 : Nat := 4983230072969 + 3 ^ 40 * 5050992 * 2
def baseEnd_5050992 : Nat := 2593586678014607204270917

theorem tailTrace_5050992 : CollatzResearch.WordTrace tailWord_5050992 prefixEnd_5050992 2593586678014607204270917 := by
  unfold tailWord_5050992
  simp only [CollatzResearch.WordTrace]
  refine ⟨92112406458563049800185615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122816541944750733066914153 92112406458563049800185615)
  ·
    refine ⟨138168609687844574700278423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92112406458563049800185615 138168609687844574700278423)
    ·
      refine ⟨207252914531766862050417635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138168609687844574700278423 207252914531766862050417635)
      ·
        refine ⟨310879371797650293075626453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207252914531766862050417635 310879371797650293075626453)
        ·
          refine ⟨7286235276507428743959995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 310879371797650293075626453 7286235276507428743959995)
          ·
            refine ⟨10929352914761143115939993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7286235276507428743959995 10929352914761143115939993)
            ·
              refine ⟨8197014686070857336954995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10929352914761143115939993 8197014686070857336954995)
              ·
                refine ⟨12295522029106286005432493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8197014686070857336954995 12295522029106286005432493)
                ·
                  refine ⟨4610820760914857252037185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12295522029106286005432493 4610820760914857252037185)
                  ·
                    refine ⟨3458115570686142939027889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4610820760914857252037185 3458115570686142939027889)
                    ·
                      refine ⟨2593586678014607204270917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3458115570686142939027889 2593586678014607204270917)
                      ·
                        rfl

theorem cell23_5050992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 3, 2, 2].length) (baseStart_5050992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5050992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5050992 prefixEnd_5050992 := by exact prefixLift 5050992
  have htrace : WordTrace (prefixWord ++ tailWord_5050992) baseStart_5050992 baseEnd_5050992 := by
    simpa [prefixWord, tailWord_5050992, baseEnd_5050992] using wordTrace_append hprefix tailTrace_5050992
  have hstable : (prefixWord ++ tailWord_5050992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5050992).length < 2 ^ (prefixWord ++ tailWord_5050992).sum := by decide
  have hdescent : baseEnd_5050992 < baseStart_5050992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5050992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051005 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 1, 2, 4]
def baseStart_5051005 : Nat := 118140960795 + 5051005 * 2 ^ 59
def prefixEnd_5051005 : Nat := 4983230072969 + 3 ^ 40 * 5051005 * 2
def baseEnd_5051005 : Nat := 2593593353263115653408357

theorem tailTrace_5051005 : CollatzResearch.WordTrace tailWord_5051005 prefixEnd_5051005 2593593353263115653408357 := by
  unfold tailWord_5051005
  simp only [CollatzResearch.WordTrace]
  refine ⟨184225287066079002820594469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122816858044052668547062979 184225287066079002820594469)
  ·
    refine ⟨34542241324889813028861463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184225287066079002820594469 34542241324889813028861463)
    ·
      refine ⟨51813361987334719543292195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34542241324889813028861463 51813361987334719543292195)
      ·
        refine ⟨77720042981002079314938293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51813361987334719543292195 77720042981002079314938293)
        ·
          refine ⟨7286254029468944935775465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77720042981002079314938293 7286254029468944935775465)
          ·
            refine ⟨5464690522101708701831599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7286254029468944935775465 5464690522101708701831599)
            ·
              refine ⟨8197035783152563052747399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5464690522101708701831599 8197035783152563052747399)
              ·
                refine ⟨12295553674728844579121099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8197035783152563052747399 12295553674728844579121099)
                ·
                  refine ⟨18443330512093266868681649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12295553674728844579121099 18443330512093266868681649)
                  ·
                    refine ⟨13832497884069950151511237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18443330512093266868681649 13832497884069950151511237)
                    ·
                      refine ⟨2593593353263115653408357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13832497884069950151511237 2593593353263115653408357)
                      ·
                        rfl

theorem cell23_5051005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_5051005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051005 prefixEnd_5051005 := by exact prefixLift 5051005
  have htrace : WordTrace (prefixWord ++ tailWord_5051005) baseStart_5051005 baseEnd_5051005 := by
    simpa [prefixWord, tailWord_5051005, baseEnd_5051005] using wordTrace_append hprefix tailTrace_5051005
  have hstable : (prefixWord ++ tailWord_5051005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051005).length < 2 ^ (prefixWord ++ tailWord_5051005).sum := by decide
  have hdescent : baseEnd_5051005 < baseStart_5051005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051008 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 3]
def baseStart_5051008 : Nat := 118140960795 + 5051008 * 2 ^ 59
def prefixEnd_5051008 : Nat := 4983230072969 + 3 ^ 40 * 5051008 * 2
def baseEnd_5051008 : Nat := 2593594893705079141670843

theorem tailTrace_5051008 : CollatzResearch.WordTrace tailWord_5051008 prefixEnd_5051008 2593594893705079141670843 := by
  unfold tailWord_5051008
  simp only [CollatzResearch.WordTrace]
  refine ⟨92112698242534067166476839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122816930990045422888635785 92112698242534067166476839)
  ·
    refine ⟨138169047363801100749715259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92112698242534067166476839 138169047363801100749715259)
    ·
      refine ⟨207253571045701651124572889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138169047363801100749715259 207253571045701651124572889)
      ·
        refine ⟨155440178284276238343429667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207253571045701651124572889 155440178284276238343429667)
        ·
          refine ⟨233160267426414357515144501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155440178284276238343429667 233160267426414357515144501)
          ·
            refine ⟨21858775071226346017044797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 233160267426414357515144501 21858775071226346017044797)
            ·
              refine ⟨8197040651709879756391799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21858775071226346017044797 8197040651709879756391799)
              ·
                refine ⟨12295560977564819634587699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8197040651709879756391799 12295560977564819634587699)
                ·
                  refine ⟨18443341466347229451881549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12295560977564819634587699 18443341466347229451881549)
                  ·
                    refine ⟨6916253049880211044455581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18443341466347229451881549 6916253049880211044455581)
                    ·
                      refine ⟨2593594893705079141670843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6916253049880211044455581 2593594893705079141670843)
                      ·
                        rfl

theorem cell23_5051008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_5051008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051008 prefixEnd_5051008 := by exact prefixLift 5051008
  have htrace : WordTrace (prefixWord ++ tailWord_5051008) baseStart_5051008 baseEnd_5051008 := by
    simpa [prefixWord, tailWord_5051008, baseEnd_5051008] using wordTrace_append hprefix tailTrace_5051008
  have hstable : (prefixWord ++ tailWord_5051008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051008).length < 2 ^ (prefixWord ++ tailWord_5051008).sum := by decide
  have hdescent : baseEnd_5051008 < baseStart_5051008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051026 : List Nat := [3, 2, 3, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_5051026 : Nat := 118140960795 + 5051026 * 2 ^ 59
def prefixEnd_5051026 : Nat := 4983230072969 + 3 ^ 40 * 5051026 * 2
def baseEnd_5051026 : Nat := 2593604136356860071245761

theorem tailTrace_5051026 : CollatzResearch.WordTrace tailWord_5051026 prefixEnd_5051026 2593604136356860071245761 := by
  unfold tailWord_5051026
  simp only [CollatzResearch.WordTrace]
  refine ⟨46056513249750730851777233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122817368666001948938072621 46056513249750730851777233)
  ·
    refine ⟨34542384937313048138832925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46056513249750730851777233 34542384937313048138832925)
    ·
      refine ⟨12953394351492393052062347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34542384937313048138832925 12953394351492393052062347)
      ·
        refine ⟨19430091527238589578093521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12953394351492393052062347 19430091527238589578093521)
        ·
          refine ⟨14572568645428942183570141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19430091527238589578093521 14572568645428942183570141)
          ·
            refine ⟨5464713242035853318838803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14572568645428942183570141 5464713242035853318838803)
            ·
              refine ⟨8197069863053779978258205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5464713242035853318838803 8197069863053779978258205)
              ·
                refine ⟨3073901198645167491846827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8197069863053779978258205 3073901198645167491846827)
                ·
                  refine ⟨4610851797967751237770241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073901198645167491846827 4610851797967751237770241)
                  ·
                    refine ⟨3458138848475813428327681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4610851797967751237770241 3458138848475813428327681)
                    ·
                      refine ⟨2593604136356860071245761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3458138848475813428327681 2593604136356860071245761)
                      ·
                        rfl

theorem cell23_5051026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_5051026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051026 prefixEnd_5051026 := by exact prefixLift 5051026
  have htrace : WordTrace (prefixWord ++ tailWord_5051026) baseStart_5051026 baseEnd_5051026 := by
    simpa [prefixWord, tailWord_5051026, baseEnd_5051026] using wordTrace_append hprefix tailTrace_5051026
  have hstable : (prefixWord ++ tailWord_5051026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051026).length < 2 ^ (prefixWord ++ tailWord_5051026).sum := by decide
  have hdescent : baseEnd_5051026 < baseStart_5051026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051038 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_5051038 : Nat := 118140960795 + 5051038 * 2 ^ 59
def prefixEnd_5051038 : Nat := 4983230072969 + 3 ^ 40 * 5051038 * 2
def baseEnd_5051038 : Nat := 2593610298124714024295705

theorem tailTrace_5051038 : CollatzResearch.WordTrace tailWord_5051038 prefixEnd_5051038 2593610298124714024295705 := by
  unfold tailWord_5051038
  simp only [CollatzResearch.WordTrace]
  refine ⟨23028311334369931182068221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122817660449972966304363845 23028311334369931182068221)
  ·
    refine ⟨8635616750388724193275583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23028311334369931182068221 8635616750388724193275583)
    ·
      refine ⟨12953425125583086289913375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8635616750388724193275583 12953425125583086289913375)
      ·
        refine ⟨19430137688374629434870063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12953425125583086289913375 19430137688374629434870063)
        ·
          refine ⟨29145206532561944152305095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19430137688374629434870063 29145206532561944152305095)
          ·
            refine ⟨43717809798842916228457643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29145206532561944152305095 43717809798842916228457643)
            ·
              refine ⟨65576714698264374342686465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43717809798842916228457643 65576714698264374342686465)
              ·
                refine ⟨49182536023698280757014849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65576714698264374342686465 49182536023698280757014849)
                ·
                  refine ⟨36886902017773710567761137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49182536023698280757014849 36886902017773710567761137)
                  ·
                    refine ⟨27665176513330282925820853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36886902017773710567761137 27665176513330282925820853)
                    ·
                      refine ⟨2593610298124714024295705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27665176513330282925820853 2593610298124714024295705)
                      ·
                        rfl

theorem cell23_5051038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_5051038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051038 prefixEnd_5051038 := by exact prefixLift 5051038
  have htrace : WordTrace (prefixWord ++ tailWord_5051038) baseStart_5051038 baseEnd_5051038 := by
    simpa [prefixWord, tailWord_5051038, baseEnd_5051038] using wordTrace_append hprefix tailTrace_5051038
  have hstable : (prefixWord ++ tailWord_5051038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051038).length < 2 ^ (prefixWord ++ tailWord_5051038).sum := by decide
  have hdescent : baseEnd_5051038 < baseStart_5051038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051098 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3]
def baseStart_5051098 : Nat := 118140960795 + 5051098 * 2 ^ 59
def prefixEnd_5051098 : Nat := 4983230072969 + 3 ^ 40 * 5051098 * 2
def baseEnd_5051098 : Nat := 2593641106963983789545429

theorem tailTrace_5051098 : CollatzResearch.WordTrace tailWord_5051098 prefixEnd_5051098 2593641106963983789545429 := by
  unfold tailWord_5051098
  simp only [CollatzResearch.WordTrace]
  refine ⟨46057169763685519925932487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122819119369828053135819965 46057169763685519925932487)
  ·
    refine ⟨69085754645528279888898731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46057169763685519925932487 69085754645528279888898731)
    ·
      refine ⟨103628631968292419833348097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69085754645528279888898731 103628631968292419833348097)
      ·
        refine ⟨77721473976219314875011073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103628631968292419833348097 77721473976219314875011073)
        ·
          refine ⟨58291105482164486156258305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77721473976219314875011073 58291105482164486156258305)
          ·
            refine ⟨43718329111623364617193729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58291105482164486156258305 43718329111623364617193729)
            ·
              refine ⟨32788746833717523462895297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43718329111623364617193729 32788746833717523462895297)
              ·
                refine ⟨24591560125288142597171473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32788746833717523462895297 24591560125288142597171473)
                ·
                  refine ⟨18443670093966106947878605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24591560125288142597171473 18443670093966106947878605)
                  ·
                    refine ⟨6916376285237290105454477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18443670093966106947878605 6916376285237290105454477)
                    ·
                      refine ⟨2593641106963983789545429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6916376285237290105454477 2593641106963983789545429)
                      ·
                        rfl

theorem cell23_5051098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_5051098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051098 prefixEnd_5051098 := by exact prefixLift 5051098
  have htrace : WordTrace (prefixWord ++ tailWord_5051098) baseStart_5051098 baseEnd_5051098 := by
    simpa [prefixWord, tailWord_5051098, baseEnd_5051098] using wordTrace_append hprefix tailTrace_5051098
  have hstable : (prefixWord ++ tailWord_5051098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051098).length < 2 ^ (prefixWord ++ tailWord_5051098).sum := by decide
  have hdescent : baseEnd_5051098 < baseStart_5051098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051105 : List Nat := [1, 2, 3, 1, 4, 2, 1, 4, 5]
def baseStart_5051105 : Nat := 118140960795 + 5051105 * 2 ^ 59
def prefixEnd_5051105 : Nat := 4983230072969 + 3 ^ 40 * 5051105 * 2
def baseEnd_5051105 : Nat := 288182744592062806906433

theorem tailTrace_5051105 : CollatzResearch.WordTrace tailWord_5051105 prefixEnd_5051105 288182744592062806906433 := by
  unfold tailWord_5051105
  simp only [CollatzResearch.WordTrace]
  refine ⟨184228934365716719899234769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122819289577144479932823179 184228934365716719899234769)
  ·
    refine ⟨138171700774287539924426077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184228934365716719899234769 138171700774287539924426077)
    ·
      refine ⟨51814387790357827471659779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138171700774287539924426077 51814387790357827471659779)
      ·
        refine ⟨77721581685536741207489669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51814387790357827471659779 77721581685536741207489669)
        ·
          refine ⟨14572796566038138976404313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77721581685536741207489669 14572796566038138976404313)
          ·
            refine ⟨10929597424528604232303235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14572796566038138976404313 10929597424528604232303235)
            ·
              refine ⟨16394396136792906348454853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10929597424528604232303235 16394396136792906348454853)
              ·
                refine ⟨3073949275648669940335285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16394396136792906348454853 3073949275648669940335285)
                ·
                  refine ⟨288182744592062806906433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3073949275648669940335285 288182744592062806906433)
                  ·
                    rfl

theorem cell23_5051105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 5].length) (baseStart_5051105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051105 prefixEnd_5051105 := by exact prefixLift 5051105
  have htrace : WordTrace (prefixWord ++ tailWord_5051105) baseStart_5051105 baseEnd_5051105 := by
    simpa [prefixWord, tailWord_5051105, baseEnd_5051105] using wordTrace_append hprefix tailTrace_5051105
  have hstable : (prefixWord ++ tailWord_5051105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051105).length < 2 ^ (prefixWord ++ tailWord_5051105).sum := by decide
  have hdescent : baseEnd_5051105 < baseStart_5051105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051148 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 7, 4]
def baseStart_5051148 : Nat := 118140960795 + 5051148 * 2 ^ 59
def prefixEnd_5051148 : Nat := 4983230072969 + 3 ^ 40 * 5051148 * 2
def baseEnd_5051148 : Nat := 864555593665569531306733

theorem tailTrace_5051148 : CollatzResearch.WordTrace tailWord_5051148 prefixEnd_5051148 864555593665569531306733 := by
  unfold tailWord_5051148
  simp only [CollatzResearch.WordTrace]
  refine ⟨92115251352280469121525049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122820335136373958828700065 92115251352280469121525049)
  ·
    refine ⟨69086438514210351841143787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92115251352280469121525049 69086438514210351841143787)
    ·
      refine ⟨103629657771315527761715681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69086438514210351841143787 103629657771315527761715681)
      ·
        refine ⟨77722243328486645821286761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103629657771315527761715681 77722243328486645821286761)
        ·
          refine ⟨58291682496364984365965071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77722243328486645821286761 58291682496364984365965071)
          ·
            refine ⟨87437523744547476548947607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58291682496364984365965071 87437523744547476548947607)
            ·
              refine ⟨131156285616821214823421411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87437523744547476548947607 131156285616821214823421411)
              ·
                refine ⟨196734428425231822235132117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131156285616821214823421411 196734428425231822235132117)
                ·
                  refine ⟨4610963166216370833635909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 196734428425231822235132117 4610963166216370833635909)
                  ·
                    refine ⟨864555593665569531306733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4610963166216370833635909 864555593665569531306733)
                    ·
                      rfl

theorem cell23_5051148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_5051148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051148 prefixEnd_5051148 := by exact prefixLift 5051148
  have htrace : WordTrace (prefixWord ++ tailWord_5051148) baseStart_5051148 baseEnd_5051148 := by
    simpa [prefixWord, tailWord_5051148, baseEnd_5051148] using wordTrace_append hprefix tailTrace_5051148
  have hstable : (prefixWord ++ tailWord_5051148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051148).length < 2 ^ (prefixWord ++ tailWord_5051148).sum := by decide
  have hdescent : baseEnd_5051148 < baseStart_5051148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051151 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 6]
def baseStart_5051151 : Nat := 118140960795 + 5051151 * 2 ^ 59
def prefixEnd_5051151 : Nat := 4983230072969 + 3 ^ 40 * 5051151 * 2
def baseEnd_5051151 : Nat := 2593668321438672082182685

theorem tailTrace_5051151 : CollatzResearch.WordTrace tailWord_5051151 prefixEnd_5051151 2593668321438672082182685 := by
  unfold tailWord_5051151
  simp only [CollatzResearch.WordTrace]
  refine ⟨184230612123550069755409307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122820408082366713170272871 184230612123550069755409307)
  ·
    refine ⟨276345918185325104633113961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184230612123550069755409307 276345918185325104633113961)
    ·
      refine ⟨207259438638993828474835471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276345918185325104633113961 207259438638993828474835471)
      ·
        refine ⟨310889157958490742712253207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207259438638993828474835471 310889157958490742712253207)
        ·
          refine ⟨466333736937736114068379811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310889157958490742712253207 466333736937736114068379811)
          ·
            refine ⟨699500605406604171102569717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466333736937736114068379811 699500605406604171102569717)
            ·
              refine ⟨65578181756869141040865911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 699500605406604171102569717 65578181756869141040865911)
              ·
                refine ⟨98367272635303711561298867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65578181756869141040865911 98367272635303711561298867)
                ·
                  refine ⟨147550908952955567341948301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98367272635303711561298867 147550908952955567341948301)
                  ·
                    refine ⟨55331590857358337753230613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 147550908952955567341948301 55331590857358337753230613)
                    ·
                      refine ⟨2593668321438672082182685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55331590857358337753230613 2593668321438672082182685)
                      ·
                        rfl

theorem cell23_5051151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_5051151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051151 prefixEnd_5051151 := by exact prefixLift 5051151
  have htrace : WordTrace (prefixWord ++ tailWord_5051151) baseStart_5051151 baseEnd_5051151 := by
    simpa [prefixWord, tailWord_5051151, baseEnd_5051151] using wordTrace_append hprefix tailTrace_5051151
  have hstable : (prefixWord ++ tailWord_5051151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051151).length < 2 ^ (prefixWord ++ tailWord_5051151).sum := by decide
  have hdescent : baseEnd_5051151 < baseStart_5051151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051182 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 3, 4]
def baseStart_5051182 : Nat := 118140960795 + 5051182 * 2 ^ 59
def prefixEnd_5051182 : Nat := 4983230072969 + 3 ^ 40 * 5051182 * 2
def baseEnd_5051182 : Nat := 864561413112987153631681

theorem tailTrace_5051182 : CollatzResearch.WordTrace tailWord_5051182 prefixEnd_5051182 864561413112987153631681 := by
  unfold tailWord_5051182
  simp only [CollatzResearch.WordTrace]
  refine ⟨23028967848304720256223475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122821161857625174699858533 23028967848304720256223475)
  ·
    refine ⟨34543451772457080384335213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23028967848304720256223475 34543451772457080384335213)
    ·
      refine ⟨12953794414671405144125705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34543451772457080384335213 12953794414671405144125705)
      ·
        refine ⟨9715345811003553858094279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12953794414671405144125705 9715345811003553858094279)
        ·
          refine ⟨14573018716505330787141419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9715345811003553858094279 14573018716505330787141419)
          ·
            refine ⟨21859528074757996180712129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14573018716505330787141419 21859528074757996180712129)
            ·
              refine ⟨16394646056068497135534097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21859528074757996180712129 16394646056068497135534097)
              ·
                refine ⟨12295984542051372851650573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16394646056068497135534097 12295984542051372851650573)
                ·
                  refine ⟨4610994203269264819368965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12295984542051372851650573 4610994203269264819368965)
                  ·
                    refine ⟨864561413112987153631681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4610994203269264819368965 864561413112987153631681)
                    ·
                      rfl

theorem cell23_5051182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_5051182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051182 prefixEnd_5051182 := by exact prefixLift 5051182
  have htrace : WordTrace (prefixWord ++ tailWord_5051182) baseStart_5051182 baseEnd_5051182 := by
    simpa [prefixWord, tailWord_5051182, baseEnd_5051182] using wordTrace_append hprefix tailTrace_5051182
  have hstable : (prefixWord ++ tailWord_5051182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051182).length < 2 ^ (prefixWord ++ tailWord_5051182).sum := by decide
  have hdescent : baseEnd_5051182 < baseStart_5051182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051199 : List Nat := [1, 1, 2, 2, 5, 3, 1, 3, 1, 4]
def baseStart_5051199 : Nat := 118140960795 + 5051199 * 2 ^ 59
def prefixEnd_5051199 : Nat := 4983230072969 + 3 ^ 40 * 5051199 * 2
def baseEnd_5051199 : Nat := 864564322836695964794155

theorem tailTrace_5051199 : CollatzResearch.WordTrace tailWord_5051199 prefixEnd_5051199 864564322836695964794155 := by
  unfold tailWord_5051199
  simp only [CollatzResearch.WordTrace]
  refine ⟨184232362827376173953156651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122821575218250782635437767 184232362827376173953156651)
  ·
    refine ⟨276348544241064260929734977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184232362827376173953156651 276348544241064260929734977)
    ·
      refine ⟨207261408180798195697301233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276348544241064260929734977 207261408180798195697301233)
      ·
        refine ⟨155446056135598646772975925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207261408180798195697301233 155446056135598646772975925)
        ·
          refine ⟨14573067762712373134966493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155446056135598646772975925 14573067762712373134966493)
          ·
            refine ⟨5464900411017139925612435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14573067762712373134966493 5464900411017139925612435)
            ·
              refine ⟨8197350616525709888418653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5464900411017139925612435 8197350616525709888418653)
              ·
                refine ⟨3074006481197141208156995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8197350616525709888418653 3074006481197141208156995)
                ·
                  refine ⟨4611009721795711812235493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3074006481197141208156995 4611009721795711812235493)
                  ·
                    refine ⟨864564322836695964794155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4611009721795711812235493 864564322836695964794155)
                    ·
                      rfl

theorem cell23_5051199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 1, 4].length) (baseStart_5051199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051199 prefixEnd_5051199 := by exact prefixLift 5051199
  have htrace : WordTrace (prefixWord ++ tailWord_5051199) baseStart_5051199 baseEnd_5051199 := by
    simpa [prefixWord, tailWord_5051199, baseEnd_5051199] using wordTrace_append hprefix tailTrace_5051199
  have hstable : (prefixWord ++ tailWord_5051199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051199).length < 2 ^ (prefixWord ++ tailWord_5051199).sum := by decide
  have hdescent : baseEnd_5051199 < baseStart_5051199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051248 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 5]
def baseStart_5051248 : Nat := 118140960795 + 5051248 * 2 ^ 59
def prefixEnd_5051248 : Nat := 4983230072969 + 3 ^ 40 * 5051248 * 2
def baseEnd_5051248 : Nat := 2593718129062158202669739

theorem tailTrace_5051248 : CollatzResearch.WordTrace tailWord_5051248 prefixEnd_5051248 2593718129062158202669739 := by
  unfold tailWord_5051248
  simp only [CollatzResearch.WordTrace]
  refine ⟨92117075002099327660845199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122822766669465770214460265 92117075002099327660845199)
  ·
    refine ⟨138175612503148991491267799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92117075002099327660845199 138175612503148991491267799)
    ·
      refine ⟨207263418754723487236901699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138175612503148991491267799 207263418754723487236901699)
      ·
        refine ⟨310895128132085230855352549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207263418754723487236901699 310895128132085230855352549)
        ·
          refine ⟨58292836524765980785378603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 310895128132085230855352549 58292836524765980785378603)
          ·
            refine ⟨87439254787148971178067905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58292836524765980785378603 87439254787148971178067905)
            ·
              refine ⟨65579441090361728383550929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87439254787148971178067905 65579441090361728383550929)
              ·
                refine ⟨49184580817771296287663197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65579441090361728383550929 49184580817771296287663197)
                ·
                  refine ⟨18444217806664236107873699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49184580817771296287663197 18444217806664236107873699)
                  ·
                    refine ⟨27666326709996354161810549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18444217806664236107873699 27666326709996354161810549)
                    ·
                      refine ⟨2593718129062158202669739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27666326709996354161810549 2593718129062158202669739)
                      ·
                        rfl

theorem cell23_5051248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_5051248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051248 prefixEnd_5051248 := by exact prefixLift 5051248
  have htrace : WordTrace (prefixWord ++ tailWord_5051248) baseStart_5051248 baseEnd_5051248 := by
    simpa [prefixWord, tailWord_5051248, baseEnd_5051248] using wordTrace_append hprefix tailTrace_5051248
  have hstable : (prefixWord ++ tailWord_5051248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051248).length < 2 ^ (prefixWord ++ tailWord_5051248).sum := by decide
  have hdescent : baseEnd_5051248 < baseStart_5051248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051272 : List Nat := [2, 1, 3, 3, 2, 1, 1, 4, 2, 4]
def baseStart_5051272 : Nat := 118140960795 + 5051272 * 2 ^ 59
def prefixEnd_5051272 : Nat := 4983230072969 + 3 ^ 40 * 5051272 * 2
def baseEnd_5051272 : Nat := 864576817532622036256543

theorem tailTrace_5051272 : CollatzResearch.WordTrace tailWord_5051272 prefixEnd_5051272 864576817532622036256543 := by
  unfold tailWord_5051272
  simp only [CollatzResearch.WordTrace]
  refine ⟨92117512678055853710282035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122823350237407804947042713 92117512678055853710282035)
  ·
    refine ⟨138176269017083780565423053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92117512678055853710282035 138176269017083780565423053)
    ·
      refine ⟨51816100881406417712033645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138176269017083780565423053 51816100881406417712033645)
      ·
        refine ⟨19431037830527406642012617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51816100881406417712033645 19431037830527406642012617)
        ·
          refine ⟨14573278372895554981509463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19431037830527406642012617 14573278372895554981509463)
          ·
            refine ⟨21859917559343332472264195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14573278372895554981509463 21859917559343332472264195)
            ·
              refine ⟨32789876339014998708396293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21859917559343332472264195 32789876339014998708396293)
              ·
                refine ⟨6148101813565312257824305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32789876339014998708396293 6148101813565312257824305)
                ·
                  refine ⟨4611076360173984193368229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6148101813565312257824305 4611076360173984193368229)
                  ·
                    refine ⟨864576817532622036256543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4611076360173984193368229 864576817532622036256543)
                    ·
                      rfl

theorem cell23_5051272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_5051272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051272 prefixEnd_5051272 := by exact prefixLift 5051272
  have htrace : WordTrace (prefixWord ++ tailWord_5051272) baseStart_5051272 baseEnd_5051272 := by
    simpa [prefixWord, tailWord_5051272, baseEnd_5051272] using wordTrace_append hprefix tailTrace_5051272
  have hstable : (prefixWord ++ tailWord_5051272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051272).length < 2 ^ (prefixWord ++ tailWord_5051272).sum := by decide
  have hdescent : baseEnd_5051272 < baseStart_5051272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051285 : List Nat := [1, 3, 2, 1, 1, 6, 1, 8]
def baseStart_5051285 : Nat := 118140960795 + 5051285 * 2 ^ 59
def prefixEnd_5051285 : Nat := 4983230072969 + 3 ^ 40 * 5051285 * 2
def baseEnd_5051285 : Nat := 96064338068384242885447

theorem tailTrace_5051285 : CollatzResearch.WordTrace tailWord_5051285 prefixEnd_5051285 96064338068384242885447 := by
  unfold tailWord_5051285
  simp only [CollatzResearch.WordTrace]
  refine ⟨184235499505064610640787309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122823666336709740427191539 184235499505064610640787309)
  ·
    refine ⟨69088312314399228990295241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184235499505064610640787309 69088312314399228990295241)
    ·
      refine ⟨51816234235799421742721431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69088312314399228990295241 51816234235799421742721431)
      ·
        refine ⟨77724351353699132614082147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51816234235799421742721431 77724351353699132614082147)
        ·
          refine ⟨116586527030548698921123221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77724351353699132614082147 116586527030548698921123221)
          ·
            refine ⟨5464993454556970261927651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116586527030548698921123221 5464993454556970261927651)
            ·
              refine ⟨8197490181835455392891477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5464993454556970261927651 8197490181835455392891477)
              ·
                refine ⟨96064338068384242885447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8197490181835455392891477 96064338068384242885447)
                ·
                  rfl

theorem cell23_5051285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 8].length) (baseStart_5051285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051285 prefixEnd_5051285 := by exact prefixLift 5051285
  have htrace : WordTrace (prefixWord ++ tailWord_5051285) baseStart_5051285 baseEnd_5051285 := by
    simpa [prefixWord, tailWord_5051285, baseEnd_5051285] using wordTrace_append hprefix tailTrace_5051285
  have hstable : (prefixWord ++ tailWord_5051285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051285).length < 2 ^ (prefixWord ++ tailWord_5051285).sum := by decide
  have hdescent : baseEnd_5051285 < baseStart_5051285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051308 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 5]
def baseStart_5051308 : Nat := 118140960795 + 5051308 * 2 ^ 59
def prefixEnd_5051308 : Nat := 4983230072969 + 3 ^ 40 * 5051308 * 2
def baseEnd_5051308 : Nat := 2593748937901427967919463

theorem tailTrace_5051308 : CollatzResearch.WordTrace tailWord_5051308 prefixEnd_5051308 2593748937901427967919463 := by
  unfold tailWord_5051308
  simp only [CollatzResearch.WordTrace]
  refine ⟨92118169191990642784437289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122824225589320857045916385 92118169191990642784437289)
  ·
    refine ⟨69088626893992982088327967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92118169191990642784437289 69088626893992982088327967)
    ·
      refine ⟨103632940340989473132491951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69088626893992982088327967 103632940340989473132491951)
      ·
        refine ⟨155449410511484209698737927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103632940340989473132491951 155449410511484209698737927)
        ·
          refine ⟨233174115767226314548106891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155449410511484209698737927 233174115767226314548106891)
          ·
            refine ⟨349761173650839471822160337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233174115767226314548106891 349761173650839471822160337)
            ·
              refine ⟨262320880238129603866620253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349761173650839471822160337 262320880238129603866620253)
              ·
                refine ⟨98370330089298601449982595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262320880238129603866620253 98370330089298601449982595)
                ·
                  refine ⟨147555495133947902174973893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98370330089298601449982595 147555495133947902174973893)
                  ·
                    refine ⟨27666655337615231657807605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 147555495133947902174973893 27666655337615231657807605)
                    ·
                      refine ⟨2593748937901427967919463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27666655337615231657807605 2593748937901427967919463)
                      ·
                        rfl

theorem cell23_5051308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_5051308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051308 prefixEnd_5051308 := by exact prefixLift 5051308
  have htrace : WordTrace (prefixWord ++ tailWord_5051308) baseStart_5051308 baseEnd_5051308 := by
    simpa [prefixWord, tailWord_5051308, baseEnd_5051308] using wordTrace_append hprefix tailTrace_5051308
  have hstable : (prefixWord ++ tailWord_5051308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051308).length < 2 ^ (prefixWord ++ tailWord_5051308).sum := by decide
  have hdescent : baseEnd_5051308 < baseStart_5051308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051313 : List Nat := [1, 2, 2, 4, 3, 1, 2, 3, 1, 2, 2]
def baseStart_5051313 : Nat := 118140960795 + 5051313 * 2 ^ 59
def prefixEnd_5051313 : Nat := 4983230072969 + 3 ^ 40 * 5051313 * 2
def baseEnd_5051313 : Nat := 2593751505304700448356941

theorem tailTrace_5051313 : CollatzResearch.WordTrace tailWord_5051313 prefixEnd_5051313 2593751505304700448356941 := by
  unfold tailWord_5051313
  simp only [CollatzResearch.WordTrace]
  refine ⟨184236520748963171422806593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122824347165975447615204395 184236520748963171422806593)
  ·
    refine ⟨138177390561722378567104945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184236520748963171422806593 138177390561722378567104945)
    ·
      refine ⟨103633042921291783925328709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138177390561722378567104945 103633042921291783925328709)
      ·
        refine ⟨19431195547742209485999133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103633042921291783925328709 19431195547742209485999133)
        ·
          refine ⟨7286698330403328557249675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19431195547742209485999133 7286698330403328557249675)
          ·
            refine ⟨10930047495604992835874513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7286698330403328557249675 10930047495604992835874513)
            ·
              refine ⟨8197535621703744626905885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10930047495604992835874513 8197535621703744626905885)
              ·
                refine ⟨3074075858138904235089707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8197535621703744626905885 3074075858138904235089707)
                ·
                  refine ⟨4611113787208356352634561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3074075858138904235089707 4611113787208356352634561)
                  ·
                    refine ⟨3458335340406267264475921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4611113787208356352634561 3458335340406267264475921)
                    ·
                      refine ⟨2593751505304700448356941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3458335340406267264475921 2593751505304700448356941)
                      ·
                        rfl

theorem cell23_5051313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_5051313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051313 prefixEnd_5051313 := by exact prefixLift 5051313
  have htrace : WordTrace (prefixWord ++ tailWord_5051313) baseStart_5051313 baseEnd_5051313 := by
    simpa [prefixWord, tailWord_5051313, baseEnd_5051313] using wordTrace_append hprefix tailTrace_5051313
  have hstable : (prefixWord ++ tailWord_5051313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051313).length < 2 ^ (prefixWord ++ tailWord_5051313).sum := by decide
  have hdescent : baseEnd_5051313 < baseStart_5051313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051316 : List Nat := [2, 5, 2, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_5051316 : Nat := 118140960795 + 5051316 * 2 ^ 59
def prefixEnd_5051316 : Nat := 4983230072969 + 3 ^ 40 * 5051316 * 2
def baseEnd_5051316 : Nat := 2593753045746663936619427

theorem tailTrace_5051316 : CollatzResearch.WordTrace tailWord_5051316 prefixEnd_5051316 2593753045746663936619427 := by
  unfold tailWord_5051316
  simp only [CollatzResearch.WordTrace]
  refine ⟨92118315083976151467582901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122824420111968201956777201 92118315083976151467582901)
  ·
    refine ⟨8636092039122764200085897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92118315083976151467582901 8636092039122764200085897)
    ·
      refine ⟨6477069029342073150064423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8636092039122764200085897 6477069029342073150064423)
      ·
        refine ⟨9715603544013109725096635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6477069029342073150064423 9715603544013109725096635)
        ·
          refine ⟨14573405316019664587644953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9715603544013109725096635 14573405316019664587644953)
          ·
            refine ⟨10930053987014748440733715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14573405316019664587644953 10930053987014748440733715)
            ·
              refine ⟨16395080980522122661100573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10930053987014748440733715 16395080980522122661100573)
              ·
                refine ⟨6148155367695795997912715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16395080980522122661100573 6148155367695795997912715)
                ·
                  refine ⟨9222233051543693996869073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6148155367695795997912715 9222233051543693996869073)
                  ·
                    refine ⟨6916674788657770497651805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9222233051543693996869073 6916674788657770497651805)
                    ·
                      refine ⟨2593753045746663936619427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6916674788657770497651805 2593753045746663936619427)
                      ·
                        rfl

theorem cell23_5051316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_5051316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051316 prefixEnd_5051316 := by exact prefixLift 5051316
  have htrace : WordTrace (prefixWord ++ tailWord_5051316) baseStart_5051316 baseEnd_5051316 := by
    simpa [prefixWord, tailWord_5051316, baseEnd_5051316] using wordTrace_append hprefix tailTrace_5051316
  have hstable : (prefixWord ++ tailWord_5051316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051316).length < 2 ^ (prefixWord ++ tailWord_5051316).sum := by decide
  have hdescent : baseEnd_5051316 < baseStart_5051316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051403 : List Nat := [1, 1, 1, 1, 6, 4, 2, 1, 2, 2, 2]
def baseStart_5051403 : Nat := 118140960795 + 5051403 * 2 ^ 59
def prefixEnd_5051403 : Nat := 4983230072969 + 3 ^ 40 * 5051403 * 2
def baseEnd_5051403 : Nat := 2593797718563605096231527

theorem tailTrace_5051403 : CollatzResearch.WordTrace tailWord_5051403 prefixEnd_5051403 2593797718563605096231527 := by
  unfold tailWord_5051403
  simp only [CollatzResearch.WordTrace]
  refine ⟨184239803318637116793582863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122826535545758077862388575 184239803318637116793582863)
  ·
    refine ⟨276359704977955675190374295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184239803318637116793582863 276359704977955675190374295)
    ·
      refine ⟨414539557466933512785561443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276359704977955675190374295 414539557466933512785561443)
      ·
        refine ⟨621809336200400269178342165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414539557466933512785561443 621809336200400269178342165)
        ·
          refine ⟨29147312634393762617734789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 621809336200400269178342165 29147312634393762617734789)
          ·
            refine ⟨5465121118948830490825273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29147312634393762617734789 5465121118948830490825273)
            ·
              refine ⟨4098840839211622868118955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5465121118948830490825273 4098840839211622868118955)
              ·
                refine ⟨6148261258817434302178433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4098840839211622868118955 6148261258817434302178433)
                ·
                  refine ⟨4611195944113075726633825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6148261258817434302178433 4611195944113075726633825)
                  ·
                    refine ⟨3458396958084806794975369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4611195944113075726633825 3458396958084806794975369)
                    ·
                      refine ⟨2593797718563605096231527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3458396958084806794975369 2593797718563605096231527)
                      ·
                        rfl

theorem cell23_5051403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 2, 2, 2].length) (baseStart_5051403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051403 prefixEnd_5051403 := by exact prefixLift 5051403
  have htrace : WordTrace (prefixWord ++ tailWord_5051403) baseStart_5051403 baseEnd_5051403 := by
    simpa [prefixWord, tailWord_5051403, baseEnd_5051403] using wordTrace_append hprefix tailTrace_5051403
  have hstable : (prefixWord ++ tailWord_5051403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051403).length < 2 ^ (prefixWord ++ tailWord_5051403).sum := by decide
  have hdescent : baseEnd_5051403 < baseStart_5051403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051442 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_5051442 : Nat := 118140960795 + 5051442 * 2 ^ 59
def prefixEnd_5051442 : Nat := 4983230072969 + 3 ^ 40 * 5051442 * 2
def baseEnd_5051442 : Nat := 2593817744309130443643847

theorem tailTrace_5051442 : CollatzResearch.WordTrace tailWord_5051442 prefixEnd_5051442 2593817744309130443643847 := by
  unfold tailWord_5051442
  simp only [CollatzResearch.WordTrace]
  refine ⟨46060306441373956613563145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122827483843663884302835053 46060306441373956613563145)
  ·
    refine ⟨34545229831030467460172359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46060306441373956613563145 34545229831030467460172359)
    ·
      refine ⟨51817844746545701190258539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34545229831030467460172359 51817844746545701190258539)
      ·
        refine ⟨77726767119818551785387809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51817844746545701190258539 77726767119818551785387809)
        ·
          refine ⟨58295075339863913839040857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77726767119818551785387809 58295075339863913839040857)
          ·
            refine ⟨43721306504897935379280643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58295075339863913839040857 43721306504897935379280643)
            ·
              refine ⟨65581959757346903068920965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43721306504897935379280643 65581959757346903068920965)
              ·
                refine ⟨12296617454502544325422681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65581959757346903068920965 12296617454502544325422681)
                ·
                  refine ⟨9222463090876908244067011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12296617454502544325422681 9222463090876908244067011)
                  ·
                    refine ⟨13833694636315362366100517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9222463090876908244067011 13833694636315362366100517)
                    ·
                      refine ⟨2593817744309130443643847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13833694636315362366100517 2593817744309130443643847)
                      ·
                        rfl

theorem cell23_5051442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_5051442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051442 prefixEnd_5051442 := by exact prefixLift 5051442
  have htrace : WordTrace (prefixWord ++ tailWord_5051442) baseStart_5051442 baseEnd_5051442 := by
    simpa [prefixWord, tailWord_5051442, baseEnd_5051442] using wordTrace_append hprefix tailTrace_5051442
  have hstable : (prefixWord ++ tailWord_5051442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051442).length < 2 ^ (prefixWord ++ tailWord_5051442).sum := by decide
  have hdescent : baseEnd_5051442 < baseStart_5051442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051445 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_5051445 : Nat := 118140960795 + 5051445 * 2 ^ 59
def prefixEnd_5051445 : Nat := 4983230072969 + 3 ^ 40 * 5051445 * 2
def baseEnd_5051445 : Nat := 2593819284751093931906333

theorem tailTrace_5051445 : CollatzResearch.WordTrace tailWord_5051445 prefixEnd_5051445 2593819284751093931906333 := by
  unfold tailWord_5051445
  simp only [CollatzResearch.WordTrace]
  refine ⟨184241335184484957966611789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122827556789656638644407859 184241335184484957966611789)
  ·
    refine ⟨69090500694181859237479421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184241335184484957966611789 69090500694181859237479421)
    ·
      refine ⟨25908937760318197214054783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69090500694181859237479421 25908937760318197214054783)
      ·
        refine ⟨38863406640477295821082175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25908937760318197214054783 38863406640477295821082175)
        ·
          refine ⟨58295109960715943731623263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38863406640477295821082175 58295109960715943731623263)
          ·
            refine ⟨87442664941073915597434895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58295109960715943731623263 87442664941073915597434895)
            ·
              refine ⟨131163997411610873396152343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87442664941073915597434895 131163997411610873396152343)
              ·
                refine ⟨196745996117416310094228515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131163997411610873396152343 196745996117416310094228515)
                ·
                  refine ⟨295118994176124465141342773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196745996117416310094228515 295118994176124465141342773)
                  ·
                    refine ⟨27667405704011668607000885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 295118994176124465141342773 27667405704011668607000885)
                    ·
                      refine ⟨2593819284751093931906333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27667405704011668607000885 2593819284751093931906333)
                      ·
                        rfl

theorem cell23_5051445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_5051445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051445 prefixEnd_5051445 := by exact prefixLift 5051445
  have htrace : WordTrace (prefixWord ++ tailWord_5051445) baseStart_5051445 baseEnd_5051445 := by
    simpa [prefixWord, tailWord_5051445, baseEnd_5051445] using wordTrace_append hprefix tailTrace_5051445
  have hstable : (prefixWord ++ tailWord_5051445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051445).length < 2 ^ (prefixWord ++ tailWord_5051445).sum := by decide
  have hdescent : baseEnd_5051445 < baseStart_5051445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051455 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 4]
def baseStart_5051455 : Nat := 118140960795 + 5051455 * 2 ^ 59
def prefixEnd_5051455 : Nat := 4983230072969 + 3 ^ 40 * 5051455 * 2
def baseEnd_5051455 : Nat := 2593824419557638892781287

theorem tailTrace_5051455 : CollatzResearch.WordTrace tailWord_5051455 prefixEnd_5051455 2593824419557638892781287 := by
  unfold tailWord_5051455
  simp only [CollatzResearch.WordTrace]
  refine ⟨184241699914448729674475819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122827799942965819782983879 184241699914448729674475819)
  ·
    refine ⟨276362549871673094511713729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184241699914448729674475819 276362549871673094511713729)
    ·
      refine ⟨207271912403754820883785297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276362549871673094511713729 207271912403754820883785297)
      ·
        refine ⟨155453934302816115662838973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207271912403754820883785297 155453934302816115662838973)
        ·
          refine ⟨58295225363556043373564615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155453934302816115662838973 58295225363556043373564615)
          ·
            refine ⟨87442838045334065060346923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58295225363556043373564615 87442838045334065060346923)
            ·
              refine ⟨131164257068001097590520385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87442838045334065060346923 131164257068001097590520385)
              ·
                refine ⟨98373192801000823192890289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131164257068001097590520385 98373192801000823192890289)
                ·
                  refine ⟨73779894600750617394667717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98373192801000823192890289 73779894600750617394667717)
                  ·
                    refine ⟨13833730237640740761500197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73779894600750617394667717 13833730237640740761500197)
                    ·
                      refine ⟨2593824419557638892781287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13833730237640740761500197 2593824419557638892781287)
                      ·
                        rfl

theorem cell23_5051455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_5051455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051455 prefixEnd_5051455 := by exact prefixLift 5051455
  have htrace : WordTrace (prefixWord ++ tailWord_5051455) baseStart_5051455 baseEnd_5051455 := by
    simpa [prefixWord, tailWord_5051455, baseEnd_5051455] using wordTrace_append hprefix tailTrace_5051455
  have hstable : (prefixWord ++ tailWord_5051455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051455).length < 2 ^ (prefixWord ++ tailWord_5051455).sum := by decide
  have hdescent : baseEnd_5051455 < baseStart_5051455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051469 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_5051469 : Nat := 118140960795 + 5051469 * 2 ^ 59
def prefixEnd_5051469 : Nat := 4983230072969 + 3 ^ 40 * 5051469 * 2
def baseEnd_5051469 : Nat := 864610536095600612668741

theorem tailTrace_5051469 : CollatzResearch.WordTrace tailWord_5051469 prefixEnd_5051469 864610536095600612668741 := by
  unfold tailWord_5051469
  simp only [CollatzResearch.WordTrace]
  refine ⟨184242210536398010065485461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122828140357598673376990307 184242210536398010065485461)
  ·
    refine ⟨8636353618893656721819631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 184242210536398010065485461 8636353618893656721819631)
    ·
      refine ⟨12954530428340485082729447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8636353618893656721819631 12954530428340485082729447)
      ·
        refine ⟨19431795642510727624094171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12954530428340485082729447 19431795642510727624094171)
        ·
          refine ⟨29147693463766091436141257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19431795642510727624094171 29147693463766091436141257)
          ·
            refine ⟨21860770097824568577105943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29147693463766091436141257 21860770097824568577105943)
            ·
              refine ⟨32791155146736852865658915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21860770097824568577105943 32791155146736852865658915)
              ·
                refine ⟨49186732720105279298488373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32791155146736852865658915 49186732720105279298488373)
                ·
                  refine ⟨4611256192509869934233285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49186732720105279298488373 4611256192509869934233285)
                  ·
                    refine ⟨864610536095600612668741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4611256192509869934233285 864610536095600612668741)
                    ·
                      rfl

theorem cell23_5051469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_5051469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051469 prefixEnd_5051469 := by exact prefixLift 5051469
  have htrace : WordTrace (prefixWord ++ tailWord_5051469) baseStart_5051469 baseEnd_5051469 := by
    simpa [prefixWord, tailWord_5051469, baseEnd_5051469] using wordTrace_append hprefix tailTrace_5051469
  have hstable : (prefixWord ++ tailWord_5051469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051469).length < 2 ^ (prefixWord ++ tailWord_5051469).sum := by decide
  have hdescent : baseEnd_5051469 < baseStart_5051469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051502 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_5051502 : Nat := 118140960795 + 5051502 * 2 ^ 59
def prefixEnd_5051502 : Nat := 4983230072969 + 3 ^ 40 * 5051502 * 2
def baseEnd_5051502 : Nat := 2593848553148400208893571

theorem tailTrace_5051502 : CollatzResearch.WordTrace tailWord_5051502 prefixEnd_5051502 2593848553148400208893571 := by
  unfold tailWord_5051502
  simp only [CollatzResearch.WordTrace]
  refine ⟨23030426768159807087679595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122828942763518971134291173 23030426768159807087679595)
  ·
    refine ⟨34545640152239710631519393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23030426768159807087679595 34545640152239710631519393)
    ·
      refine ⟨25909230114179782973639545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34545640152239710631519393 25909230114179782973639545)
      ·
        refine ⟨19431922585634837230229659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25909230114179782973639545 19431922585634837230229659)
        ·
          refine ⟨29147883878452255845344489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19431922585634837230229659 29147883878452255845344489)
          ·
            refine ⟨21860912908839191884008367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29147883878452255845344489 21860912908839191884008367)
            ·
              refine ⟨32791369363258787826012551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21860912908839191884008367 32791369363258787826012551)
              ·
                refine ⟨49187054044888181739018827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32791369363258787826012551 49187054044888181739018827)
                ·
                  refine ⟨73780581067332272608528241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49187054044888181739018827 73780581067332272608528241)
                  ·
                    refine ⟨55335435800499204456396181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73780581067332272608528241 55335435800499204456396181)
                    ·
                      refine ⟨2593848553148400208893571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55335435800499204456396181 2593848553148400208893571)
                      ·
                        rfl

theorem cell23_5051502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_5051502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051502 prefixEnd_5051502 := by exact prefixLift 5051502
  have htrace : WordTrace (prefixWord ++ tailWord_5051502) baseStart_5051502 baseEnd_5051502 := by
    simpa [prefixWord, tailWord_5051502, baseEnd_5051502] using wordTrace_append hprefix tailTrace_5051502
  have hstable : (prefixWord ++ tailWord_5051502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051502).length < 2 ^ (prefixWord ++ tailWord_5051502).sum := by decide
  have hdescent : baseEnd_5051502 < baseStart_5051502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051505 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 7]
def baseStart_5051505 : Nat := 118140960795 + 5051505 * 2 ^ 59
def prefixEnd_5051505 : Nat := 4983230072969 + 3 ^ 40 * 5051505 * 2
def baseEnd_5051505 : Nat := 2593850093590363697156057

theorem tailTrace_5051505 : CollatzResearch.WordTrace tailWord_5051505 prefixEnd_5051505 2593850093590363697156057 := by
  unfold tailWord_5051505
  simp only [CollatzResearch.WordTrace]
  refine ⟨184243523564267588213795969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122829015709511725475863979 184243523564267588213795969)
  ·
    refine ⟨138182642673200691160346977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184243523564267588213795969 138182642673200691160346977)
    ·
      refine ⟨103636982004900518370260233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138182642673200691160346977 103636982004900518370260233)
      ·
        refine ⟨77727736503675388777695175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103636982004900518370260233 77727736503675388777695175)
        ·
          refine ⟨116591604755513083166542763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77727736503675388777695175 116591604755513083166542763)
          ·
            refine ⟨174887407133269624749814145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116591604755513083166542763 174887407133269624749814145)
            ·
              refine ⟨131165555349952218562360609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174887407133269624749814145 131165555349952218562360609)
              ·
                refine ⟨98374166512464163921770457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131165555349952218562360609 98374166512464163921770457)
                ·
                  refine ⟨73780624884348122941327843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98374166512464163921770457 73780624884348122941327843)
                  ·
                    refine ⟨110670937326522184411991765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73780624884348122941327843 110670937326522184411991765)
                    ·
                      refine ⟨2593850093590363697156057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110670937326522184411991765 2593850093590363697156057)
                      ·
                        rfl

theorem cell23_5051505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_5051505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051505 prefixEnd_5051505 := by exact prefixLift 5051505
  have htrace : WordTrace (prefixWord ++ tailWord_5051505) baseStart_5051505 baseEnd_5051505 := by
    simpa [prefixWord, tailWord_5051505, baseEnd_5051505] using wordTrace_append hprefix tailTrace_5051505
  have hstable : (prefixWord ++ tailWord_5051505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051505).length < 2 ^ (prefixWord ++ tailWord_5051505).sum := by decide
  have hdescent : baseEnd_5051505 < baseStart_5051505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051529 : List Nat := [1, 2, 1, 1, 4, 4, 2, 2, 1, 5]
def baseStart_5051529 : Nat := 118140960795 + 5051529 * 2 ^ 59
def prefixEnd_5051529 : Nat := 4983230072969 + 3 ^ 40 * 5051529 * 2
def baseEnd_5051529 : Nat := 864620805708690534418649

theorem tailTrace_5051529 : CollatzResearch.WordTrace tailWord_5051529 prefixEnd_5051529 864620805708690534418649 := by
  unfold tailWord_5051529
  simp only [CollatzResearch.WordTrace]
  refine ⟨184244398916180640312669641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122829599277453760208446427 184244398916180640312669641)
  ·
    refine ⟨138183299187135480234502231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184244398916180640312669641 138183299187135480234502231)
    ·
      refine ⟨207274948780703220351753347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138183299187135480234502231 207274948780703220351753347)
      ·
        refine ⟨310912423171054830527630021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207274948780703220351753347 310912423171054830527630021)
        ·
          refine ⟨58296079344572780723930629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 310912423171054830527630021 58296079344572780723930629)
          ·
            refine ⟨10930514877107396385736993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58296079344572780723930629 10930514877107396385736993)
            ·
              refine ⟨8197886157830547289302745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10930514877107396385736993 8197886157830547289302745)
              ·
                refine ⟨6148414618372910466977059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8197886157830547289302745 6148414618372910466977059)
                ·
                  refine ⟨9222621927559365700465589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6148414618372910466977059 9222621927559365700465589)
                  ·
                    refine ⟨864620805708690534418649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9222621927559365700465589 864620805708690534418649)
                    ·
                      rfl

theorem cell23_5051529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 5].length) (baseStart_5051529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051529 prefixEnd_5051529 := by exact prefixLift 5051529
  have htrace : WordTrace (prefixWord ++ tailWord_5051529) baseStart_5051529 baseEnd_5051529 := by
    simpa [prefixWord, tailWord_5051529, baseEnd_5051529] using wordTrace_append hprefix tailTrace_5051529
  have hstable : (prefixWord ++ tailWord_5051529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051529).length < 2 ^ (prefixWord ++ tailWord_5051529).sum := by decide
  have hdescent : baseEnd_5051529 < baseStart_5051529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051532 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 3, 1, 4]
def baseStart_5051532 : Nat := 118140960795 + 5051532 * 2 ^ 59
def prefixEnd_5051532 : Nat := 4983230072969 + 3 ^ 40 * 5051532 * 2
def baseEnd_5051532 : Nat := 2593863957568035091518433

theorem tailTrace_5051532 : CollatzResearch.WordTrace tailWord_5051532 prefixEnd_5051532 2593863957568035091518433 := by
  unfold tailWord_5051532
  simp only [CollatzResearch.WordTrace]
  refine ⟨92122254167584885912514425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122829672223446514550019233 92122254167584885912514425)
  ·
    refine ⟨69091690625688664434385819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92122254167584885912514425 69091690625688664434385819)
    ·
      refine ⟨103637535938532996651578729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69091690625688664434385819 103637535938532996651578729)
      ·
        refine ⟨77728151953899747488684047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103637535938532996651578729 77728151953899747488684047)
        ·
          refine ⟨116592227930849621233026071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77728151953899747488684047 116592227930849621233026071)
          ·
            refine ⟨174888341896274431849539107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116592227930849621233026071 174888341896274431849539107)
            ·
              refine ⟨262332512844411647774308661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174888341896274431849539107 262332512844411647774308661)
              ·
                refine ⟨24593673079163591978841437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 262332512844411647774308661 24593673079163591978841437)
                ·
                  refine ⟨9222627404686346992065539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24593673079163591978841437 9222627404686346992065539)
                  ·
                    refine ⟨13833941107029520488098309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9222627404686346992065539 13833941107029520488098309)
                    ·
                      refine ⟨2593863957568035091518433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13833941107029520488098309 2593863957568035091518433)
                      ·
                        rfl

theorem cell23_5051532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_5051532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051532 prefixEnd_5051532 := by exact prefixLift 5051532
  have htrace : WordTrace (prefixWord ++ tailWord_5051532) baseStart_5051532 baseEnd_5051532 := by
    simpa [prefixWord, tailWord_5051532, baseEnd_5051532] using wordTrace_append hprefix tailTrace_5051532
  have hstable : (prefixWord ++ tailWord_5051532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051532).length < 2 ^ (prefixWord ++ tailWord_5051532).sum := by decide
  have hdescent : baseEnd_5051532 < baseStart_5051532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051543 : List Nat := [1, 1, 3, 3, 3, 1, 3, 3, 1, 1, 3]
def baseStart_5051543 : Nat := 118140960795 + 5051543 * 2 ^ 59
def prefixEnd_5051543 : Nat := 4983230072969 + 3 ^ 40 * 5051543 * 2
def baseEnd_5051543 : Nat := 2593869605855234548480883

theorem tailTrace_5051543 : CollatzResearch.WordTrace tailWord_5051543 prefixEnd_5051543 2593869605855234548480883 := by
  unfold tailWord_5051543
  simp only [CollatzResearch.WordTrace]
  refine ⟨184244909538129920703679283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122829939692086613802452855 184244909538129920703679283)
  ·
    refine ⟨276367364307194881055518925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184244909538129920703679283 276367364307194881055518925)
    ·
      refine ⟨103637761615198080395819597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276367364307194881055518925 103637761615198080395819597)
      ·
        refine ⟨38864160605699280148432349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103637761615198080395819597 38864160605699280148432349)
        ·
          refine ⟨14574060227137230055662131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38864160605699280148432349 14574060227137230055662131)
          ·
            refine ⟨21861090340705845083493197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14574060227137230055662131 21861090340705845083493197)
            ·
              refine ⟨8197908877764691906309949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21861090340705845083493197 8197908877764691906309949)
              ·
                refine ⟨3074215829161759464866231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8197908877764691906309949 3074215829161759464866231)
                ·
                  refine ⟨4611323743742639197299347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3074215829161759464866231 4611323743742639197299347)
                  ·
                    refine ⟨6916985615613958795949021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4611323743742639197299347 6916985615613958795949021)
                    ·
                      refine ⟨2593869605855234548480883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6916985615613958795949021 2593869605855234548480883)
                      ·
                        rfl

theorem cell23_5051543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_5051543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051543 prefixEnd_5051543 := by exact prefixLift 5051543
  have htrace : WordTrace (prefixWord ++ tailWord_5051543) baseStart_5051543 baseEnd_5051543 := by
    simpa [prefixWord, tailWord_5051543, baseEnd_5051543] using wordTrace_append hprefix tailTrace_5051543
  have hstable : (prefixWord ++ tailWord_5051543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051543).length < 2 ^ (prefixWord ++ tailWord_5051543).sum := by decide
  have hdescent : baseEnd_5051543 < baseStart_5051543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051549 : List Nat := [1, 4, 2, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_5051549 : Nat := 118140960795 + 5051549 * 2 ^ 59
def prefixEnd_5051549 : Nat := 4983230072969 + 3 ^ 40 * 5051549 * 2
def baseEnd_5051549 : Nat := 2593872686739161525005855

theorem tailTrace_5051549 : CollatzResearch.WordTrace tailWord_5051549 prefixEnd_5051549 2593872686739161525005855 := by
  unfold tailWord_5051549
  simp only [CollatzResearch.WordTrace]
  refine ⟨184245128376108183728397701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122830085584072122485598467 184245128376108183728397701)
  ·
    refine ⟨34545961570520284449074569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184245128376108183728397701 34545961570520284449074569)
    ·
      refine ⟨25909471177890213336805927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34545961570520284449074569 25909471177890213336805927)
      ·
        refine ⟨38864206766835320005208891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25909471177890213336805927 38864206766835320005208891)
        ·
          refine ⟨58296310150252980007813337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38864206766835320005208891 58296310150252980007813337)
          ·
            refine ⟨43722232612689735005860003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58296310150252980007813337 43722232612689735005860003)
            ·
              refine ⟨65583348919034602508790005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43722232612689735005860003 65583348919034602508790005)
              ·
                refine ⟨6148438961159493985199063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65583348919034602508790005 6148438961159493985199063)
                ·
                  refine ⟨9222658441739240977798595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6148438961159493985199063 9222658441739240977798595)
                  ·
                    refine ⟨13833987662608861466697893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9222658441739240977798595 13833987662608861466697893)
                    ·
                      refine ⟨2593872686739161525005855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13833987662608861466697893 2593872686739161525005855)
                      ·
                        rfl

theorem cell23_5051549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_5051549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051549 prefixEnd_5051549 := by exact prefixLift 5051549
  have htrace : WordTrace (prefixWord ++ tailWord_5051549) baseStart_5051549 baseEnd_5051549 := by
    simpa [prefixWord, tailWord_5051549, baseEnd_5051549] using wordTrace_append hprefix tailTrace_5051549
  have hstable : (prefixWord ++ tailWord_5051549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051549).length < 2 ^ (prefixWord ++ tailWord_5051549).sum := by decide
  have hdescent : baseEnd_5051549 < baseStart_5051549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051569 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 1, 1, 5]
def baseStart_5051569 : Nat := 118140960795 + 5051569 * 2 ^ 59
def prefixEnd_5051569 : Nat := 4983230072969 + 3 ^ 40 * 5051569 * 2
def baseEnd_5051569 : Nat := 2593882956352251446755763

theorem tailTrace_5051569 : CollatzResearch.WordTrace tailWord_5051569 prefixEnd_5051569 2593882956352251446755763 := by
  unfold tailWord_5051569
  simp only [CollatzResearch.WordTrace]
  refine ⟨184245857836035727144125761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122830571890690484762750507 184245857836035727144125761)
  ·
    refine ⟨138184393377026795358094321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184245857836035727144125761 138184393377026795358094321)
    ·
      refine ⟨103638295032770096518570741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138184393377026795358094321 103638295032770096518570741)
      ·
        refine ⟨9716090159322196548616007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103638295032770096518570741 9716090159322196548616007)
        ·
          refine ⟨14574135238983294822924011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9716090159322196548616007 14574135238983294822924011)
          ·
            refine ⟨21861202858474942234386017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14574135238983294822924011 21861202858474942234386017)
            ·
              refine ⟨16395902143856206675789513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21861202858474942234386017 16395902143856206675789513)
              ·
                refine ⟨12296926607892155006842135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16395902143856206675789513 12296926607892155006842135)
                ·
                  refine ⟨18445389911838232510263203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12296926607892155006842135 18445389911838232510263203)
                  ·
                    refine ⟨27668084867757348765394805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18445389911838232510263203 27668084867757348765394805)
                    ·
                      refine ⟨2593882956352251446755763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27668084867757348765394805 2593882956352251446755763)
                      ·
                        rfl

theorem cell23_5051569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_5051569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051569 prefixEnd_5051569 := by exact prefixLift 5051569
  have htrace : WordTrace (prefixWord ++ tailWord_5051569) baseStart_5051569 baseEnd_5051569 := by
    simpa [prefixWord, tailWord_5051569, baseEnd_5051569] using wordTrace_append hprefix tailTrace_5051569
  have hstable : (prefixWord ++ tailWord_5051569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051569).length < 2 ^ (prefixWord ++ tailWord_5051569).sum := by decide
  have hdescent : baseEnd_5051569 < baseStart_5051569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051599 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 4, 1, 3]
def baseStart_5051599 : Nat := 118140960795 + 5051599 * 2 ^ 59
def prefixEnd_5051599 : Nat := 4983230072969 + 3 ^ 40 * 5051599 * 2
def baseEnd_5051599 : Nat := 2593898360771886329380625

theorem tailTrace_5051599 : CollatzResearch.WordTrace tailWord_5051599 prefixEnd_5051599 2593898360771886329380625 := by
  unfold tailWord_5051599
  simp only [CollatzResearch.WordTrace]
  refine ⟨184246952025927042267717851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122831301350618028178478567 184246952025927042267717851)
  ·
    refine ⟨276370428038890563401576777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184246952025927042267717851 276370428038890563401576777)
    ·
      refine ⟨207277821029167922551182583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276370428038890563401576777 207277821029167922551182583)
      ·
        refine ⟨310916731543751883826773875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207277821029167922551182583 310916731543751883826773875)
        ·
          refine ⟨466375097315627825740160813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310916731543751883826773875 466375097315627825740160813)
          ·
            refine ⟨174890661493360434652560305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 466375097315627825740160813 174890661493360434652560305)
            ·
              refine ⟨131167996120020325989420229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174890661493360434652560305 131167996120020325989420229)
              ·
                refine ⟨24593999272503811123016293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131167996120020325989420229 24593999272503811123016293)
                ·
                  refine ⟨4611374863594464585565555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24593999272503811123016293 4611374863594464585565555)
                  ·
                    refine ⟨6917062295391696878348333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4611374863594464585565555 6917062295391696878348333)
                    ·
                      refine ⟨2593898360771886329380625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6917062295391696878348333 2593898360771886329380625)
                      ·
                        rfl

theorem cell23_5051599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 1, 3].length) (baseStart_5051599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051599 prefixEnd_5051599 := by exact prefixLift 5051599
  have htrace : WordTrace (prefixWord ++ tailWord_5051599) baseStart_5051599 baseEnd_5051599 := by
    simpa [prefixWord, tailWord_5051599, baseEnd_5051599] using wordTrace_append hprefix tailTrace_5051599
  have hstable : (prefixWord ++ tailWord_5051599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051599).length < 2 ^ (prefixWord ++ tailWord_5051599).sum := by decide
  have hdescent : baseEnd_5051599 < baseStart_5051599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051606 : List Nat := [5, 2, 1, 2, 3, 10]
def baseStart_5051606 : Nat := 118140960795 + 5051606 * 2 ^ 59
def prefixEnd_5051606 : Nat := 4983230072969 + 3 ^ 40 * 5051606 * 2
def baseEnd_5051606 : Nat := 10674493642536904534951

theorem tailTrace_5051606 : CollatzResearch.WordTrace tailWord_5051606 prefixEnd_5051606 10674493642536904534951 := by
  unfold tailWord_5051606
  simp only [CollatzResearch.WordTrace]
  refine ⟨11515450458556355153951417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122831471557934454975481781 11515450458556355153951417)
  ·
    refine ⟨8636587843917266365463563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11515450458556355153951417 8636587843917266365463563)
    ·
      refine ⟨12954881765875899548195345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8636587843917266365463563 12954881765875899548195345)
      ·
        refine ⟨9716161324406924661146509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12954881765875899548195345 9716161324406924661146509)
        ·
          refine ⟨3643560496652596747929941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9716161324406924661146509 3643560496652596747929941)
          ·
            refine ⟨10674493642536904534951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3643560496652596747929941 10674493642536904534951)
            ·
              rfl

theorem cell23_5051606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 10].length) (baseStart_5051606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051606 prefixEnd_5051606 := by exact prefixLift 5051606
  have htrace : WordTrace (prefixWord ++ tailWord_5051606) baseStart_5051606 baseEnd_5051606 := by
    simpa [prefixWord, tailWord_5051606, baseEnd_5051606] using wordTrace_append hprefix tailTrace_5051606
  have hstable : (prefixWord ++ tailWord_5051606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051606).length < 2 ^ (prefixWord ++ tailWord_5051606).sum := by decide
  have hdescent : baseEnd_5051606 < baseStart_5051606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051616 : List Nat := [2, 1, 1, 3, 1, 4, 1, 4, 2, 1, 3]
def baseStart_5051616 : Nat := 118140960795 + 5051616 * 2 ^ 59
def prefixEnd_5051616 : Nat := 4983230072969 + 3 ^ 40 * 5051616 * 2
def baseEnd_5051616 : Nat := 2593907089943012762868047

theorem tailTrace_5051616 : CollatzResearch.WordTrace tailWord_5051616 prefixEnd_5051616 2593907089943012762868047 := by
  unfold tailWord_5051616
  simp only [CollatzResearch.WordTrace]
  refine ⟨92123786033432727085543351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122831714711243636114057801 92123786033432727085543351)
  ·
    refine ⟨138185679050149090628315027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92123786033432727085543351 138185679050149090628315027)
    ·
      refine ⟨207278518575223635942472541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138185679050149090628315027 207278518575223635942472541)
      ·
        refine ⟨77729444465708863478427203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207278518575223635942472541 77729444465708863478427203)
        ·
          refine ⟨116594166698563295217640805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77729444465708863478427203 116594166698563295217640805)
          ·
            refine ⟨21861406255980617853307651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116594166698563295217640805 21861406255980617853307651)
            ·
              refine ⟨32792109383970926779961477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21861406255980617853307651 32792109383970926779961477)
              ·
                refine ⟨6148520509494548771242777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32792109383970926779961477 6148520509494548771242777)
                ·
                  refine ⟨4611390382120911578432083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6148520509494548771242777 4611390382120911578432083)
                  ·
                    refine ⟨6917085573181367367648125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4611390382120911578432083 6917085573181367367648125)
                    ·
                      refine ⟨2593907089943012762868047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6917085573181367367648125 2593907089943012762868047)
                      ·
                        rfl

theorem cell23_5051616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_5051616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051616 prefixEnd_5051616 := by exact prefixLift 5051616
  have htrace : WordTrace (prefixWord ++ tailWord_5051616) baseStart_5051616 baseEnd_5051616 := by
    simpa [prefixWord, tailWord_5051616, baseEnd_5051616] using wordTrace_append hprefix tailTrace_5051616
  have hstable : (prefixWord ++ tailWord_5051616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051616).length < 2 ^ (prefixWord ++ tailWord_5051616).sum := by decide
  have hdescent : baseEnd_5051616 < baseStart_5051616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051617 : List Nat := [1, 2, 3, 1, 3, 4, 2, 2, 1, 2, 2]
def baseStart_5051617 : Nat := 118140960795 + 5051617 * 2 ^ 59
def prefixEnd_5051617 : Nat := 4983230072969 + 3 ^ 40 * 5051617 * 2
def baseEnd_5051617 : Nat := 2593907603423667258955543

theorem tailTrace_5051617 : CollatzResearch.WordTrace tailWord_5051617 prefixEnd_5051617 2593907603423667258955543 := by
  unfold tailWord_5051617
  simp only [CollatzResearch.WordTrace]
  refine ⟨184247608539861831341873105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122831739026574554227915403 184247608539861831341873105)
  ·
    refine ⟨138185706404896373506404829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184247608539861831341873105 138185706404896373506404829)
    ·
      refine ⟨51819639901836140064901811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138185706404896373506404829 51819639901836140064901811)
      ·
        refine ⟨77729459852754210097352717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51819639901836140064901811 77729459852754210097352717)
        ·
          refine ⟨29148547444782828786507269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77729459852754210097352717 29148547444782828786507269)
          ·
            refine ⟨5465352645896780397470113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29148547444782828786507269 5465352645896780397470113)
            ·
              refine ⟨4099014484422585298102585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5465352645896780397470113 4099014484422585298102585)
              ·
                refine ⟨3074260863316938973576939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4099014484422585298102585 3074260863316938973576939)
                ·
                  refine ⟨4611391294975408460365409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3074260863316938973576939 4611391294975408460365409)
                  ·
                    refine ⟨3458543471231556345274057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4611391294975408460365409 3458543471231556345274057)
                    ·
                      refine ⟨2593907603423667258955543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3458543471231556345274057 2593907603423667258955543)
                      ·
                        rfl

theorem cell23_5051617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_5051617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051617 prefixEnd_5051617 := by exact prefixLift 5051617
  have htrace : WordTrace (prefixWord ++ tailWord_5051617) baseStart_5051617 baseEnd_5051617 := by
    simpa [prefixWord, tailWord_5051617, baseEnd_5051617] using wordTrace_append hprefix tailTrace_5051617
  have hstable : (prefixWord ++ tailWord_5051617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051617).length < 2 ^ (prefixWord ++ tailWord_5051617).sum := by decide
  have hdescent : baseEnd_5051617 < baseStart_5051617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051626 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 3, 3, 2]
def baseStart_5051626 : Nat := 118140960795 + 5051626 * 2 ^ 59
def prefixEnd_5051626 : Nat := 4983230072969 + 3 ^ 40 * 5051626 * 2
def baseEnd_5051626 : Nat := 2593912224749557723743001

theorem tailTrace_5051626 : CollatzResearch.WordTrace tailWord_5051626 prefixEnd_5051626 2593912224749557723743001 := by
  unfold tailWord_5051626
  simp only [CollatzResearch.WordTrace]
  refine ⟨46061984199207306469737683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122831957864552817252633821 46061984199207306469737683)
  ·
    refine ⟨69092976298810959704606525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46061984199207306469737683 69092976298810959704606525)
    ·
      refine ⟨25909866112054109889227447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69092976298810959704606525 25909866112054109889227447)
      ·
        refine ⟨38864799168081164833841171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25909866112054109889227447 38864799168081164833841171)
        ·
          refine ⟨58297198752121747250761757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38864799168081164833841171 58297198752121747250761757)
          ·
            refine ⟨21861449532045655219035659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58297198752121747250761757 21861449532045655219035659)
            ·
              refine ⟨32792174298068482828553489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21861449532045655219035659 32792174298068482828553489)
              ·
                refine ⟨24594130723551362121415117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32792174298068482828553489 24594130723551362121415117)
                ·
                  refine ⟨9222799021331760795530669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24594130723551362121415117 9222799021331760795530669)
                  ·
                    refine ⟨3458549632999410298324001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9222799021331760795530669 3458549632999410298324001)
                    ·
                      refine ⟨2593912224749557723743001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3458549632999410298324001 2593912224749557723743001)
                      ·
                        rfl

theorem cell23_5051626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_5051626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051626 prefixEnd_5051626 := by exact prefixLift 5051626
  have htrace : WordTrace (prefixWord ++ tailWord_5051626) baseStart_5051626 baseEnd_5051626 := by
    simpa [prefixWord, tailWord_5051626, baseEnd_5051626] using wordTrace_append hprefix tailTrace_5051626
  have hstable : (prefixWord ++ tailWord_5051626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051626).length < 2 ^ (prefixWord ++ tailWord_5051626).sum := by decide
  have hdescent : baseEnd_5051626 < baseStart_5051626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051639 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 5, 4, 2]
def baseStart_5051639 : Nat := 118140960795 + 5051639 * 2 ^ 59
def prefixEnd_5051639 : Nat := 4983230072969 + 3 ^ 40 * 5051639 * 2
def baseEnd_5051639 : Nat := 2593918899998066172880441

theorem tailTrace_5051639 : CollatzResearch.WordTrace tailWord_5051639 prefixEnd_5051639 2593918899998066172880441 := by
  unfold tailWord_5051639
  simp only [CollatzResearch.WordTrace]
  refine ⟨184248410945782129099173971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122832273963854752732782647 184248410945782129099173971)
  ·
    refine ⟨276372616418673193648760957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184248410945782129099173971 276372616418673193648760957)
    ·
      refine ⟨103639731157002447618285359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276372616418673193648760957 103639731157002447618285359)
      ·
        refine ⟨155459596735503671427428039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103639731157002447618285359 155459596735503671427428039)
        ·
          refine ⟨233189395103255507141142059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155459596735503671427428039 233189395103255507141142059)
          ·
            refine ⟨349784092654883260711713089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233189395103255507141142059 349784092654883260711713089)
            ·
              refine ⟨262338069491162445533784817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349784092654883260711713089 262338069491162445533784817)
              ·
                refine ⟨196753552118371834150338613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262338069491162445533784817 196753552118371834150338613)
                ·
                  refine ⟨18445645511097359451594245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 196753552118371834150338613 18445645511097359451594245)
                  ·
                    refine ⟨3458558533330754897173921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18445645511097359451594245 3458558533330754897173921)
                    ·
                      refine ⟨2593918899998066172880441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3458558533330754897173921 2593918899998066172880441)
                      ·
                        rfl

theorem cell23_5051639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 4, 2].length) (baseStart_5051639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051639 prefixEnd_5051639 := by exact prefixLift 5051639
  have htrace : WordTrace (prefixWord ++ tailWord_5051639) baseStart_5051639 baseEnd_5051639 := by
    simpa [prefixWord, tailWord_5051639, baseEnd_5051639] using wordTrace_append hprefix tailTrace_5051639
  have hstable : (prefixWord ++ tailWord_5051639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051639).length < 2 ^ (prefixWord ++ tailWord_5051639).sum := by decide
  have hdescent : baseEnd_5051639 < baseStart_5051639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051660 : List Nat := [2, 2, 1, 2, 2, 5, 2, 1, 1, 3, 2]
def baseStart_5051660 : Nat := 118140960795 + 5051660 * 2 ^ 59
def prefixEnd_5051660 : Nat := 4983230072969 + 3 ^ 40 * 5051660 * 2
def baseEnd_5051660 : Nat := 2593929683091810590717845

theorem tailTrace_5051660 : CollatzResearch.WordTrace tailWord_5051660 prefixEnd_5051660 2593929683091810590717845 := by
  unfold tailWord_5051660
  simp only [CollatzResearch.WordTrace]
  refine ⟨92124588439353024842844217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122832784585804033123792289 92124588439353024842844217)
  ·
    refine ⟨69093441329514768632133163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92124588439353024842844217 69093441329514768632133163)
    ·
      refine ⟨103640161994272152948199745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69093441329514768632133163 103640161994272152948199745)
      ·
        refine ⟨77730121495704114711149809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103640161994272152948199745 77730121495704114711149809)
        ·
          refine ⟨58297591121778086033362357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77730121495704114711149809 58297591121778086033362357)
          ·
            refine ⟨5465399167666695565627721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58297591121778086033362357 5465399167666695565627721)
            ·
              refine ⟨4099049375750021674220791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5465399167666695565627721 4099049375750021674220791)
              ·
                refine ⟨6148574063625032511331187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4099049375750021674220791 6148574063625032511331187)
                ·
                  refine ⟨9222861095437548766996781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6148574063625032511331187 9222861095437548766996781)
                  ·
                    refine ⟨3458572910789080787623793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9222861095437548766996781 3458572910789080787623793)
                    ·
                      refine ⟨2593929683091810590717845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3458572910789080787623793 2593929683091810590717845)
                      ·
                        rfl

theorem cell23_5051660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_5051660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051660 prefixEnd_5051660 := by exact prefixLift 5051660
  have htrace : WordTrace (prefixWord ++ tailWord_5051660) baseStart_5051660 baseEnd_5051660 := by
    simpa [prefixWord, tailWord_5051660, baseEnd_5051660] using wordTrace_append hprefix tailTrace_5051660
  have hstable : (prefixWord ++ tailWord_5051660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051660).length < 2 ^ (prefixWord ++ tailWord_5051660).sum := by decide
  have hdescent : baseEnd_5051660 < baseStart_5051660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051690 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_5051690 : Nat := 118140960795 + 5051690 * 2 ^ 59
def prefixEnd_5051690 : Nat := 4983230072969 + 3 ^ 40 * 5051690 * 2
def baseEnd_5051690 : Nat := 2593945087511445473342707

theorem tailTrace_5051690 : CollatzResearch.WordTrace tailWord_5051690 prefixEnd_5051690 2593945087511445473342707 := by
  unfold tailWord_5051690
  simp only [CollatzResearch.WordTrace]
  refine ⟨46062567767149341202320131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122833514045731576539520349 46062567767149341202320131)
  ·
    refine ⟨69093851650724011803480197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46062567767149341202320131 69093851650724011803480197)
    ·
      refine ⟨12955097184510752213152537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69093851650724011803480197 12955097184510752213152537)
      ·
        refine ⟨9716322888383064159864403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12955097184510752213152537 9716322888383064159864403)
        ·
          refine ⟨14574484332574596239796605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9716322888383064159864403 14574484332574596239796605)
          ·
            refine ⟨5465431624715473589923727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14574484332574596239796605 5465431624715473589923727)
            ·
              refine ⟨8198147437073210384885591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5465431624715473589923727 8198147437073210384885591)
              ·
                refine ⟨12297221155609815577328387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8198147437073210384885591 12297221155609815577328387)
                ·
                  refine ⟨18445831733414723365992581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12297221155609815577328387 18445831733414723365992581)
                  ·
                    refine ⟨3458593450015260631123609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18445831733414723365992581 3458593450015260631123609)
                    ·
                      refine ⟨2593945087511445473342707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3458593450015260631123609 2593945087511445473342707)
                      ·
                        rfl

theorem cell23_5051690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_5051690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051690 prefixEnd_5051690 := by exact prefixLift 5051690
  have htrace : WordTrace (prefixWord ++ tailWord_5051690) baseStart_5051690 baseEnd_5051690 := by
    simpa [prefixWord, tailWord_5051690, baseEnd_5051690] using wordTrace_append hprefix tailTrace_5051690
  have hstable : (prefixWord ++ tailWord_5051690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051690).length < 2 ^ (prefixWord ++ tailWord_5051690).sum := by decide
  have hdescent : baseEnd_5051690 < baseStart_5051690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051713 : List Nat := [1, 2, 5, 2, 1, 1, 3, 3, 5]
def baseStart_5051713 : Nat := 118140960795 + 5051713 * 2 ^ 59
def prefixEnd_5051713 : Nat := 4983230072969 + 3 ^ 40 * 5051713 * 2
def baseEnd_5051713 : Nat := 288217433062944320372789

theorem tailTrace_5051713 : CollatzResearch.WordTrace tailWord_5051713 prefixEnd_5051713 288217433062944320372789 := by
  unfold tailWord_5051713
  simp only [CollatzResearch.WordTrace]
  refine ⟨184251109947514039737367793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122834073298342693158245195 184251109947514039737367793)
  ·
    refine ⟨138188332460635529803025845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184251109947514039737367793 138188332460635529803025845)
    ·
      refine ⟨12955156168184580919033673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138188332460635529803025845 12955156168184580919033673)
      ·
        refine ⟨9716367126138435689275255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12955156168184580919033673 9716367126138435689275255)
        ·
          refine ⟨14574550689207653533912883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9716367126138435689275255 14574550689207653533912883)
          ·
            refine ⟨21861826033811480300869325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14574550689207653533912883 21861826033811480300869325)
            ·
              refine ⟨8198184762679305112825997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21861826033811480300869325 8198184762679305112825997)
              ·
                refine ⟨3074319286004739417309749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8198184762679305112825997 3074319286004739417309749)
                ·
                  refine ⟨288217433062944320372789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3074319286004739417309749 288217433062944320372789)
                  ·
                    rfl

theorem cell23_5051713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 5].length) (baseStart_5051713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051713 prefixEnd_5051713 := by exact prefixLift 5051713
  have htrace : WordTrace (prefixWord ++ tailWord_5051713) baseStart_5051713 baseEnd_5051713 := by
    simpa [prefixWord, tailWord_5051713, baseEnd_5051713] using wordTrace_append hprefix tailTrace_5051713
  have hstable : (prefixWord ++ tailWord_5051713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051713).length < 2 ^ (prefixWord ++ tailWord_5051713).sum := by decide
  have hdescent : baseEnd_5051713 < baseStart_5051713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051746 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_5051746 : Nat := 118140960795 + 5051746 * 2 ^ 59
def prefixEnd_5051746 : Nat := 4983230072969 + 3 ^ 40 * 5051746 * 2
def baseEnd_5051746 : Nat := 2593973842428097254242449

theorem tailTrace_5051746 : CollatzResearch.WordTrace tailWord_5051746 prefixEnd_5051746 2593973842428097254242449 := by
  unfold tailWord_5051746
  simp only [CollatzResearch.WordTrace]
  refine ⟨46063078389098621593329773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122834875704262990915546061 46063078389098621593329773)
  ·
    refine ⟨17273654395911983097498665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46063078389098621593329773 17273654395911983097498665)
    ·
      refine ⟨12955240796933987323123999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17273654395911983097498665 12955240796933987323123999)
      ·
        refine ⟨19432861195400980984685999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12955240796933987323123999 19432861195400980984685999)
        ·
          refine ⟨29149291793101471477028999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19432861195400980984685999 29149291793101471477028999)
          ·
            refine ⟨43723937689652207215543499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29149291793101471477028999 43723937689652207215543499)
            ·
              refine ⟨65585906534478310823315249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43723937689652207215543499 65585906534478310823315249)
              ·
                refine ⟨49189429900858733117486437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65585906534478310823315249 49189429900858733117486437)
                ·
                  refine ⟨9223018106411012459528707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49189429900858733117486437 9223018106411012459528707)
                  ·
                    refine ⟨13834527159616518689293061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9223018106411012459528707 13834527159616518689293061)
                    ·
                      refine ⟨2593973842428097254242449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13834527159616518689293061 2593973842428097254242449)
                      ·
                        rfl

theorem cell23_5051746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_5051746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051746 prefixEnd_5051746 := by exact prefixLift 5051746
  have htrace : WordTrace (prefixWord ++ tailWord_5051746) baseStart_5051746 baseEnd_5051746 := by
    simpa [prefixWord, tailWord_5051746, baseEnd_5051746] using wordTrace_append hprefix tailTrace_5051746
  have hstable : (prefixWord ++ tailWord_5051746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051746).length < 2 ^ (prefixWord ++ tailWord_5051746).sum := by decide
  have hdescent : baseEnd_5051746 < baseStart_5051746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051773 : List Nat := [1, 4, 1, 1, 2, 2, 2, 5, 1, 4]
def baseStart_5051773 : Nat := 118140960795 + 5051773 * 2 ^ 59
def prefixEnd_5051773 : Nat := 4983230072969 + 3 ^ 40 * 5051773 * 2
def baseEnd_5051773 : Nat := 864662568801922882868275

theorem tailTrace_5051773 : CollatzResearch.WordTrace tailWord_5051773 prefixEnd_5051773 864662568801922882868275 := by
  unfold tailWord_5051773
  simp only [CollatzResearch.WordTrace]
  refine ⟨184253298327296669984551973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122835532218197779989701315 184253298327296669984551973)
  ·
    refine ⟨34547493436368125622103495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184253298327296669984551973 34547493436368125622103495)
    ·
      refine ⟨51821240154552188433155243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34547493436368125622103495 51821240154552188433155243)
      ·
        refine ⟨77731860231828282649732865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51821240154552188433155243 77731860231828282649732865)
        ·
          refine ⟨58298895173871211987299649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77731860231828282649732865 58298895173871211987299649)
          ·
            refine ⟨43724171380403408990474737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58298895173871211987299649 43724171380403408990474737)
            ·
              refine ⟨32793128535302556742856053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43724171380403408990474737 32793128535302556742856053)
              ·
                refine ⟨3074355800184614694642755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32793128535302556742856053 3074355800184614694642755)
                ·
                  refine ⟨4611533700276922041964133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3074355800184614694642755 4611533700276922041964133)
                  ·
                    refine ⟨864662568801922882868275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4611533700276922041964133 864662568801922882868275)
                    ·
                      rfl

theorem cell23_5051773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_5051773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051773 prefixEnd_5051773 := by exact prefixLift 5051773
  have htrace : WordTrace (prefixWord ++ tailWord_5051773) baseStart_5051773 baseEnd_5051773 := by
    simpa [prefixWord, tailWord_5051773, baseEnd_5051773] using wordTrace_append hprefix tailTrace_5051773
  have hstable : (prefixWord ++ tailWord_5051773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051773).length < 2 ^ (prefixWord ++ tailWord_5051773).sum := by decide
  have hdescent : baseEnd_5051773 < baseStart_5051773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051833 : List Nat := [1, 2, 1, 4, 4, 1, 1, 3, 1, 5]
def baseStart_5051833 : Nat := 118140960795 + 5051833 * 2 ^ 59
def prefixEnd_5051833 : Nat := 4983230072969 + 3 ^ 40 * 5051833 * 2
def baseEnd_5051833 : Nat := 864672838415012804618183

theorem tailTrace_5051833 : CollatzResearch.WordTrace tailWord_5051833 prefixEnd_5051833 864672838415012804618183 := by
  unfold tailWord_5051833
  simp only [CollatzResearch.WordTrace]
  refine ⟨184255486707079300231736153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122836991138052866821157435 184255486707079300231736153)
  ·
    refine ⟨138191615030309475173802115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184255486707079300231736153 138191615030309475173802115)
    ·
      refine ⟨207287422545464212760703173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138191615030309475173802115 207287422545464212760703173)
      ·
        refine ⟨38866391727274539892631845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207287422545464212760703173 38866391727274539892631845)
        ·
          refine ⟨7287448448863976229868471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38866391727274539892631845 7287448448863976229868471)
          ·
            refine ⟨10931172673295964344802707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7287448448863976229868471 10931172673295964344802707)
            ·
              refine ⟨16396759009943946517204061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10931172673295964344802707 16396759009943946517204061)
              ·
                refine ⟨6148784628728979943951523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16396759009943946517204061 6148784628728979943951523)
                ·
                  refine ⟨9223176943093469915927285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6148784628728979943951523 9223176943093469915927285)
                  ·
                    refine ⟨864672838415012804618183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9223176943093469915927285 864672838415012804618183)
                    ·
                      rfl

theorem cell23_5051833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 5].length) (baseStart_5051833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051833 prefixEnd_5051833 := by exact prefixLift 5051833
  have htrace : WordTrace (prefixWord ++ tailWord_5051833) baseStart_5051833 baseEnd_5051833 := by
    simpa [prefixWord, tailWord_5051833, baseEnd_5051833] using wordTrace_append hprefix tailTrace_5051833
  have hstable : (prefixWord ++ tailWord_5051833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051833).length < 2 ^ (prefixWord ++ tailWord_5051833).sum := by decide
  have hdescent : baseEnd_5051833 < baseStart_5051833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051839 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 5]
def baseStart_5051839 : Nat := 118140960795 + 5051839 * 2 ^ 59
def prefixEnd_5051839 : Nat := 4983230072969 + 3 ^ 40 * 5051839 * 2
def baseEnd_5051839 : Nat := 2594021596128965390379521

theorem tailTrace_5051839 : CollatzResearch.WordTrace tailWord_5051839 prefixEnd_5051839 2594021596128965390379521 := by
  unfold tailWord_5051839
  simp only [CollatzResearch.WordTrace]
  refine ⟨184255705545057563256454571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122837137030038375504303047 184255705545057563256454571)
  ·
    refine ⟨276383558317586344884681857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184255705545057563256454571 276383558317586344884681857)
    ·
      refine ⟨207287668738189758663511393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276383558317586344884681857 207287668738189758663511393)
      ·
        refine ⟨155465751553642318997633545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207287668738189758663511393 155465751553642318997633545)
        ·
          refine ⟨116599313665231739248225159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155465751553642318997633545 116599313665231739248225159)
          ·
            refine ⟨174898970497847608872337739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116599313665231739248225159 174898970497847608872337739)
            ·
              refine ⟨262348455746771413308506609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174898970497847608872337739 262348455746771413308506609)
              ·
                refine ⟨196761341810078559981379957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262348455746771413308506609 196761341810078559981379957)
                ·
                  refine ⟨18446375794694864998254371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 196761341810078559981379957 18446375794694864998254371)
                  ·
                    refine ⟨27669563692042297497381557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18446375794694864998254371 27669563692042297497381557)
                    ·
                      refine ⟨2594021596128965390379521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27669563692042297497381557 2594021596128965390379521)
                      ·
                        rfl

theorem cell23_5051839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_5051839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051839 prefixEnd_5051839 := by exact prefixLift 5051839
  have htrace : WordTrace (prefixWord ++ tailWord_5051839) baseStart_5051839 baseEnd_5051839 := by
    simpa [prefixWord, tailWord_5051839, baseEnd_5051839] using wordTrace_append hprefix tailTrace_5051839
  have hstable : (prefixWord ++ tailWord_5051839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051839).length < 2 ^ (prefixWord ++ tailWord_5051839).sum := by decide
  have hdescent : baseEnd_5051839 < baseStart_5051839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051849 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 1, 1, 6]
def baseStart_5051849 : Nat := 118140960795 + 5051849 * 2 ^ 59
def prefixEnd_5051849 : Nat := 4983230072969 + 3 ^ 40 * 5051849 * 2
def baseEnd_5051849 : Nat := 2594026730935510351254475

theorem tailTrace_5051849 : CollatzResearch.WordTrace tailWord_5051849 prefixEnd_5051849 2594026730935510351254475 := by
  unfold tailWord_5051849
  simp only [CollatzResearch.WordTrace]
  refine ⟨184256070275021334964318601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122837380183347556642879067 184256070275021334964318601)
  ·
    refine ⟨138192052706266001223238951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184256070275021334964318601 138192052706266001223238951)
    ·
      refine ⟨207288079059399001834858427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138192052706266001223238951 207288079059399001834858427)
      ·
        refine ⟨310932118589098502752287641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207288079059399001834858427 310932118589098502752287641)
        ·
          refine ⟨233199088941823877064215731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310932118589098502752287641 233199088941823877064215731)
          ·
            refine ⟨349798633412735815596323597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233199088941823877064215731 349798633412735815596323597)
            ·
              refine ⟨131174487529775930848621349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 349798633412735815596323597 131174487529775930848621349)
              ·
                refine ⟨24595216411832987034116503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131174487529775930848621349 24595216411832987034116503)
                ·
                  refine ⟨36892824617749480551174755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24595216411832987034116503 36892824617749480551174755)
                  ·
                    refine ⟨55339236926624220826762133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36892824617749480551174755 55339236926624220826762133)
                    ·
                      refine ⟨2594026730935510351254475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55339236926624220826762133 2594026730935510351254475)
                      ·
                        rfl

theorem cell23_5051849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_5051849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051849 prefixEnd_5051849 := by exact prefixLift 5051849
  have htrace : WordTrace (prefixWord ++ tailWord_5051849) baseStart_5051849 baseEnd_5051849 := by
    simpa [prefixWord, tailWord_5051849, baseEnd_5051849] using wordTrace_append hprefix tailTrace_5051849
  have hstable : (prefixWord ++ tailWord_5051849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051849).length < 2 ^ (prefixWord ++ tailWord_5051849).sum := by decide
  have hdescent : baseEnd_5051849 < baseStart_5051849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051866 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6]
def baseStart_5051866 : Nat := 118140960795 + 5051866 * 2 ^ 59
def prefixEnd_5051866 : Nat := 4983230072969 + 3 ^ 40 * 5051866 * 2
def baseEnd_5051866 : Nat := 2594035460106636784741897

theorem tailTrace_5051866 : CollatzResearch.WordTrace tailWord_5051866 prefixEnd_5051866 2594035460106636784741897 := by
  unfold tailWord_5051866
  simp only [CollatzResearch.WordTrace]
  refine ⟨46064172578989936716921863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122837793543973164578458301 46064172578989936716921863)
  ·
    refine ⟨69096258868484905075382795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46064172578989936716921863 69096258868484905075382795)
    ·
      refine ⟨103644388302727357613074193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69096258868484905075382795 103644388302727357613074193)
      ·
        refine ⟨77733291227045518209805645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103644388302727357613074193 77733291227045518209805645)
        ·
          refine ⟨29149984210142069328677117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77733291227045518209805645 29149984210142069328677117)
          ·
            refine ⟨10931244078803275998253919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29149984210142069328677117 10931244078803275998253919)
            ·
              refine ⟨16396866118204913997380879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10931244078803275998253919 16396866118204913997380879)
              ·
                refine ⟨24595299177307370996071319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16396866118204913997380879 24595299177307370996071319)
                ·
                  refine ⟨36892948765961056494106979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24595299177307370996071319 36892948765961056494106979)
                  ·
                    refine ⟨55339423148941584741160469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36892948765961056494106979 55339423148941584741160469)
                    ·
                      refine ⟨2594035460106636784741897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55339423148941584741160469 2594035460106636784741897)
                      ·
                        rfl

theorem cell23_5051866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_5051866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051866 prefixEnd_5051866 := by exact prefixLift 5051866
  have htrace : WordTrace (prefixWord ++ tailWord_5051866) baseStart_5051866 baseEnd_5051866 := by
    simpa [prefixWord, tailWord_5051866, baseEnd_5051866] using wordTrace_append hprefix tailTrace_5051866
  have hstable : (prefixWord ++ tailWord_5051866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051866).length < 2 ^ (prefixWord ++ tailWord_5051866).sum := by decide
  have hdescent : baseEnd_5051866 < baseStart_5051866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051873 : List Nat := [1, 2, 3, 1, 2, 3, 1, 4, 1, 2, 3]
def baseStart_5051873 : Nat := 118140960795 + 5051873 * 2 ^ 59
def prefixEnd_5051873 : Nat := 4983230072969 + 3 ^ 40 * 5051873 * 2
def baseEnd_5051873 : Nat := 2594039054471218257354365

theorem tailTrace_5051873 : CollatzResearch.WordTrace tailWord_5051873 prefixEnd_5051873 2594039054471218257354365 := by
  unfold tailWord_5051873
  simp only [CollatzResearch.WordTrace]
  refine ⟨184256945626934387063192273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122837963751289591375461515 184256945626934387063192273)
  ·
    refine ⟨138192709220200790297394205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184256945626934387063192273 138192709220200790297394205)
    ·
      refine ⟨51822265957575296361522827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138192709220200790297394205 51822265957575296361522827)
      ·
        refine ⟨77733398936362944542284241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51822265957575296361522827 77733398936362944542284241)
        ·
          refine ⟨58300049202272208406713181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77733398936362944542284241 58300049202272208406713181)
          ·
            refine ⟨21862518450852078152517443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58300049202272208406713181 21862518450852078152517443)
            ·
              refine ⟨32793777676278117228776165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21862518450852078152517443 32793777676278117228776165)
              ·
                refine ⟨6148833314302146980395531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32793777676278117228776165 6148833314302146980395531)
                ·
                  refine ⟨9223249971453220470593297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6148833314302146980395531 9223249971453220470593297)
                  ·
                    refine ⟨6917437478589915352944973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9223249971453220470593297 6917437478589915352944973)
                    ·
                      refine ⟨2594039054471218257354365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6917437478589915352944973 2594039054471218257354365)
                      ·
                        rfl

theorem cell23_5051873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_5051873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051873 prefixEnd_5051873 := by exact prefixLift 5051873
  have htrace : WordTrace (prefixWord ++ tailWord_5051873) baseStart_5051873 baseEnd_5051873 := by
    simpa [prefixWord, tailWord_5051873, baseEnd_5051873] using wordTrace_append hprefix tailTrace_5051873
  have hstable : (prefixWord ++ tailWord_5051873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051873).length < 2 ^ (prefixWord ++ tailWord_5051873).sum := by decide
  have hdescent : baseEnd_5051873 < baseStart_5051873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051887 : List Nat := [1, 1, 2, 1, 4, 1, 5, 3, 1, 2, 2]
def baseStart_5051887 : Nat := 118140960795 + 5051887 * 2 ^ 59
def prefixEnd_5051887 : Nat := 4983230072969 + 3 ^ 40 * 5051887 * 2
def baseEnd_5051887 : Nat := 2594046243200381202579301

theorem tailTrace_5051887 : CollatzResearch.WordTrace tailWord_5051887 prefixEnd_5051887 2594046243200381202579301 := by
  unfold tailWord_5051887
  simp only [CollatzResearch.WordTrace]
  refine ⟨184257456248883667454201915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122838304165922444969467943 184257456248883667454201915)
  ·
    refine ⟨276386184373325501181302873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184257456248883667454201915 276386184373325501181302873)
    ·
      refine ⟨207289638279994125885977155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276386184373325501181302873 207289638279994125885977155)
      ·
        refine ⟨310934457419991188828965733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207289638279994125885977155 310934457419991188828965733)
        ·
          refine ⟨58300210766248347905431075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 310934457419991188828965733 58300210766248347905431075)
          ·
            refine ⟨87450316149372521858146613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58300210766248347905431075 87450316149372521858146613)
            ·
              refine ⟨8198467139003673924201245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87450316149372521858146613 8198467139003673924201245)
              ·
                refine ⟨3074425177126377721575467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8198467139003673924201245 3074425177126377721575467)
                ·
                  refine ⟨4611637765689566582363201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3074425177126377721575467 4611637765689566582363201)
                  ·
                    refine ⟨3458728324267174936772401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4611637765689566582363201 3458728324267174936772401)
                    ·
                      refine ⟨2594046243200381202579301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3458728324267174936772401 2594046243200381202579301)
                      ·
                        rfl

theorem cell23_5051887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 1, 2, 2].length) (baseStart_5051887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051887 prefixEnd_5051887 := by exact prefixLift 5051887
  have htrace : WordTrace (prefixWord ++ tailWord_5051887) baseStart_5051887 baseEnd_5051887 := by
    simpa [prefixWord, tailWord_5051887, baseEnd_5051887] using wordTrace_append hprefix tailTrace_5051887
  have hstable : (prefixWord ++ tailWord_5051887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051887).length < 2 ^ (prefixWord ++ tailWord_5051887).sum := by decide
  have hdescent : baseEnd_5051887 < baseStart_5051887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051890 : List Nat := [3, 2, 1, 4, 1, 1, 2, 3, 1, 2, 3]
def baseStart_5051890 : Nat := 118140960795 + 5051890 * 2 ^ 59
def prefixEnd_5051890 : Nat := 4983230072969 + 3 ^ 40 * 5051890 * 2
def baseEnd_5051890 : Nat := 2594047783642344690841787

theorem tailTrace_5051890 : CollatzResearch.WordTrace tailWord_5051890 prefixEnd_5051890 2594047783642344690841787 := by
  unfold tailWord_5051890
  simp only [CollatzResearch.WordTrace]
  refine ⟨46064391416968199741640281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122838377111915199311040749 46064391416968199741640281)
  ·
    refine ⟨34548293562726149806230211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46064391416968199741640281 34548293562726149806230211)
    ·
      refine ⟨51822440344089224709345317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34548293562726149806230211 51822440344089224709345317)
      ·
        refine ⟨9716707564516729633002247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51822440344089224709345317 9716707564516729633002247)
        ·
          refine ⟨14575061346775094449503371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9716707564516729633002247 14575061346775094449503371)
          ·
            refine ⟨21862592020162641674255057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14575061346775094449503371 21862592020162641674255057)
            ·
              refine ⟨16396944015121981255691293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21862592020162641674255057 16396944015121981255691293)
              ·
                refine ⟨6148854005670742970884235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16396944015121981255691293 6148854005670742970884235)
                ·
                  refine ⟨9223281008506114456326353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6148854005670742970884235 9223281008506114456326353)
                  ·
                    refine ⟨6917460756379585842244765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9223281008506114456326353 6917460756379585842244765)
                    ·
                      refine ⟨2594047783642344690841787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6917460756379585842244765 2594047783642344690841787)
                      ·
                        rfl

theorem cell23_5051890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_5051890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051890 prefixEnd_5051890 := by exact prefixLift 5051890
  have htrace : WordTrace (prefixWord ++ tailWord_5051890) baseStart_5051890 baseEnd_5051890 := by
    simpa [prefixWord, tailWord_5051890, baseEnd_5051890] using wordTrace_append hprefix tailTrace_5051890
  have hstable : (prefixWord ++ tailWord_5051890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051890).length < 2 ^ (prefixWord ++ tailWord_5051890).sum := by decide
  have hdescent : baseEnd_5051890 < baseStart_5051890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051893 : List Nat := [1, 3, 5, 1, 1, 3, 9]
def baseStart_5051893 : Nat := 118140960795 + 5051893 * 2 ^ 59
def prefixEnd_5051893 : Nat := 4983230072969 + 3 ^ 40 * 5051893 * 2
def baseEnd_5051893 : Nat := 32025300297337138013633

theorem tailTrace_5051893 : CollatzResearch.WordTrace tailWord_5051893 prefixEnd_5051893 32025300297337138013633 := by
  unfold tailWord_5051893
  simp only [CollatzResearch.WordTrace]
  refine ⟨184257675086861930478920333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122838450057907953652613555 184257675086861930478920333)
  ·
    refine ⟨69096628157573223929595125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184257675086861930478920333 69096628157573223929595125)
    ·
      refine ⟨6477808889772489743399543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69096628157573223929595125 6477808889772489743399543)
      ·
        refine ⟨9716713334658734615099315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6477808889772489743399543 9716713334658734615099315)
        ·
          refine ⟨14575070001988101922648973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9716713334658734615099315 14575070001988101922648973)
          ·
            refine ⟨5465651250745538220993365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14575070001988101922648973 5465651250745538220993365)
            ·
              refine ⟨32025300297337138013633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5465651250745538220993365 32025300297337138013633)
              ·
                rfl

theorem cell23_5051893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 9].length) (baseStart_5051893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051893 prefixEnd_5051893 := by exact prefixLift 5051893
  have htrace : WordTrace (prefixWord ++ tailWord_5051893) baseStart_5051893 baseEnd_5051893 := by
    simpa [prefixWord, tailWord_5051893, baseEnd_5051893] using wordTrace_append hprefix tailTrace_5051893
  have hstable : (prefixWord ++ tailWord_5051893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051893).length < 2 ^ (prefixWord ++ tailWord_5051893).sum := by decide
  have hdescent : baseEnd_5051893 < baseStart_5051893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051913 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 3, 3, 2]
def baseStart_5051913 : Nat := 118140960795 + 5051913 * 2 ^ 59
def prefixEnd_5051913 : Nat := 4983230072969 + 3 ^ 40 * 5051913 * 2
def baseEnd_5051913 : Nat := 2594059593697398100854181

theorem tailTrace_5051913 : CollatzResearch.WordTrace tailWord_5051913 prefixEnd_5051913 2594059593697398100854181 := by
  unfold tailWord_5051913
  simp only [CollatzResearch.WordTrace]
  refine ⟨184258404546789473894648393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122838936364526315929765595 184258404546789473894648393)
  ·
    refine ⟨138193803410092105420986295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184258404546789473894648393 138193803410092105420986295)
    ·
      refine ⟨207290705115138158131479443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138193803410092105420986295 207290705115138158131479443)
      ·
        refine ⟨310936057672707237197219165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207290705115138158131479443 310936057672707237197219165)
        ·
          refine ⟨116601021627265213948957187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310936057672707237197219165 116601021627265213948957187)
          ·
            refine ⟨174901532440897820923435781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116601021627265213948957187 174901532440897820923435781)
            ·
              refine ⟨32794037332668341423144209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174901532440897820923435781 32794037332668341423144209)
              ·
                refine ⟨24595527999501256067358157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32794037332668341423144209 24595527999501256067358157)
                ·
                  refine ⟨9223322999812971025259309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24595527999501256067358157 9223322999812971025259309)
                  ·
                    refine ⟨3458746124929864134472241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9223322999812971025259309 3458746124929864134472241)
                    ·
                      refine ⟨2594059593697398100854181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3458746124929864134472241 2594059593697398100854181)
                      ·
                        rfl

theorem cell23_5051913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 3, 2].length) (baseStart_5051913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051913 prefixEnd_5051913 := by exact prefixLift 5051913
  have htrace : WordTrace (prefixWord ++ tailWord_5051913) baseStart_5051913 baseEnd_5051913 := by
    simpa [prefixWord, tailWord_5051913, baseEnd_5051913] using wordTrace_append hprefix tailTrace_5051913
  have hstable : (prefixWord ++ tailWord_5051913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051913).length < 2 ^ (prefixWord ++ tailWord_5051913).sum := by decide
  have hdescent : baseEnd_5051913 < baseStart_5051913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051924 : List Nat := [2, 4, 3, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_5051924 : Nat := 118140960795 + 5051924 * 2 ^ 59
def prefixEnd_5051924 : Nat := 4983230072969 + 3 ^ 40 * 5051924 * 2
def baseEnd_5051924 : Nat := 2594065241984597557816631

theorem tailTrace_5051924 : CollatzResearch.WordTrace tailWord_5051924 prefixEnd_5051924 2594065241984597557816631 := by
  unfold tailWord_5051924
  simp only [CollatzResearch.WordTrace]
  refine ⟨92129402874874811386649413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122839203833166415182199217 92129402874874811386649413)
  ·
    refine ⟨17274263039039027134996765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92129402874874811386649413 17274263039039027134996765)
    ·
      refine ⟨6477848639639635175623787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17274263039039027134996765 6477848639639635175623787)
      ·
        refine ⟨9716772959459452763435681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6477848639639635175623787 9716772959459452763435681)
        ·
          refine ⟨7287579719594589572576761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9716772959459452763435681 7287579719594589572576761)
          ·
            refine ⟨5465684789695942179432571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7287579719594589572576761 5465684789695942179432571)
            ·
              refine ⟨8198527184543913269148857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5465684789695942179432571 8198527184543913269148857)
              ·
                refine ⟨6148895388407934951861643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8198527184543913269148857 6148895388407934951861643)
                ·
                  refine ⟨9223343082611902427792465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6148895388407934951861643 9223343082611902427792465)
                  ·
                    refine ⟨6917507311958926820844349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9223343082611902427792465 6917507311958926820844349)
                    ·
                      refine ⟨2594065241984597557816631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6917507311958926820844349 2594065241984597557816631)
                      ·
                        rfl

theorem cell23_5051924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_5051924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051924 prefixEnd_5051924 := by exact prefixLift 5051924
  have htrace : WordTrace (prefixWord ++ tailWord_5051924) baseStart_5051924 baseEnd_5051924 := by
    simpa [prefixWord, tailWord_5051924, baseEnd_5051924] using wordTrace_append hprefix tailTrace_5051924
  have hstable : (prefixWord ++ tailWord_5051924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051924).length < 2 ^ (prefixWord ++ tailWord_5051924).sum := by decide
  have hdescent : baseEnd_5051924 < baseStart_5051924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5051934 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_5051934 : Nat := 118140960795 + 5051934 * 2 ^ 59
def prefixEnd_5051934 : Nat := 4983230072969 + 3 ^ 40 * 5051934 * 2
def baseEnd_5051934 : Nat := 2594070376791142518691585

theorem tailTrace_5051934 : CollatzResearch.WordTrace tailWord_5051934 prefixEnd_5051934 2594070376791142518691585 := by
  unfold tailWord_5051934
  simp only [CollatzResearch.WordTrace]
  refine ⟨23032396309964174310145357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122839446986475596320775237 23032396309964174310145357)
  ·
    refine ⟨8637148616236565366304509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23032396309964174310145357 8637148616236565366304509)
    ·
      refine ⟨3238930731088712012364191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8637148616236565366304509 3238930731088712012364191)
      ·
        refine ⟨4858396096633068018546287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3238930731088712012364191 4858396096633068018546287)
        ·
          refine ⟨7287594144949602027819431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4858396096633068018546287 7287594144949602027819431)
          ·
            refine ⟨10931391217424403041729147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7287594144949602027819431 10931391217424403041729147)
            ·
              refine ⟨16397086826136604562593721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10931391217424403041729147 16397086826136604562593721)
              ·
                refine ⟨12297815119602453421945291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16397086826136604562593721 12297815119602453421945291)
                ·
                  refine ⟨18446722679403680132917937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12297815119602453421945291 18446722679403680132917937)
                  ·
                    refine ⟨13835042009552760099688453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18446722679403680132917937 13835042009552760099688453)
                    ·
                      refine ⟨2594070376791142518691585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13835042009552760099688453 2594070376791142518691585)
                      ·
                        rfl

theorem cell23_5051934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_5051934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5051934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5051934 prefixEnd_5051934 := by exact prefixLift 5051934
  have htrace : WordTrace (prefixWord ++ tailWord_5051934) baseStart_5051934 baseEnd_5051934 := by
    simpa [prefixWord, tailWord_5051934, baseEnd_5051934] using wordTrace_append hprefix tailTrace_5051934
  have hstable : (prefixWord ++ tailWord_5051934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5051934).length < 2 ^ (prefixWord ++ tailWord_5051934).sum := by decide
  have hdescent : baseEnd_5051934 < baseStart_5051934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5051934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052033 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_5052033 : Nat := 118140960795 + 5052033 * 2 ^ 59
def prefixEnd_5052033 : Nat := 4983230072969 + 3 ^ 40 * 5052033 * 2
def baseEnd_5052033 : Nat := 2594121211375937631353629

theorem tailTrace_5052033 : CollatzResearch.WordTrace tailWord_5052033 prefixEnd_5052033 2594121211375937631353629 := by
  unfold tailWord_5052033
  simp only [CollatzResearch.WordTrace]
  refine ⟨184262781306354734389016753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122841854204236489592677835 184262781306354734389016753)
  ·
    refine ⟨138197085979766050791762565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184262781306354734389016753 138197085979766050791762565)
    ·
      refine ⟨25911953621206134523455481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138197085979766050791762565 25911953621206134523455481)
      ·
        refine ⟨19433965215904600892591611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25911953621206134523455481 19433965215904600892591611)
        ·
          refine ⟨29150947823856901338887417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19433965215904600892591611 29150947823856901338887417)
          ·
            refine ⟨21863210867892676004165563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29150947823856901338887417 21863210867892676004165563)
            ·
              refine ⟨32794816301839014006248345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21863210867892676004165563 32794816301839014006248345)
              ·
                refine ⟨24596112226379260504686259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32794816301839014006248345 24596112226379260504686259)
                ·
                  refine ⟨36894168339568890757029389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24596112226379260504686259 36894168339568890757029389)
                  ·
                    refine ⟨13835313127338334033886021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36894168339568890757029389 13835313127338334033886021)
                    ·
                      refine ⟨2594121211375937631353629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13835313127338334033886021 2594121211375937631353629)
                      ·
                        rfl

theorem cell23_5052033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_5052033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052033 prefixEnd_5052033 := by exact prefixLift 5052033
  have htrace : WordTrace (prefixWord ++ tailWord_5052033) baseStart_5052033 baseEnd_5052033 := by
    simpa [prefixWord, tailWord_5052033, baseEnd_5052033] using wordTrace_append hprefix tailTrace_5052033
  have hstable : (prefixWord ++ tailWord_5052033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052033).length < 2 ^ (prefixWord ++ tailWord_5052033).sum := by decide
  have hdescent : baseEnd_5052033 < baseStart_5052033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052043 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 3, 4]
def baseStart_5052043 : Nat := 118140960795 + 5052043 * 2 ^ 59
def prefixEnd_5052043 : Nat := 4983230072969 + 3 ^ 40 * 5052043 * 2
def baseEnd_5052043 : Nat := 864708782060827530742861

theorem tailTrace_5052043 : CollatzResearch.WordTrace tailWord_5052043 prefixEnd_5052043 864708782060827530742861 := by
  unfold tailWord_5052043
  simp only [CollatzResearch.WordTrace]
  refine ⟨184263146036318506096880783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122842097357545670731253855 184263146036318506096880783)
  ·
    refine ⟨276394719054477759145321175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184263146036318506096880783 276394719054477759145321175)
    ·
      refine ⟨414592078581716638717981763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276394719054477759145321175 414592078581716638717981763)
      ·
        refine ⟨621888117872574958076972645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414592078581716638717981763 621888117872574958076972645)
        ·
          refine ⟨116604022101107804639432371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 621888117872574958076972645 116604022101107804639432371)
          ·
            refine ⟨174906033151661706959148557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116604022101107804639432371 174906033151661706959148557)
            ·
              refine ⟨65589762431873140109680709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174906033151661706959148557 65589762431873140109680709)
              ·
                refine ⟨12298080455976213770565133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65589762431873140109680709 12298080455976213770565133)
                ·
                  refine ⟨4611780170991080163961925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12298080455976213770565133 4611780170991080163961925)
                  ·
                    refine ⟨864708782060827530742861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4611780170991080163961925 864708782060827530742861)
                    ·
                      rfl

theorem cell23_5052043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 4].length) (baseStart_5052043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052043 prefixEnd_5052043 := by exact prefixLift 5052043
  have htrace : WordTrace (prefixWord ++ tailWord_5052043) baseStart_5052043 baseEnd_5052043 := by
    simpa [prefixWord, tailWord_5052043, baseEnd_5052043] using wordTrace_append hprefix tailTrace_5052043
  have hstable : (prefixWord ++ tailWord_5052043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052043).length < 2 ^ (prefixWord ++ tailWord_5052043).sum := by decide
  have hdescent : baseEnd_5052043 < baseStart_5052043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052053 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 6, 2, 3]
def baseStart_5052053 : Nat := 118140960795 + 5052053 * 2 ^ 59
def prefixEnd_5052053 : Nat := 4983230072969 + 3 ^ 40 * 5052053 * 2
def baseEnd_5052053 : Nat := 2594131480989027553103537

theorem tailTrace_5052053 : CollatzResearch.WordTrace tailWord_5052053 prefixEnd_5052053 2594131480989027553103537 := by
  unfold tailWord_5052053
  simp only [CollatzResearch.WordTrace]
  refine ⟨184263510766282277804744813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122842340510854851869829875 184263510766282277804744813)
  ·
    refine ⟨69098816537355854176779305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184263510766282277804744813 69098816537355854176779305)
    ·
      refine ⟨51824112403016890632584479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69098816537355854176779305 51824112403016890632584479)
      ·
        refine ⟨77736168604525335948876719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51824112403016890632584479 77736168604525335948876719)
        ·
          refine ⟨116604252906788003923315079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77736168604525335948876719 116604252906788003923315079)
          ·
            refine ⟨174906379360182005884972619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116604252906788003923315079 174906379360182005884972619)
            ·
              refine ⟨262359569040273008827458929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174906379360182005884972619 262359569040273008827458929)
              ·
                refine ⟨196769676780204756620594197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262359569040273008827458929 196769676780204756620594197)
                ·
                  refine ⟨9223578599072097966590353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 196769676780204756620594197 9223578599072097966590353)
                  ·
                    refine ⟨6917683949304073474942765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9223578599072097966590353 6917683949304073474942765)
                    ·
                      refine ⟨2594131480989027553103537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6917683949304073474942765 2594131480989027553103537)
                      ·
                        rfl

theorem cell23_5052053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_5052053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052053 prefixEnd_5052053 := by exact prefixLift 5052053
  have htrace : WordTrace (prefixWord ++ tailWord_5052053) baseStart_5052053 baseEnd_5052053 := by
    simpa [prefixWord, tailWord_5052053, baseEnd_5052053] using wordTrace_append hprefix tailTrace_5052053
  have hstable : (prefixWord ++ tailWord_5052053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052053).length < 2 ^ (prefixWord ++ tailWord_5052053).sum := by decide
  have hdescent : baseEnd_5052053 < baseStart_5052053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052090 : List Nat := [3, 1, 1, 1, 2, 4, 4, 1, 6]
def baseStart_5052090 : Nat := 118140960795 + 5052090 * 2 ^ 59
def prefixEnd_5052090 : Nat := 4983230072969 + 3 ^ 40 * 5052090 * 2
def baseEnd_5052090 : Nat := 288238942197027100926763

theorem tailTrace_5052090 : CollatzResearch.WordTrace tailWord_5052090 prefixEnd_5052090 288238942197027100926763 := by
  unfold tailWord_5052090
  simp only [CollatzResearch.WordTrace]
  refine ⟨46066215066787058280960431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122843240178098822082561149 46066215066787058280960431)
  ·
    refine ⟨69099322600180587421440647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46066215066787058280960431 69099322600180587421440647)
    ·
      refine ⟨103648983900270881132160971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69099322600180587421440647 103648983900270881132160971)
      ·
        refine ⟨155473475850406321698241457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103648983900270881132160971 155473475850406321698241457)
        ·
          refine ⟨116605106887804741273681093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155473475850406321698241457 116605106887804741273681093)
          ·
            refine ⟨21863457541463388988815205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116605106887804741273681093 21863457541463388988815205)
            ·
              refine ⟨4099398289024385435402851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21863457541463388988815205 4099398289024385435402851)
              ·
                refine ⟨6149097433536578153104277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4099398289024385435402851 6149097433536578153104277)
                ·
                  refine ⟨288238942197027100926763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6149097433536578153104277 288238942197027100926763)
                  ·
                    rfl

theorem cell23_5052090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 6].length) (baseStart_5052090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052090 prefixEnd_5052090 := by exact prefixLift 5052090
  have htrace : WordTrace (prefixWord ++ tailWord_5052090) baseStart_5052090 baseEnd_5052090 := by
    simpa [prefixWord, tailWord_5052090, baseEnd_5052090] using wordTrace_append hprefix tailTrace_5052090
  have hstable : (prefixWord ++ tailWord_5052090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052090).length < 2 ^ (prefixWord ++ tailWord_5052090).sum := by decide
  have hdescent : baseEnd_5052090 < baseStart_5052090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052103 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 3, 5]
def baseStart_5052103 : Nat := 118140960795 + 5052103 * 2 ^ 59
def prefixEnd_5052103 : Nat := 4983230072969 + 3 ^ 40 * 5052103 * 2
def baseEnd_5052103 : Nat := 864719051673917452492769

theorem tailTrace_5052103 : CollatzResearch.WordTrace tailWord_5052103 prefixEnd_5052103 864719051673917452492769 := by
  unfold tailWord_5052103
  simp only [CollatzResearch.WordTrace]
  refine ⟨184265334416101136344064963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122843556277400757562709975 184265334416101136344064963)
  ·
    refine ⟨276398001624151704516097445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184265334416101136344064963 276398001624151704516097445)
    ·
      refine ⟨51824625304528444596768271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276398001624151704516097445 51824625304528444596768271)
      ·
        refine ⟨77736937956792666895152407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51824625304528444596768271 77736937956792666895152407)
        ·
          refine ⟨116605406935189000342728611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77736937956792666895152407 116605406935189000342728611)
          ·
            refine ⟨174908110402783500514092917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116605406935189000342728611 174908110402783500514092917)
            ·
              refine ⟨16397635350260953173196211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 174908110402783500514092917 16397635350260953173196211)
              ·
                refine ⟨24596453025391429759794317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16397635350260953173196211 24596453025391429759794317)
                ·
                  refine ⟨9223669884521786159922869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24596453025391429759794317 9223669884521786159922869)
                  ·
                    refine ⟨864719051673917452492769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9223669884521786159922869 864719051673917452492769)
                    ·
                      rfl

theorem cell23_5052103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_5052103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052103 prefixEnd_5052103 := by exact prefixLift 5052103
  have htrace : WordTrace (prefixWord ++ tailWord_5052103) baseStart_5052103 baseEnd_5052103 := by
    simpa [prefixWord, tailWord_5052103, baseEnd_5052103] using wordTrace_append hprefix tailTrace_5052103
  have hstable : (prefixWord ++ tailWord_5052103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052103).length < 2 ^ (prefixWord ++ tailWord_5052103).sum := by decide
  have hdescent : baseEnd_5052103 < baseStart_5052103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052133 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 3, 6]
def baseStart_5052133 : Nat := 118140960795 + 5052133 * 2 ^ 59
def prefixEnd_5052133 : Nat := 4983230072969 + 3 ^ 40 * 5052133 * 2
def baseEnd_5052133 : Nat := 864724186480462413367723

theorem tailTrace_5052133 : CollatzResearch.WordTrace tailWord_5052133 prefixEnd_5052133 864724186480462413367723 := by
  unfold tailWord_5052133
  simp only [CollatzResearch.WordTrace]
  refine ⟨184266428605992451467657053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122844285737328300978438035 184266428605992451467657053)
  ·
    refine ⟨69099910727247169300371395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184266428605992451467657053 69099910727247169300371395)
    ·
      refine ⟨103649866090870753950557093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69099910727247169300371395 103649866090870753950557093)
      ·
        refine ⟨19434349892038266365729455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103649866090870753950557093 19434349892038266365729455)
        ·
          refine ⟨29151524838057399548594183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19434349892038266365729455 29151524838057399548594183)
          ·
            refine ⟨43727287257086099322891275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29151524838057399548594183 43727287257086099322891275)
            ·
              refine ⟨65590930885629148984336913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43727287257086099322891275 65590930885629148984336913)
              ·
                refine ⟨49193198164221861738252685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65590930885629148984336913 49193198164221861738252685)
                ·
                  refine ⟨18447449311583198151844757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49193198164221861738252685 18447449311583198151844757)
                  ·
                    refine ⟨864724186480462413367723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18447449311583198151844757 864724186480462413367723)
                    ·
                      rfl

theorem cell23_5052133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_5052133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052133 prefixEnd_5052133 := by exact prefixLift 5052133
  have htrace : WordTrace (prefixWord ++ tailWord_5052133) baseStart_5052133 baseEnd_5052133 := by
    simpa [prefixWord, tailWord_5052133, baseEnd_5052133] using wordTrace_append hprefix tailTrace_5052133
  have hstable : (prefixWord ++ tailWord_5052133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052133).length < 2 ^ (prefixWord ++ tailWord_5052133).sum := by decide
  have hdescent : baseEnd_5052133 < baseStart_5052133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052143 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 5]
def baseStart_5052143 : Nat := 118140960795 + 5052143 * 2 ^ 59
def prefixEnd_5052143 : Nat := 4983230072969 + 3 ^ 40 * 5052143 * 2
def baseEnd_5052143 : Nat := 2594177694247932200978123

theorem tailTrace_5052143 : CollatzResearch.WordTrace tailWord_5052143 prefixEnd_5052143 2594177694247932200978123 := by
  unfold tailWord_5052143
  simp only [CollatzResearch.WordTrace]
  refine ⟨184266793335956223175521083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122844528890637482117014055 184266793335956223175521083)
  ·
    refine ⟨276400190003934334763281625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184266793335956223175521083 276400190003934334763281625)
    ·
      refine ⟨207300142502950751072461219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276400190003934334763281625 207300142502950751072461219)
      ·
        refine ⟨310950213754426126608691829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207300142502950751072461219 310950213754426126608691829)
        ·
          refine ⟨29151582539477449369564859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 310950213754426126608691829 29151582539477449369564859)
          ·
            refine ⟨43727373809216174054347289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29151582539477449369564859 43727373809216174054347289)
            ·
              refine ⟨32795530356912130540760467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43727373809216174054347289 32795530356912130540760467)
              ·
                refine ⟨49193295535368195811140701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32795530356912130540760467 49193295535368195811140701)
                ·
                  refine ⟨18447485825763073429177763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49193295535368195811140701 18447485825763073429177763)
                  ·
                    refine ⟨27671228738644610143766645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18447485825763073429177763 27671228738644610143766645)
                    ·
                      refine ⟨2594177694247932200978123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27671228738644610143766645 2594177694247932200978123)
                      ·
                        rfl

theorem cell23_5052143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_5052143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052143 prefixEnd_5052143 := by exact prefixLift 5052143
  have htrace : WordTrace (prefixWord ++ tailWord_5052143) baseStart_5052143 baseEnd_5052143 := by
    simpa [prefixWord, tailWord_5052143, baseEnd_5052143] using wordTrace_append hprefix tailTrace_5052143
  have hstable : (prefixWord ++ tailWord_5052143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052143).length < 2 ^ (prefixWord ++ tailWord_5052143).sum := by decide
  have hdescent : baseEnd_5052143 < baseStart_5052143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052150 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_5052150 : Nat := 118140960795 + 5052150 * 2 ^ 59
def prefixEnd_5052150 : Nat := 4983230072969 + 3 ^ 40 * 5052150 * 2
def baseEnd_5052150 : Nat := 864727096204171224530197

theorem tailTrace_5052150 : CollatzResearch.WordTrace tailWord_5052150 prefixEnd_5052150 864727096204171224530197 := by
  unfold tailWord_5052150
  simp only [CollatzResearch.WordTrace]
  refine ⟨11516690540433178960689119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122844699097953908914017269 11516690540433178960689119)
  ·
    refine ⟨17275035810649768441033679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11516690540433178960689119 17275035810649768441033679)
    ·
      refine ⟨25912553715974652661550519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17275035810649768441033679 25912553715974652661550519)
      ·
        refine ⟨38868830573961978992325779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25912553715974652661550519 38868830573961978992325779)
        ·
          refine ⟨58303245860942968488488669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38868830573961978992325779 58303245860942968488488669)
          ·
            refine ⟨21863717197853613183183251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58303245860942968488488669 21863717197853613183183251)
            ·
              refine ⟨32795575796780419774774877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21863717197853613183183251 32795575796780419774774877)
              ·
                refine ⟨12298340923792657415540579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32795575796780419774774877 12298340923792657415540579)
                ·
                  refine ⟨18447511385688986123310869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12298340923792657415540579 18447511385688986123310869)
                  ·
                    refine ⟨864727096204171224530197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18447511385688986123310869 864727096204171224530197)
                    ·
                      rfl

theorem cell23_5052150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_5052150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052150 prefixEnd_5052150 := by exact prefixLift 5052150
  have htrace : WordTrace (prefixWord ++ tailWord_5052150) baseStart_5052150 baseEnd_5052150 := by
    simpa [prefixWord, tailWord_5052150, baseEnd_5052150] using wordTrace_append hprefix tailTrace_5052150
  have hstable : (prefixWord ++ tailWord_5052150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052150).length < 2 ^ (prefixWord ++ tailWord_5052150).sum := by decide
  have hdescent : baseEnd_5052150 < baseStart_5052150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052170 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_5052170 : Nat := 118140960795 + 5052170 * 2 ^ 59
def prefixEnd_5052170 : Nat := 4983230072969 + 3 ^ 40 * 5052170 * 2
def baseEnd_5052170 : Nat := 2594191558225603595340499

theorem tailTrace_5052170 : CollatzResearch.WordTrace tailWord_5052170 prefixEnd_5052170 2594191558225603595340499 := by
  unfold tailWord_5052170
  simp only [CollatzResearch.WordTrace]
  refine ⟨46066944526714601696688491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122845185404572271191169309 46066944526714601696688491)
  ·
    refine ⟨69100416790071902545032737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46066944526714601696688491 69100416790071902545032737)
    ·
      refine ⟨51825312592553926908774553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69100416790071902545032737 51825312592553926908774553)
      ·
        refine ⟨38868984444415445181580915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51825312592553926908774553 38868984444415445181580915)
        ·
          refine ⟨58303476666623167772371373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38868984444415445181580915 58303476666623167772371373)
          ·
            refine ⟨21863803749983687914639265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58303476666623167772371373 21863803749983687914639265)
            ·
              refine ⟨16397852812487765935979449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21863803749983687914639265 16397852812487765935979449)
              ·
                refine ⟨12298389609365824451984587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16397852812487765935979449 12298389609365824451984587)
                ·
                  refine ⟨18447584414048736677976881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12298389609365824451984587 18447584414048736677976881)
                  ·
                    refine ⟨13835688310536552508482661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18447584414048736677976881 13835688310536552508482661)
                    ·
                      refine ⟨2594191558225603595340499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13835688310536552508482661 2594191558225603595340499)
                      ·
                        rfl

theorem cell23_5052170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_5052170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052170 prefixEnd_5052170 := by exact prefixLift 5052170
  have htrace : WordTrace (prefixWord ++ tailWord_5052170) baseStart_5052170 baseEnd_5052170 := by
    simpa [prefixWord, tailWord_5052170, baseEnd_5052170] using wordTrace_append hprefix tailTrace_5052170
  have hstable : (prefixWord ++ tailWord_5052170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052170).length < 2 ^ (prefixWord ++ tailWord_5052170).sum := by decide
  have hdescent : baseEnd_5052170 < baseStart_5052170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052214 : List Nat := [5, 1, 2, 2, 1, 3, 2, 7]
def baseStart_5052214 : Nat := 118140960795 + 5052214 * 2 ^ 59
def prefixEnd_5052214 : Nat := 4983230072969 + 3 ^ 40 * 5052214 * 2
def baseEnd_5052214 : Nat := 96082005606459311970011

theorem tailTrace_5052214 : CollatzResearch.WordTrace tailWord_5052214 prefixEnd_5052214 96082005606459311970011 := by
  unfold tailWord_5052214
  simp only [CollatzResearch.WordTrace]
  refine ⟨11516836432418687643834731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122846255279132668200903797 11516836432418687643834731)
  ·
    refine ⟨17275254648628031465752097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11516836432418687643834731 17275254648628031465752097)
    ·
      refine ⟨12956440986471023599314073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17275254648628031465752097 12956440986471023599314073)
      ·
        refine ⟨9717330739853267699485555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12956440986471023599314073 9717330739853267699485555)
        ·
          refine ⟨14575996109779901549228333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9717330739853267699485555 14575996109779901549228333)
          ·
            refine ⟨5465998541167463080960625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14575996109779901549228333 5465998541167463080960625)
            ·
              refine ⟨4099498905875597310720469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5465998541167463080960625 4099498905875597310720469)
              ·
                refine ⟨96082005606459311970011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4099498905875597310720469 96082005606459311970011)
                ·
                  rfl

theorem cell23_5052214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_5052214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052214 prefixEnd_5052214 := by exact prefixLift 5052214
  have htrace : WordTrace (prefixWord ++ tailWord_5052214) baseStart_5052214 baseEnd_5052214 := by
    simpa [prefixWord, tailWord_5052214, baseEnd_5052214] using wordTrace_append hprefix tailTrace_5052214
  have hstable : (prefixWord ++ tailWord_5052214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052214).length < 2 ^ (prefixWord ++ tailWord_5052214).sum := by decide
  have hdescent : baseEnd_5052214 < baseStart_5052214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052250 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3]
def baseStart_5052250 : Nat := 118140960795 + 5052250 * 2 ^ 59
def prefixEnd_5052250 : Nat := 4983230072969 + 3 ^ 40 * 5052250 * 2
def baseEnd_5052250 : Nat := 2594232636677963282340131

theorem tailTrace_5052250 : CollatzResearch.WordTrace tailWord_5052250 prefixEnd_5052250 2594232636677963282340131 := by
  unfold tailWord_5052250
  simp only [CollatzResearch.WordTrace]
  refine ⟨46067673986642145112416551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122847130631045720299777469 46067673986642145112416551)
  ·
    refine ⟨69101510979963217668624827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46067673986642145112416551 69101510979963217668624827)
    ·
      refine ⟨103652266469944826502937241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69101510979963217668624827 103652266469944826502937241)
      ·
        refine ⟨77739199852458619877202931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103652266469944826502937241 77739199852458619877202931)
        ·
          refine ⟨116608799778687929815804397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77739199852458619877202931 116608799778687929815804397)
          ·
            refine ⟨43728299917007973680926649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116608799778687929815804397 43728299917007973680926649)
            ·
              refine ⟨32796224937755980260694987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43728299917007973680926649 32796224937755980260694987)
              ·
                refine ⟨49194337406633970391042481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32796224937755980260694987 49194337406633970391042481)
                ·
                  refine ⟨36895753054975477793281861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49194337406633970391042481 36895753054975477793281861)
                  ·
                    refine ⟨6917953697807902086240349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36895753054975477793281861 6917953697807902086240349)
                    ·
                      refine ⟨2594232636677963282340131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6917953697807902086240349 2594232636677963282340131)
                      ·
                        rfl

theorem cell23_5052250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_5052250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052250 prefixEnd_5052250 := by exact prefixLift 5052250
  have htrace : WordTrace (prefixWord ++ tailWord_5052250) baseStart_5052250 baseEnd_5052250 := by
    simpa [prefixWord, tailWord_5052250, baseEnd_5052250] using wordTrace_append hprefix tailTrace_5052250
  have hstable : (prefixWord ++ tailWord_5052250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052250).length < 2 ^ (prefixWord ++ tailWord_5052250).sum := by decide
  have hdescent : baseEnd_5052250 < baseStart_5052250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052258 : List Nat := [3, 3, 2, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_5052258 : Nat := 118140960795 + 5052258 * 2 ^ 59
def prefixEnd_5052258 : Nat := 4983230072969 + 3 ^ 40 * 5052258 * 2
def baseEnd_5052258 : Nat := 2594236744523199251040095

theorem tailTrace_5052258 : CollatzResearch.WordTrace tailWord_5052258 prefixEnd_5052258 2594236744523199251040095 := by
  unfold tailWord_5052258
  simp only [CollatzResearch.WordTrace]
  refine ⟨46067746932634899453989357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122847325153693065210638285 46067746932634899453989357)
  ·
    refine ⟨17275405099738087295246009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46067746932634899453989357 17275405099738087295246009)
    ·
      refine ⟨12956553824803565471434507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17275405099738087295246009 12956553824803565471434507)
      ·
        refine ⟨19434830737205348207151761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12956553824803565471434507 19434830737205348207151761)
        ·
          refine ⟨14576123052904011155363821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19434830737205348207151761 14576123052904011155363821)
          ·
            refine ⟨5466046144839004183261433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14576123052904011155363821 5466046144839004183261433)
            ·
              refine ⟨4099534608629253137446075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5466046144839004183261433 4099534608629253137446075)
              ·
                refine ⟨6149301912943879706169113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4099534608629253137446075 6149301912943879706169113)
                ·
                  refine ⟨4611976434707909779626835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6149301912943879706169113 4611976434707909779626835)
                  ·
                    refine ⟨6917964652061864669440253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4611976434707909779626835 6917964652061864669440253)
                    ·
                      refine ⟨2594236744523199251040095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6917964652061864669440253 2594236744523199251040095)
                      ·
                        rfl

theorem cell23_5052258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_5052258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052258 prefixEnd_5052258 := by exact prefixLift 5052258
  have htrace : WordTrace (prefixWord ++ tailWord_5052258) baseStart_5052258 baseEnd_5052258 := by
    simpa [prefixWord, tailWord_5052258, baseEnd_5052258] using wordTrace_append hprefix tailTrace_5052258
  have hstable : (prefixWord ++ tailWord_5052258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052258).length < 2 ^ (prefixWord ++ tailWord_5052258).sum := by decide
  have hdescent : baseEnd_5052258 < baseStart_5052258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052298 : List Nat := [3, 1, 2, 4, 2, 1, 2, 2, 2, 2, 2]
def baseStart_5052298 : Nat := 118140960795 + 5052298 * 2 ^ 59
def prefixEnd_5052298 : Nat := 4983230072969 + 3 ^ 40 * 5052298 * 2
def baseEnd_5052298 : Nat := 2594257283749379094539911

theorem tailTrace_5052298 : CollatzResearch.WordTrace tailWord_5052298 prefixEnd_5052298 2594257283749379094539911 := by
  unfold tailWord_5052298
  simp only [CollatzResearch.WordTrace]
  refine ⟨46068111662598671161853387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122848297766929789764942365 46068111662598671161853387)
  ·
    refine ⟨69102167493898006742780081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46068111662598671161853387 69102167493898006742780081)
    ·
      refine ⟨51826625620423505057085061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69102167493898006742780081 51826625620423505057085061)
      ·
        refine ⟨9717492303829407198203449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51826625620423505057085061 9717492303829407198203449)
        ·
          refine ⟨7288119227872055398652587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9717492303829407198203449 7288119227872055398652587)
          ·
            refine ⟨10932178841808083097978881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7288119227872055398652587 10932178841808083097978881)
            ·
              refine ⟨8199134131356062323484161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10932178841808083097978881 8199134131356062323484161)
              ·
                refine ⟨6149350598517046742613121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8199134131356062323484161 6149350598517046742613121)
                ·
                  refine ⟨4612012948887785056959841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6149350598517046742613121 4612012948887785056959841)
                  ·
                    refine ⟨3459009711665838792719881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4612012948887785056959841 3459009711665838792719881)
                    ·
                      refine ⟨2594257283749379094539911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3459009711665838792719881 2594257283749379094539911)
                      ·
                        rfl

theorem cell23_5052298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_5052298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052298 prefixEnd_5052298 := by exact prefixLift 5052298
  have htrace : WordTrace (prefixWord ++ tailWord_5052298) baseStart_5052298 baseEnd_5052298 := by
    simpa [prefixWord, tailWord_5052298, baseEnd_5052298] using wordTrace_append hprefix tailTrace_5052298
  have hstable : (prefixWord ++ tailWord_5052298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052298).length < 2 ^ (prefixWord ++ tailWord_5052298).sum := by decide
  have hdescent : baseEnd_5052298 < baseStart_5052298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052320 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 4]
def baseStart_5052320 : Nat := 118140960795 + 5052320 * 2 ^ 59
def prefixEnd_5052320 : Nat := 4983230072969 + 3 ^ 40 * 5052320 * 2
def baseEnd_5052320 : Nat := 2594268580323778008464809

theorem tailTrace_5052320 : CollatzResearch.WordTrace tailWord_5052320 prefixEnd_5052320 2594268580323778008464809 := by
  unfold tailWord_5052320
  simp only [CollatzResearch.WordTrace]
  refine ⟨92136624528157491202357207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122848832704209988269809609 92136624528157491202357207)
  ·
    refine ⟨138204936792236236803535811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92136624528157491202357207 138204936792236236803535811)
    ·
      refine ⟨207307405188354355205303717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138204936792236236803535811 207307405188354355205303717)
      ·
        refine ⟨38870138472816441600994447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207307405188354355205303717 38870138472816441600994447)
        ·
          refine ⟨58305207709224662401491671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38870138472816441600994447 58305207709224662401491671)
          ·
            refine ⟨87457811563836993602237507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58305207709224662401491671 87457811563836993602237507)
            ·
              refine ⟨131186717345755490403356261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87457811563836993602237507 131186717345755490403356261)
              ·
                refine ⟨24597509502329154450629299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131186717345755490403356261 24597509502329154450629299)
                ·
                  refine ⟨36896264253493731675943949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24597509502329154450629299 36896264253493731675943949)
                  ·
                    refine ⟨13836099095060149378478981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36896264253493731675943949 13836099095060149378478981)
                    ·
                      refine ⟨2594268580323778008464809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13836099095060149378478981 2594268580323778008464809)
                      ·
                        rfl

theorem cell23_5052320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_5052320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052320 prefixEnd_5052320 := by exact prefixLift 5052320
  have htrace : WordTrace (prefixWord ++ tailWord_5052320) baseStart_5052320 baseEnd_5052320 := by
    simpa [prefixWord, tailWord_5052320, baseEnd_5052320] using wordTrace_append hprefix tailTrace_5052320
  have hstable : (prefixWord ++ tailWord_5052320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052320).length < 2 ^ (prefixWord ++ tailWord_5052320).sum := by decide
  have hdescent : baseEnd_5052320 < baseStart_5052320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052337 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 1, 3, 4]
def baseStart_5052337 : Nat := 118140960795 + 5052337 * 2 ^ 59
def prefixEnd_5052337 : Nat := 4983230072969 + 3 ^ 40 * 5052337 * 2
def baseEnd_5052337 : Nat := 2594277309494904441952231

theorem tailTrace_5052337 : CollatzResearch.WordTrace tailWord_5052337 prefixEnd_5052337 2594277309494904441952231 := by
  unfold tailWord_5052337
  simp only [CollatzResearch.WordTrace]
  refine ⟨184273869097253394308083265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122849246064835596205388843 184273869097253394308083265)
  ·
    refine ⟨138205401822940045731062449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184273869097253394308083265 138205401822940045731062449)
    ·
      refine ⟨103654051367205034298296837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138205401822940045731062449 103654051367205034298296837)
      ·
        refine ⟨19435134631350943930930657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103654051367205034298296837 19435134631350943930930657)
        ·
          refine ⟨14576350973513207948197993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19435134631350943930930657 14576350973513207948197993)
          ·
            refine ⟨10932263230134905961148495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14576350973513207948197993 10932263230134905961148495)
            ·
              refine ⟨16398394845202358941722743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10932263230134905961148495 16398394845202358941722743)
              ·
                refine ⟨24597592267803538412584115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16398394845202358941722743 24597592267803538412584115)
                ·
                  refine ⟨36896388401705307618876173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24597592267803538412584115 36896388401705307618876173)
                  ·
                    refine ⟨13836145650639490357078565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36896388401705307618876173 13836145650639490357078565)
                    ·
                      refine ⟨2594277309494904441952231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13836145650639490357078565 2594277309494904441952231)
                      ·
                        rfl

theorem cell23_5052337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_5052337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052337 prefixEnd_5052337 := by exact prefixLift 5052337
  have htrace : WordTrace (prefixWord ++ tailWord_5052337) baseStart_5052337 baseEnd_5052337 := by
    simpa [prefixWord, tailWord_5052337, baseEnd_5052337] using wordTrace_append hprefix tailTrace_5052337
  have hstable : (prefixWord ++ tailWord_5052337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052337).length < 2 ^ (prefixWord ++ tailWord_5052337).sum := by decide
  have hdescent : baseEnd_5052337 < baseStart_5052337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052364 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 3, 4]
def baseStart_5052364 : Nat := 118140960795 + 5052364 * 2 ^ 59
def prefixEnd_5052364 : Nat := 4983230072969 + 3 ^ 40 * 5052364 * 2
def baseEnd_5052364 : Nat := 864763724490858612104869

theorem tailTrace_5052364 : CollatzResearch.WordTrace tailWord_5052364 prefixEnd_5052364 864763724490858612104869 := by
  unfold tailWord_5052364
  simp only [CollatzResearch.WordTrace]
  refine ⟨92137426934077788959658073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122849902578770385279544097 92137426934077788959658073)
  ·
    refine ⟨69103070200558341719743555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92137426934077788959658073 69103070200558341719743555)
    ·
      refine ⟨103654605300837512579615333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69103070200558341719743555 103654605300837512579615333)
      ·
        refine ⟨19435238493907033608677875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103654605300837512579615333 19435238493907033608677875)
        ·
          refine ⟨29152857740860550413016813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19435238493907033608677875 29152857740860550413016813)
          ·
            refine ⟨10932321652822706404881305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29152857740860550413016813 10932321652822706404881305)
            ·
              refine ⟨8199241239617029803660979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10932321652822706404881305 8199241239617029803660979)
              ·
                refine ⟨12298861859425544705491469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8199241239617029803660979 12298861859425544705491469)
                ·
                  refine ⟨4612073197284579264559301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12298861859425544705491469 4612073197284579264559301)
                  ·
                    refine ⟨864763724490858612104869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4612073197284579264559301 864763724490858612104869)
                    ·
                      rfl

theorem cell23_5052364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_5052364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052364 prefixEnd_5052364 := by exact prefixLift 5052364
  have htrace : WordTrace (prefixWord ++ tailWord_5052364) baseStart_5052364 baseEnd_5052364 := by
    simpa [prefixWord, tailWord_5052364, baseEnd_5052364] using wordTrace_append hprefix tailTrace_5052364
  have hstable : (prefixWord ++ tailWord_5052364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052364).length < 2 ^ (prefixWord ++ tailWord_5052364).sum := by decide
  have hdescent : baseEnd_5052364 < baseStart_5052364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052398 : List Nat := [4, 1, 2, 1, 3, 3, 1, 3, 1, 4]
def baseStart_5052398 : Nat := 118140960795 + 5052398 * 2 ^ 59
def prefixEnd_5052398 : Nat := 4983230072969 + 3 ^ 40 * 5052398 * 2
def baseEnd_5052398 : Nat := 864769543938276234429817

theorem tailTrace_5052398 : CollatzResearch.WordTrace tailWord_5052398 prefixEnd_5052398 864769543938276234429817 := by
  unfold tailWord_5052398
  simp only [CollatzResearch.WordTrace]
  refine ⟨23034511743754050215756731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122850729300021601150702565 23034511743754050215756731)
  ·
    refine ⟨34551767615631075323635097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23034511743754050215756731 34551767615631075323635097)
    ·
      refine ⟨25913825711723306492726323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34551767615631075323635097 25913825711723306492726323)
      ·
        refine ⟨38870738567584959739089485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25913825711723306492726323 38870738567584959739089485)
        ·
          refine ⟨14576526962844359902158557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38870738567584959739089485 14576526962844359902158557)
          ·
            refine ⟨5466197611066634963309459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14576526962844359902158557 5466197611066634963309459)
            ·
              refine ⟨8199296416599952444964189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5466197611066634963309459 8199296416599952444964189)
              ·
                refine ⟨3074736156224982166861571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8199296416599952444964189 3074736156224982166861571)
                ·
                  refine ⟨4612104234337473250292357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3074736156224982166861571 4612104234337473250292357)
                  ·
                    refine ⟨864769543938276234429817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4612104234337473250292357 864769543938276234429817)
                    ·
                      rfl

theorem cell23_5052398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_5052398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052398 prefixEnd_5052398 := by exact prefixLift 5052398
  have htrace : WordTrace (prefixWord ++ tailWord_5052398) baseStart_5052398 baseEnd_5052398 := by
    simpa [prefixWord, tailWord_5052398, baseEnd_5052398] using wordTrace_append hprefix tailTrace_5052398
  have hstable : (prefixWord ++ tailWord_5052398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052398).length < 2 ^ (prefixWord ++ tailWord_5052398).sum := by decide
  have hdescent : baseEnd_5052398 < baseStart_5052398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052421 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 3, 1, 3]
def baseStart_5052421 : Nat := 118140960795 + 5052421 * 2 ^ 59
def prefixEnd_5052421 : Nat := 4983230072969 + 3 ^ 40 * 5052421 * 2
def baseEnd_5052421 : Nat := 2594320441869882113301845

theorem tailTrace_5052421 : CollatzResearch.WordTrace tailWord_5052421 prefixEnd_5052421 2594320441869882113301845 := by
  unfold tailWord_5052421
  simp only [CollatzResearch.WordTrace]
  refine ⟨184276932828949076654141117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122851288552632717769427411 184276932828949076654141117)
  ·
    refine ⟨69103849810855903745302919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184276932828949076654141117 69103849810855903745302919)
    ·
      refine ⟨103655774716283855617954379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69103849810855903745302919 103655774716283855617954379)
      ·
        refine ⟨155483662074425783426931569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103655774716283855617954379 155483662074425783426931569)
        ·
          refine ⟨116612746555819337570198677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155483662074425783426931569 116612746555819337570198677)
          ·
            refine ⟨5466222494804031448603063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116612746555819337570198677 5466222494804031448603063)
            ·
              refine ⟨8199333742206047172904595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5466222494804031448603063 8199333742206047172904595)
              ·
                refine ⟨12299000613309070759356893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8199333742206047172904595 12299000613309070759356893)
                ·
                  refine ⟨4612125229990901534758835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12299000613309070759356893 4612125229990901534758835)
                  ·
                    refine ⟨6918187844986352302138253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4612125229990901534758835 6918187844986352302138253)
                    ·
                      refine ⟨2594320441869882113301845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6918187844986352302138253 2594320441869882113301845)
                      ·
                        rfl

theorem cell23_5052421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_5052421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052421 prefixEnd_5052421 := by exact prefixLift 5052421
  have htrace : WordTrace (prefixWord ++ tailWord_5052421) baseStart_5052421 baseEnd_5052421 := by
    simpa [prefixWord, tailWord_5052421, baseEnd_5052421] using wordTrace_append hprefix tailTrace_5052421
  have hstable : (prefixWord ++ tailWord_5052421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052421).length < 2 ^ (prefixWord ++ tailWord_5052421).sum := by decide
  have hdescent : baseEnd_5052421 < baseStart_5052421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052427 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 4]
def baseStart_5052427 : Nat := 118140960795 + 5052427 * 2 ^ 59
def prefixEnd_5052427 : Nat := 4983230072969 + 3 ^ 40 * 5052427 * 2
def baseEnd_5052427 : Nat := 2594323522753809089826817

theorem tailTrace_5052427 : CollatzResearch.WordTrace tailWord_5052427 prefixEnd_5052427 2594323522753809089826817 := by
  unfold tailWord_5052427
  simp only [CollatzResearch.WordTrace]
  refine ⟨184277151666927339678859535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122851434444618226452573023 184277151666927339678859535)
  ·
    refine ⟨276415727500391009518289303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184277151666927339678859535 276415727500391009518289303)
    ·
      refine ⟨414623591250586514277433955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276415727500391009518289303 414623591250586514277433955)
      ·
        refine ⟨621935386875879771416150933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414623591250586514277433955 621935386875879771416150933)
        ·
          refine ⟨29153221259806864285132075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 621935386875879771416150933 29153221259806864285132075)
          ·
            refine ⟨43729831889710296427698113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29153221259806864285132075 43729831889710296427698113)
            ·
              refine ⟨32797373917282722320773585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43729831889710296427698113 32797373917282722320773585)
              ·
                refine ⟨24598030437962041740580189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32797373917282722320773585 24598030437962041740580189)
                ·
                  refine ⟨9224261414235765652717571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24598030437962041740580189 9224261414235765652717571)
                  ·
                    refine ⟨13836392121353648479076357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9224261414235765652717571 13836392121353648479076357)
                    ·
                      refine ⟨2594323522753809089826817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13836392121353648479076357 2594323522753809089826817)
                      ·
                        rfl

theorem cell23_5052427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 4].length) (baseStart_5052427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052427 prefixEnd_5052427 := by exact prefixLift 5052427
  have htrace : WordTrace (prefixWord ++ tailWord_5052427) baseStart_5052427 baseEnd_5052427 := by
    simpa [prefixWord, tailWord_5052427, baseEnd_5052427] using wordTrace_append hprefix tailTrace_5052427
  have hstable : (prefixWord ++ tailWord_5052427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052427).length < 2 ^ (prefixWord ++ tailWord_5052427).sum := by decide
  have hdescent : baseEnd_5052427 < baseStart_5052427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052444 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_5052444 : Nat := 118140960795 + 5052444 * 2 ^ 59
def prefixEnd_5052444 : Nat := 4983230072969 + 3 ^ 40 * 5052444 * 2
def baseEnd_5052444 : Nat := 2594332251924935523314239

theorem tailTrace_5052444 : CollatzResearch.WordTrace tailWord_5052444 prefixEnd_5052444 2594332251924935523314239 := by
  unfold tailWord_5052444
  simp only [CollatzResearch.WordTrace]
  refine ⟨92138885853932875791114193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122851847805243834388152257 92138885853932875791114193)
  ·
    refine ⟨69104164390449656843335645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92138885853932875791114193 69104164390449656843335645)
    ·
      refine ⟨25914061646418621316250867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69104164390449656843335645 25914061646418621316250867)
      ·
        refine ⟨38871092469627931974376301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25914061646418621316250867 38871092469627931974376301)
        ·
          refine ⟨14576659676110474490391113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38871092469627931974376301 14576659676110474490391113)
          ·
            refine ⟨10932494757082855867793335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14576659676110474490391113 10932494757082855867793335)
            ·
              refine ⟨16398742135624283801690003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10932494757082855867793335 16398742135624283801690003)
              ·
                refine ⟨24598113203436425702535005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16398742135624283801690003 24598113203436425702535005)
                ·
                  refine ⟨9224292451288659638450627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24598113203436425702535005 9224292451288659638450627)
                  ·
                    refine ⟨13836438676932989457675941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9224292451288659638450627 13836438676932989457675941)
                    ·
                      refine ⟨2594332251924935523314239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13836438676932989457675941 2594332251924935523314239)
                      ·
                        rfl

theorem cell23_5052444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_5052444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052444 prefixEnd_5052444 := by exact prefixLift 5052444
  have htrace : WordTrace (prefixWord ++ tailWord_5052444) baseStart_5052444 baseEnd_5052444 := by
    simpa [prefixWord, tailWord_5052444, baseEnd_5052444] using wordTrace_append hprefix tailTrace_5052444
  have hstable : (prefixWord ++ tailWord_5052444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052444).length < 2 ^ (prefixWord ++ tailWord_5052444).sum := by decide
  have hdescent : baseEnd_5052444 < baseStart_5052444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052464 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 5]
def baseStart_5052464 : Nat := 118140960795 + 5052464 * 2 ^ 59
def prefixEnd_5052464 : Nat := 4983230072969 + 3 ^ 40 * 5052464 * 2
def baseEnd_5052464 : Nat := 2594342521538025445064147

theorem tailTrace_5052464 : CollatzResearch.WordTrace tailWord_5052464 prefixEnd_5052464 2594342521538025445064147 := by
  unfold tailWord_5052464
  simp only [CollatzResearch.WordTrace]
  refine ⟨92139250583896647498978223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122852334111862196665304297 92139250583896647498978223)
  ·
    refine ⟨138208875875844971248467335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92139250583896647498978223 138208875875844971248467335)
    ·
      refine ⟨207313313813767456872701003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138208875875844971248467335 207313313813767456872701003)
      ·
        refine ⟨310969970720651185309051505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207313313813767456872701003 310969970720651185309051505)
        ·
          refine ⟨233227478040488388981788629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310969970720651185309051505 233227478040488388981788629)
          ·
            refine ⟨5466269016573946616760671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 233227478040488388981788629 5466269016573946616760671)
            ·
              refine ⟨8199403524860919925141007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5466269016573946616760671 8199403524860919925141007)
              ·
                refine ⟨12299105287291379887711511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8199403524860919925141007 12299105287291379887711511)
                ·
                  refine ⟨18448657930937069831567267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12299105287291379887711511 18448657930937069831567267)
                  ·
                    refine ⟨27672986896405604747350901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18448657930937069831567267 27672986896405604747350901)
                    ·
                      refine ⟨2594342521538025445064147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27672986896405604747350901 2594342521538025445064147)
                      ·
                        rfl

theorem cell23_5052464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 5].length) (baseStart_5052464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052464 prefixEnd_5052464 := by exact prefixLift 5052464
  have htrace : WordTrace (prefixWord ++ tailWord_5052464) baseStart_5052464 baseEnd_5052464 := by
    simpa [prefixWord, tailWord_5052464, baseEnd_5052464] using wordTrace_append hprefix tailTrace_5052464
  have hstable : (prefixWord ++ tailWord_5052464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052464).length < 2 ^ (prefixWord ++ tailWord_5052464).sum := by decide
  have hdescent : baseEnd_5052464 < baseStart_5052464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052472 : List Nat := [2, 1, 2, 1, 7, 1, 2, 2, 1, 1, 3]
def baseStart_5052472 : Nat := 118140960795 + 5052472 * 2 ^ 59
def prefixEnd_5052472 : Nat := 4983230072969 + 3 ^ 40 * 5052472 * 2
def baseEnd_5052472 : Nat := 2594346629383261413764111

theorem tailTrace_5052472 : CollatzResearch.WordTrace tailWord_5052472 prefixEnd_5052472 2594346629383261413764111 := by
  unfold tailWord_5052472
  simp only [CollatzResearch.WordTrace]
  refine ⟨92139396475882156182123835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122852528634509541576165113 92139396475882156182123835)
  ·
    refine ⟨138209094713823234273185753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92139396475882156182123835 138209094713823234273185753)
    ·
      refine ⟨103656821035367425704889315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138209094713823234273185753 103656821035367425704889315)
      ·
        refine ⟨155485231553051138557333973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103656821035367425704889315 155485231553051138557333973)
        ·
          refine ⟨3644185114524636059937515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 155485231553051138557333973 3644185114524636059937515)
          ·
            refine ⟨5466277671786954089906273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3644185114524636059937515 5466277671786954089906273)
            ·
              refine ⟨4099708253840215567429705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5466277671786954089906273 4099708253840215567429705)
              ·
                refine ⟨3074781190380161675572279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4099708253840215567429705 3074781190380161675572279)
                ·
                  refine ⟨4612171785570242513358419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3074781190380161675572279 4612171785570242513358419)
                  ·
                    refine ⟨6918257678355363770037629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4612171785570242513358419 6918257678355363770037629)
                    ·
                      refine ⟨2594346629383261413764111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6918257678355363770037629 2594346629383261413764111)
                      ·
                        rfl

theorem cell23_5052472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 1, 1, 3].length) (baseStart_5052472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052472 prefixEnd_5052472 := by exact prefixLift 5052472
  have htrace : WordTrace (prefixWord ++ tailWord_5052472) baseStart_5052472 baseEnd_5052472 := by
    simpa [prefixWord, tailWord_5052472, baseEnd_5052472] using wordTrace_append hprefix tailTrace_5052472
  have hstable : (prefixWord ++ tailWord_5052472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052472).length < 2 ^ (prefixWord ++ tailWord_5052472).sum := by decide
  have hdescent : baseEnd_5052472 < baseStart_5052472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052494 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3]
def baseStart_5052494 : Nat := 118140960795 + 5052494 * 2 ^ 59
def prefixEnd_5052494 : Nat := 4983230072969 + 3 ^ 40 * 5052494 * 2
def baseEnd_5052494 : Nat := 2594357925957660327689009

theorem tailTrace_5052494 : CollatzResearch.WordTrace tailWord_5052494 prefixEnd_5052494 2594357925957660327689009 := by
  unfold tailWord_5052494
  simp only [CollatzResearch.WordTrace]
  refine ⟨23034949419710576265193567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122853063571789740081032357 23034949419710576265193567)
  ·
    refine ⟨34552424129565864397790351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23034949419710576265193567 34552424129565864397790351)
    ·
      refine ⟨51828636194348796596685527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34552424129565864397790351 51828636194348796596685527)
      ·
        refine ⟨77742954291523194895028291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51828636194348796596685527 77742954291523194895028291)
        ·
          refine ⟨116614431437284792342542437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77742954291523194895028291 116614431437284792342542437)
          ·
            refine ⟨21865205894490898564226707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116614431437284792342542437 21865205894490898564226707)
            ·
              refine ⟨32797808841736347846340061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21865205894490898564226707 32797808841736347846340061)
              ·
                refine ⟨12299178315651130442377523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32797808841736347846340061 12299178315651130442377523)
                ·
                  refine ⟨18448767473476695663566285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12299178315651130442377523 18448767473476695663566285)
                  ·
                    refine ⟨6918287802553760873837357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18448767473476695663566285 6918287802553760873837357)
                    ·
                      refine ⟨2594357925957660327689009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6918287802553760873837357 2594357925957660327689009)
                      ·
                        rfl

theorem cell23_5052494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_5052494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052494 prefixEnd_5052494 := by exact prefixLift 5052494
  have htrace : WordTrace (prefixWord ++ tailWord_5052494) baseStart_5052494 baseEnd_5052494 := by
    simpa [prefixWord, tailWord_5052494, baseEnd_5052494] using wordTrace_append hprefix tailTrace_5052494
  have hstable : (prefixWord ++ tailWord_5052494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052494).length < 2 ^ (prefixWord ++ tailWord_5052494).sum := by decide
  have hdescent : baseEnd_5052494 < baseStart_5052494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052521 : List Nat := [1, 2, 1, 1, 1, 5, 3, 3, 1, 3, 2]
def baseStart_5052521 : Nat := 118140960795 + 5052521 * 2 ^ 59
def prefixEnd_5052521 : Nat := 4983230072969 + 3 ^ 40 * 5052521 * 2
def baseEnd_5052521 : Nat := 2594371789935331722051385

theorem tailTrace_5052521 : CollatzResearch.WordTrace tailWord_5052521 prefixEnd_5052521 2594371789935331722051385 := by
  unfold tailWord_5052521
  simp only [CollatzResearch.WordTrace]
  refine ⟨184280580128586793732781417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122853720085724529155187611 184280580128586793732781417)
  ·
    refine ⟨138210435096440095299586063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184280580128586793732781417 138210435096440095299586063)
    ·
      refine ⟨207315652644660142949379095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138210435096440095299586063 207315652644660142949379095)
      ·
        refine ⟨310973478966990214424068643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207315652644660142949379095 310973478966990214424068643)
        ·
          refine ⟨466460218450485321636102965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310973478966990214424068643 466460218450485321636102965)
          ·
            refine ⟨43730645479732998903384653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 466460218450485321636102965 43730645479732998903384653)
            ·
              refine ⟨16398992054899874588769245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43730645479732998903384653 16398992054899874588769245)
              ·
                refine ⟨6149622020587452970788467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16398992054899874588769245 6149622020587452970788467)
                ·
                  refine ⟨9224433030881179456182701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6149622020587452970788467 9224433030881179456182701)
                  ·
                    refine ⟨3459162386580442296068513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9224433030881179456182701 3459162386580442296068513)
                    ·
                      refine ⟨2594371789935331722051385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3459162386580442296068513 2594371789935331722051385)
                      ·
                        rfl

theorem cell23_5052521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 3, 2].length) (baseStart_5052521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052521 prefixEnd_5052521 := by exact prefixLift 5052521
  have htrace : WordTrace (prefixWord ++ tailWord_5052521) baseStart_5052521 baseEnd_5052521 := by
    simpa [prefixWord, tailWord_5052521, baseEnd_5052521] using wordTrace_append hprefix tailTrace_5052521
  have hstable : (prefixWord ++ tailWord_5052521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052521).length < 2 ^ (prefixWord ++ tailWord_5052521).sum := by decide
  have hdescent : baseEnd_5052521 < baseStart_5052521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052527 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 2, 6]
def baseStart_5052527 : Nat := 118140960795 + 5052527 * 2 ^ 59
def prefixEnd_5052527 : Nat := 4983230072969 + 3 ^ 40 * 5052527 * 2
def baseEnd_5052527 : Nat := 864791623606419566192119

theorem tailTrace_5052527 : CollatzResearch.WordTrace tailWord_5052527 prefixEnd_5052527 864791623606419566192119 := by
  unfold tailWord_5052527
  simp only [CollatzResearch.WordTrace]
  refine ⟨184280798966565056757499835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122853865977710037838333223 184280798966565056757499835)
  ·
    refine ⟨276421198449847585136249753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184280798966565056757499835 276421198449847585136249753)
    ·
      refine ⟨207315898837385688852187315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276421198449847585136249753 207315898837385688852187315)
      ·
        refine ⟨310973848256078533278280973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207315898837385688852187315 310973848256078533278280973)
        ·
          refine ⟨116615193096029449979355365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310973848256078533278280973 116615193096029449979355365)
          ·
            refine ⟨21865348705505521871129131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116615193096029449979355365 21865348705505521871129131)
            ·
              refine ⟨32798023058258282806693697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21865348705505521871129131 32798023058258282806693697)
              ·
                refine ⟨24598517293693712105020273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32798023058258282806693697 24598517293693712105020273)
                ·
                  refine ⟨18448887970270284078765205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24598517293693712105020273 18448887970270284078765205)
                  ·
                    refine ⟨864791623606419566192119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18448887970270284078765205 864791623606419566192119)
                    ·
                      rfl

theorem cell23_5052527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 6].length) (baseStart_5052527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052527 prefixEnd_5052527 := by exact prefixLift 5052527
  have htrace : WordTrace (prefixWord ++ tailWord_5052527) baseStart_5052527 baseEnd_5052527 := by
    simpa [prefixWord, tailWord_5052527, baseEnd_5052527] using wordTrace_append hprefix tailTrace_5052527
  have hstable : (prefixWord ++ tailWord_5052527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052527).length < 2 ^ (prefixWord ++ tailWord_5052527).sum := by decide
  have hdescent : baseEnd_5052527 < baseStart_5052527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052528 : List Nat := [2, 1, 1, 1, 5, 4, 1, 2, 2, 1, 3]
def baseStart_5052528 : Nat := 118140960795 + 5052528 * 2 ^ 59
def prefixEnd_5052528 : Nat := 4983230072969 + 3 ^ 40 * 5052528 * 2
def baseEnd_5052528 : Nat := 2594375384299913194663853

theorem tailTrace_5052528 : CollatzResearch.WordTrace tailWord_5052528 prefixEnd_5052528 2594375384299913194663853 := by
  unfold tailWord_5052528
  simp only [CollatzResearch.WordTrace]
  refine ⟨92140417719780716964143119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122853890293040955952190825 92140417719780716964143119)
  ·
    refine ⟨138210626579671075446214679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92140417719780716964143119 138210626579671075446214679)
    ·
      refine ⟨207315939869506613169322019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138210626579671075446214679 207315939869506613169322019)
      ·
        refine ⟨310973909804259919753983029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207315939869506613169322019 310973909804259919753983029)
        ·
          refine ⟨29153804044149367476935909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 310973909804259919753983029 29153804044149367476935909)
          ·
            refine ⟨5466338258278006401925483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29153804044149367476935909 5466338258278006401925483)
            ·
              refine ⟨8199507387417009602888225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5466338258278006401925483 8199507387417009602888225)
              ·
                refine ⟨6149630540562757202166169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8199507387417009602888225 6149630540562757202166169)
                ·
                  refine ⟨4612222905422067901624627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6149630540562757202166169 4612222905422067901624627)
                  ·
                    refine ⟨6918334358133101852436941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4612222905422067901624627 6918334358133101852436941)
                    ·
                      refine ⟨2594375384299913194663853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6918334358133101852436941 2594375384299913194663853)
                      ·
                        rfl

theorem cell23_5052528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 2, 1, 3].length) (baseStart_5052528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052528 prefixEnd_5052528 := by exact prefixLift 5052528
  have htrace : WordTrace (prefixWord ++ tailWord_5052528) baseStart_5052528 baseEnd_5052528 := by
    simpa [prefixWord, tailWord_5052528, baseEnd_5052528] using wordTrace_append hprefix tailTrace_5052528
  have hstable : (prefixWord ++ tailWord_5052528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052528).length < 2 ^ (prefixWord ++ tailWord_5052528).sum := by decide
  have hdescent : baseEnd_5052528 < baseStart_5052528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052545 : List Nat := [1, 2, 4, 2, 3, 1, 3, 1, 2, 1, 3]
def baseStart_5052545 : Nat := 118140960795 + 5052545 * 2 ^ 59
def prefixEnd_5052545 : Nat := 4983230072969 + 3 ^ 40 * 5052545 * 2
def baseEnd_5052545 : Nat := 2594384113471039628151275

theorem tailTrace_5052545 : CollatzResearch.WordTrace tailWord_5052545 prefixEnd_5052545 2594384113471039628151275 := by
  unfold tailWord_5052545
  simp only [CollatzResearch.WordTrace]
  refine ⟨184281455480499845831655089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122854303653666563887770059 184281455480499845831655089)
  ·
    refine ⟨138211091610374884373741317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184281455480499845831655089 138211091610374884373741317)
    ·
      refine ⟨25914579676945290820076497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138211091610374884373741317 25914579676945290820076497)
      ·
        refine ⟨19435934757708968115057373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25914579676945290820076497 19435934757708968115057373)
        ·
          refine ⟨7288475534140863043146515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19435934757708968115057373 7288475534140863043146515)
          ·
            refine ⟨10932713301211294564719773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7288475534140863043146515 10932713301211294564719773)
            ·
              refine ⟨4099767487954235461769915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10932713301211294564719773 4099767487954235461769915)
              ·
                refine ⟨6149651231931353192654873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4099767487954235461769915 6149651231931353192654873)
                ·
                  refine ⟨4612238423948514894491155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6149651231931353192654873 4612238423948514894491155)
                  ·
                    refine ⟨6918357635922772341736733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4612238423948514894491155 6918357635922772341736733)
                    ·
                      refine ⟨2594384113471039628151275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6918357635922772341736733 2594384113471039628151275)
                      ·
                        rfl

theorem cell23_5052545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_5052545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052545 prefixEnd_5052545 := by exact prefixLift 5052545
  have htrace : WordTrace (prefixWord ++ tailWord_5052545) baseStart_5052545 baseEnd_5052545 := by
    simpa [prefixWord, tailWord_5052545, baseEnd_5052545] using wordTrace_append hprefix tailTrace_5052545
  have hstable : (prefixWord ++ tailWord_5052545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052545).length < 2 ^ (prefixWord ++ tailWord_5052545).sum := by decide
  have hdescent : baseEnd_5052545 < baseStart_5052545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052551 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 1, 4, 2]
def baseStart_5052551 : Nat := 118140960795 + 5052551 * 2 ^ 59
def prefixEnd_5052551 : Nat := 4983230072969 + 3 ^ 40 * 5052551 * 2
def baseEnd_5052551 : Nat := 2594387194354966604676247

theorem tailTrace_5052551 : CollatzResearch.WordTrace tailWord_5052551 prefixEnd_5052551 2594387194354966604676247 := by
  unfold tailWord_5052551
  simp only [CollatzResearch.WordTrace]
  refine ⟨184281674318478108856373507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122854449545652072570915671 184281674318478108856373507)
  ·
    refine ⟨276422511477717163284560261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184281674318478108856373507 276422511477717163284560261)
    ·
      refine ⟨51829220902071968115855049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276422511477717163284560261 51829220902071968115855049)
      ·
        refine ⟨38871915676553976086891287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51829220902071968115855049 38871915676553976086891287)
        ·
          refine ⟨58307873514830964130336931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38871915676553976086891287 58307873514830964130336931)
          ·
            refine ⟨87461810272246446195505397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58307873514830964130336931 87461810272246446195505397)
            ·
              refine ⟨8199544713023104330828631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87461810272246446195505397 8199544713023104330828631)
              ·
                refine ⟨12299317069534656496242947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8199544713023104330828631 12299317069534656496242947)
                ·
                  refine ⟨18448975604301984744364421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12299317069534656496242947 18448975604301984744364421)
                  ·
                    refine ⟨3459182925806622139568329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18448975604301984744364421 3459182925806622139568329)
                    ·
                      refine ⟨2594387194354966604676247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3459182925806622139568329 2594387194354966604676247)
                      ·
                        rfl

theorem cell23_5052551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_5052551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052551 prefixEnd_5052551 := by exact prefixLift 5052551
  have htrace : WordTrace (prefixWord ++ tailWord_5052551) baseStart_5052551 baseEnd_5052551 := by
    simpa [prefixWord, tailWord_5052551, baseEnd_5052551] using wordTrace_append hprefix tailTrace_5052551
  have hstable : (prefixWord ++ tailWord_5052551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052551).length < 2 ^ (prefixWord ++ tailWord_5052551).sum := by decide
  have hdescent : baseEnd_5052551 < baseStart_5052551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052596 : List Nat := [2, 5, 3, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_5052596 : Nat := 118140960795 + 5052596 * 2 ^ 59
def prefixEnd_5052596 : Nat := 4983230072969 + 3 ^ 40 * 5052596 * 2
def baseEnd_5052596 : Nat := 2594410300984418928613541

theorem tailTrace_5052596 : CollatzResearch.WordTrace tailWord_5052596 prefixEnd_5052596 2594410300984418928613541 := by
  unfold tailWord_5052596
  simp only [CollatzResearch.WordTrace]
  refine ⟨92141657801657540770880821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122855543735543387694507761 92141657801657540770880821)
  ·
    refine ⟨8638280418905394447270077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92141657801657540770880821 8638280418905394447270077)
    ·
      refine ⟨3239355157089522917726279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8638280418905394447270077 3239355157089522917726279)
      ·
        refine ⟨4859032735634284376589419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3239355157089522917726279 4859032735634284376589419)
        ·
          refine ⟨7288549103451426564884129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4859032735634284376589419 7288549103451426564884129)
          ·
            refine ⟨5466411827588569923663097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7288549103451426564884129 5466411827588569923663097)
            ·
              refine ⟨4099808870691427442747323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5466411827588569923663097 4099808870691427442747323)
              ·
                refine ⟨6149713306037141164120985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4099808870691427442747323 6149713306037141164120985)
                ·
                  refine ⟨4612284979527855873090739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6149713306037141164120985 4612284979527855873090739)
                  ·
                    refine ⟨6918427469291783809636109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4612284979527855873090739 6918427469291783809636109)
                    ·
                      refine ⟨2594410300984418928613541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6918427469291783809636109 2594410300984418928613541)
                      ·
                        rfl

theorem cell23_5052596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_5052596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052596 prefixEnd_5052596 := by exact prefixLift 5052596
  have htrace : WordTrace (prefixWord ++ tailWord_5052596) baseStart_5052596 baseEnd_5052596 := by
    simpa [prefixWord, tailWord_5052596, baseEnd_5052596] using wordTrace_append hprefix tailTrace_5052596
  have hstable : (prefixWord ++ tailWord_5052596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052596).length < 2 ^ (prefixWord ++ tailWord_5052596).sum := by decide
  have hdescent : baseEnd_5052596 < baseStart_5052596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052627 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 5]
def baseStart_5052627 : Nat := 118140960795 + 5052627 * 2 ^ 59
def prefixEnd_5052627 : Nat := 4983230072969 + 3 ^ 40 * 5052627 * 2
def baseEnd_5052627 : Nat := 2594426218884708307325897

theorem tailTrace_5052627 : CollatzResearch.WordTrace tailWord_5052627 prefixEnd_5052627 2594426218884708307325897 := by
  unfold tailWord_5052627
  simp only [CollatzResearch.WordTrace]
  refine ⟨184284446266202773836140135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122856297510801849224093423 184284446266202773836140135)
  ·
    refine ⟨276426669399304160754210203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184284446266202773836140135 276426669399304160754210203)
    ·
      refine ⟨414640004098956241131315305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276426669399304160754210203 414640004098956241131315305)
      ·
        refine ⟨310980003074217180848486479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414640004098956241131315305 310980003074217180848486479)
        ·
          refine ⟨466470004611325771272729719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310980003074217180848486479 466470004611325771272729719)
          ·
            refine ⟨699705006916988656909094579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466470004611325771272729719 699705006916988656909094579)
            ·
              refine ⟨1049557510375482985363641869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699705006916988656909094579 1049557510375482985363641869)
              ·
                refine ⟨393584066390806119511365701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1049557510375482985363641869 393584066390806119511365701)
                ·
                  refine ⟨73797012448276147408381069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 393584066390806119511365701 73797012448276147408381069)
                  ·
                    refine ⟨27673879668103555278142901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73797012448276147408381069 27673879668103555278142901)
                    ·
                      refine ⟨2594426218884708307325897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27673879668103555278142901 2594426218884708307325897)
                      ·
                        rfl

theorem cell23_5052627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_5052627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052627 prefixEnd_5052627 := by exact prefixLift 5052627
  have htrace : WordTrace (prefixWord ++ tailWord_5052627) baseStart_5052627 baseEnd_5052627 := by
    simpa [prefixWord, tailWord_5052627, baseEnd_5052627] using wordTrace_append hprefix tailTrace_5052627
  have hstable : (prefixWord ++ tailWord_5052627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052627).length < 2 ^ (prefixWord ++ tailWord_5052627).sum := by decide
  have hdescent : baseEnd_5052627 < baseStart_5052627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052641 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 2, 4, 2]
def baseStart_5052641 : Nat := 118140960795 + 5052641 * 2 ^ 59
def prefixEnd_5052641 : Nat := 4983230072969 + 3 ^ 40 * 5052641 * 2
def baseEnd_5052641 : Nat := 2594433407613871252550833

theorem tailTrace_5052641 : CollatzResearch.WordTrace tailWord_5052641 prefixEnd_5052641 2594433407613871252550833 := by
  unfold tailWord_5052641
  simp only [CollatzResearch.WordTrace]
  refine ⟨184284956888152054227149777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122856637925434702818099851 184284956888152054227149777)
  ·
    refine ⟨138213717666114040670362333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184284956888152054227149777 138213717666114040670362333)
    ·
      refine ⟨51830144124792765251385875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138213717666114040670362333 51830144124792765251385875)
      ·
        refine ⟨77745216187189147877078813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51830144124792765251385875 77745216187189147877078813)
        ·
          refine ⟨29154456070195930453904555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77745216187189147877078813 29154456070195930453904555)
          ·
            refine ⟨43731684105293895680856833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29154456070195930453904555 43731684105293895680856833)
            ·
              refine ⟨32798763078970421760642625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43731684105293895680856833 32798763078970421760642625)
              ·
                refine ⟨24599072309227816320481969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32798763078970421760642625 24599072309227816320481969)
                ·
                  refine ⟨18449304231920862240361477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24599072309227816320481969 18449304231920862240361477)
                  ·
                    refine ⟨3459244543485161670067777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18449304231920862240361477 3459244543485161670067777)
                    ·
                      refine ⟨2594433407613871252550833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3459244543485161670067777 2594433407613871252550833)
                      ·
                        rfl

theorem cell23_5052641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_5052641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052641 prefixEnd_5052641 := by exact prefixLift 5052641
  have htrace : WordTrace (prefixWord ++ tailWord_5052641) baseStart_5052641 baseEnd_5052641 := by
    simpa [prefixWord, tailWord_5052641, baseEnd_5052641] using wordTrace_append hprefix tailTrace_5052641
  have hstable : (prefixWord ++ tailWord_5052641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052641).length < 2 ^ (prefixWord ++ tailWord_5052641).sum := by decide
  have hdescent : baseEnd_5052641 < baseStart_5052641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052642 : List Nat := [3, 3, 4, 1, 1, 1, 1, 4, 5]
def baseStart_5052642 : Nat := 118140960795 + 5052642 * 2 ^ 59
def prefixEnd_5052642 : Nat := 4983230072969 + 3 ^ 40 * 5052642 * 2
def baseEnd_5052642 : Nat := 288270435677169527626481

theorem tailTrace_5052642 : CollatzResearch.WordTrace tailWord_5052642 prefixEnd_5052642 288270435677169527626481 := by
  unfold tailWord_5052642
  simp only [CollatzResearch.WordTrace]
  refine ⟨46071248340287107849484045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122856662240765620931957453 46071248340287107849484045)
  ·
    refine ⟨17276718127607665443556517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46071248340287107849484045 17276718127607665443556517)
    ·
      refine ⟨3239384648926437270666847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17276718127607665443556517 3239384648926437270666847)
      ·
        refine ⟨4859076973389655906000271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3239384648926437270666847 4859076973389655906000271)
        ·
          refine ⟨7288615460084483859000407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4859076973389655906000271 7288615460084483859000407)
          ·
            refine ⟨10932923190126725788500611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7288615460084483859000407 10932923190126725788500611)
            ·
              refine ⟨16399384785190088682750917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10932923190126725788500611 16399384785190088682750917)
              ·
                refine ⟨3074884647223141628015797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16399384785190088682750917 3074884647223141628015797)
                ·
                  refine ⟨288270435677169527626481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3074884647223141628015797 288270435677169527626481)
                  ·
                    rfl

theorem cell23_5052642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_5052642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052642 prefixEnd_5052642 := by exact prefixLift 5052642
  have htrace : WordTrace (prefixWord ++ tailWord_5052642) baseStart_5052642 baseEnd_5052642 := by
    simpa [prefixWord, tailWord_5052642, baseEnd_5052642] using wordTrace_append hprefix tailTrace_5052642
  have hstable : (prefixWord ++ tailWord_5052642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052642).length < 2 ^ (prefixWord ++ tailWord_5052642).sum := by decide
  have hdescent : baseEnd_5052642 < baseStart_5052642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052644 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 3, 4, 3]
def baseStart_5052644 : Nat := 118140960795 + 5052644 * 2 ^ 59
def prefixEnd_5052644 : Nat := 4983230072969 + 3 ^ 40 * 5052644 * 2
def baseEnd_5052644 : Nat := 2594434948055834740813319

theorem tailTrace_5052644 : CollatzResearch.WordTrace tailWord_5052644 prefixEnd_5052644 2594434948055834740813319 := by
  unfold tailWord_5052644
  simp only [CollatzResearch.WordTrace]
  refine ⟨92142533153570592869754493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122856710871427457159672657 92142533153570592869754493)
  ·
    refine ⟨34553449932588972326157935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92142533153570592869754493 34553449932588972326157935)
    ·
      refine ⟨51830174898883458489236903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34553449932588972326157935 51830174898883458489236903)
      ·
        refine ⟨77745262348325187733855355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51830174898883458489236903 77745262348325187733855355)
        ·
          refine ⟨116617893522487781600783033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77745262348325187733855355 116617893522487781600783033)
          ·
            refine ⟨87463420141865836200587275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116617893522487781600783033 87463420141865836200587275)
            ·
              refine ⟨131195130212798754300880913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87463420141865836200587275 131195130212798754300880913)
              ·
                refine ⟨98396347659599065725660685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131195130212798754300880913 98396347659599065725660685)
                ·
                  refine ⟨36898630372349649647122757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98396347659599065725660685 36898630372349649647122757)
                  ·
                    refine ⟨6918493194815559308835517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36898630372349649647122757 6918493194815559308835517)
                    ·
                      refine ⟨2594434948055834740813319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6918493194815559308835517 2594434948055834740813319)
                      ·
                        rfl

theorem cell23_5052644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_5052644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052644 prefixEnd_5052644 := by exact prefixLift 5052644
  have htrace : WordTrace (prefixWord ++ tailWord_5052644) baseStart_5052644 baseEnd_5052644 := by
    simpa [prefixWord, tailWord_5052644, baseEnd_5052644] using wordTrace_append hprefix tailTrace_5052644
  have hstable : (prefixWord ++ tailWord_5052644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052644).length < 2 ^ (prefixWord ++ tailWord_5052644).sum := by decide
  have hdescent : baseEnd_5052644 < baseStart_5052644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052654 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_5052654 : Nat := 118140960795 + 5052654 * 2 ^ 59
def prefixEnd_5052654 : Nat := 4983230072969 + 3 ^ 40 * 5052654 * 2
def baseEnd_5052654 : Nat := 2594440082862379701688273

theorem tailTrace_5052654 : CollatzResearch.WordTrace tailWord_5052654 prefixEnd_5052654 2594440082862379701688273 := by
  unfold tailWord_5052654
  simp only [CollatzResearch.WordTrace]
  refine ⟨23035678879638119680921627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122856954024736638298248677 23035678879638119680921627)
  ·
    refine ⟨34553518319457179521382441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23035678879638119680921627 34553518319457179521382441)
    ·
      refine ⟨25915138739592884641036831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34553518319457179521382441 25915138739592884641036831)
      ·
        refine ⟨38872708109389326961555247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25915138739592884641036831 38872708109389326961555247)
        ·
          refine ⟨58309062164083990442332871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38872708109389326961555247 58309062164083990442332871)
          ·
            refine ⟨87463593246125985663499307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58309062164083990442332871 87463593246125985663499307)
            ·
              refine ⟨131195389869188978495248961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87463593246125985663499307 131195389869188978495248961)
              ·
                refine ⟨98396542401891733871436721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131195389869188978495248961 98396542401891733871436721)
                ·
                  refine ⟨73797406801418800403577541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98396542401891733871436721 73797406801418800403577541)
                  ·
                    refine ⟨13837013775266025075670789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73797406801418800403577541 13837013775266025075670789)
                    ·
                      refine ⟨2594440082862379701688273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13837013775266025075670789 2594440082862379701688273)
                      ·
                        rfl

theorem cell23_5052654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_5052654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052654 prefixEnd_5052654 := by exact prefixLift 5052654
  have htrace : WordTrace (prefixWord ++ tailWord_5052654) baseStart_5052654 baseEnd_5052654 := by
    simpa [prefixWord, tailWord_5052654, baseEnd_5052654] using wordTrace_append hprefix tailTrace_5052654
  have hstable : (prefixWord ++ tailWord_5052654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052654).length < 2 ^ (prefixWord ++ tailWord_5052654).sum := by decide
  have hdescent : baseEnd_5052654 < baseStart_5052654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052658 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 2, 4, 2]
def baseStart_5052658 : Nat := 118140960795 + 5052658 * 2 ^ 59
def prefixEnd_5052658 : Nat := 4983230072969 + 3 ^ 40 * 5052658 * 2
def baseEnd_5052658 : Nat := 2594442136784997686038255

theorem tailTrace_5052658 : CollatzResearch.WordTrace tailWord_5052658 prefixEnd_5052658 2594442136784997686038255 := by
  unfold tailWord_5052658
  simp only [CollatzResearch.WordTrace]
  refine ⟨46071394232272616532629657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122857051286060310753679085 46071394232272616532629657)
  ·
    refine ⟨34553545674204462399472243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46071394232272616532629657 34553545674204462399472243)
    ·
      refine ⟨51830318511306693599208365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34553545674204462399472243 51830318511306693599208365)
      ·
        refine ⟨19436369441740010099703137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51830318511306693599208365 19436369441740010099703137)
        ·
          refine ⟨14577277081305007574777353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19436369441740010099703137 14577277081305007574777353)
          ·
            refine ⟨10932957810978755681083015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14577277081305007574777353 10932957810978755681083015)
            ·
              refine ⟨16399436716468133521624523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10932957810978755681083015 16399436716468133521624523)
              ·
                refine ⟨24599155074702200282436785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16399436716468133521624523 24599155074702200282436785)
                ·
                  refine ⟨18449366306026650211827589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24599155074702200282436785 18449366306026650211827589)
                  ·
                    refine ⟨3459256182379996914717673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18449366306026650211827589 3459256182379996914717673)
                    ·
                      refine ⟨2594442136784997686038255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3459256182379996914717673 2594442136784997686038255)
                      ·
                        rfl

theorem cell23_5052658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_5052658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052658 prefixEnd_5052658 := by exact prefixLift 5052658
  have htrace : WordTrace (prefixWord ++ tailWord_5052658) baseStart_5052658 baseEnd_5052658 := by
    simpa [prefixWord, tailWord_5052658, baseEnd_5052658] using wordTrace_append hprefix tailTrace_5052658
  have hstable : (prefixWord ++ tailWord_5052658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052658).length < 2 ^ (prefixWord ++ tailWord_5052658).sum := by decide
  have hdescent : baseEnd_5052658 < baseStart_5052658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052698 : List Nat := [3, 1, 1, 3, 4, 2, 1, 2, 6]
def baseStart_5052698 : Nat := 118140960795 + 5052698 * 2 ^ 59
def prefixEnd_5052698 : Nat := 4983230072969 + 3 ^ 40 * 5052698 * 2
def baseEnd_5052698 : Nat := 288273630667908614393119

theorem tailTrace_5052698 : CollatzResearch.WordTrace tailWord_5052698 prefixEnd_5052698 288273630667908614393119 := by
  unfold tailWord_5052698
  simp only [CollatzResearch.WordTrace]
  refine ⟨46071758962236388240493687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122858023899297035307983165 46071758962236388240493687)
  ·
    refine ⟨69107638443354582360740531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46071758962236388240493687 69107638443354582360740531)
    ·
      refine ⟨103661457665031873541110797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69107638443354582360740531 103661457665031873541110797)
      ·
        refine ⟨38873046624386952577916549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103661457665031873541110797 38873046624386952577916549)
        ·
          refine ⟨7288696242072553608359353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38873046624386952577916549 7288696242072553608359353)
          ·
            refine ⟨5466522181554415206269515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7288696242072553608359353 5466522181554415206269515)
            ·
              refine ⟨8199783272331622809404273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5466522181554415206269515 8199783272331622809404273)
              ·
                refine ⟨6149837454248717107053205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8199783272331622809404273 6149837454248717107053205)
                ·
                  refine ⟨288273630667908614393119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6149837454248717107053205 288273630667908614393119)
                  ·
                    rfl

theorem cell23_5052698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 6].length) (baseStart_5052698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052698 prefixEnd_5052698 := by exact prefixLift 5052698
  have htrace : WordTrace (prefixWord ++ tailWord_5052698) baseStart_5052698 baseEnd_5052698 := by
    simpa [prefixWord, tailWord_5052698, baseEnd_5052698] using wordTrace_append hprefix tailTrace_5052698
  have hstable : (prefixWord ++ tailWord_5052698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052698).length < 2 ^ (prefixWord ++ tailWord_5052698).sum := by decide
  have hdescent : baseEnd_5052698 < baseStart_5052698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052702 : List Nat := [4, 3, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_5052702 : Nat := 118140960795 + 5052702 * 2 ^ 59
def prefixEnd_5052702 : Nat := 4983230072969 + 3 ^ 40 * 5052702 * 2
def baseEnd_5052702 : Nat := 864821576644598504629351

theorem tailTrace_5052702 : CollatzResearch.WordTrace tailWord_5052702 prefixEnd_5052702 864821576644598504629351 := by
  unfold tailWord_5052702
  simp only [CollatzResearch.WordTrace]
  refine ⟨23035897717616382705640045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122858121160620707763413573 23035897717616382705640045)
  ·
    refine ⟨8638461644106143514615017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23035897717616382705640045 8638461644106143514615017)
    ·
      refine ⟨6478846233079607635961263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8638461644106143514615017 6478846233079607635961263)
      ·
        refine ⟨9718269349619411453941895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6478846233079607635961263 9718269349619411453941895)
        ·
          refine ⟨14577404024429117180912843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9718269349619411453941895 14577404024429117180912843)
          ·
            refine ⟨21866106036643675771369265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14577404024429117180912843 21866106036643675771369265)
            ·
              refine ⟨16399579527482756828526949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21866106036643675771369265 16399579527482756828526949)
              ·
                refine ⟨3074921161403016905348803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16399579527482756828526949 3074921161403016905348803)
                ·
                  refine ⟨4612381742104525358023205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3074921161403016905348803 4612381742104525358023205)
                  ·
                    refine ⟨864821576644598504629351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4612381742104525358023205 864821576644598504629351)
                    ·
                      rfl

theorem cell23_5052702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_5052702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052702 prefixEnd_5052702 := by exact prefixLift 5052702
  have htrace : WordTrace (prefixWord ++ tailWord_5052702) baseStart_5052702 baseEnd_5052702 := by
    simpa [prefixWord, tailWord_5052702, baseEnd_5052702] using wordTrace_append hprefix tailTrace_5052702
  have hstable : (prefixWord ++ tailWord_5052702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052702).length < 2 ^ (prefixWord ++ tailWord_5052702).sum := by decide
  have hdescent : baseEnd_5052702 < baseStart_5052702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052708 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 3, 1, 3]
def baseStart_5052708 : Nat := 118140960795 + 5052708 * 2 ^ 59
def prefixEnd_5052708 : Nat := 4983230072969 + 3 ^ 40 * 5052708 * 2
def baseEnd_5052708 : Nat := 2594467810817722490413025

theorem tailTrace_5052708 : CollatzResearch.WordTrace tailWord_5052708 prefixEnd_5052708 2594467810817722490413025 := by
  unfold tailWord_5052708
  simp only [CollatzResearch.WordTrace]
  refine ⟨92143700289454662334919389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122858267052606216446559185 92143700289454662334919389)
  ·
    refine ⟨34553887608545498375594771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92143700289454662334919389 34553887608545498375594771)
    ·
      refine ⟨51830831412818247563392157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34553887608545498375594771 51830831412818247563392157)
      ·
        refine ⟨19436561779806842836272059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51830831412818247563392157 19436561779806842836272059)
        ·
          refine ⟨29154842669710264254408089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19436561779806842836272059 29154842669710264254408089)
          ·
            refine ⟨21866132002282698190806067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29154842669710264254408089 21866132002282698190806067)
            ·
              refine ⟨32799198003424047286209101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21866132002282698190806067 32799198003424047286209101)
              ·
                refine ⟨12299699251284017732328413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32799198003424047286209101 12299699251284017732328413)
                ·
                  refine ⟨4612387219231506649623155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12299699251284017732328413 4612387219231506649623155)
                  ·
                    refine ⟨6918580828847259974434733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4612387219231506649623155 6918580828847259974434733)
                    ·
                      refine ⟨2594467810817722490413025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6918580828847259974434733 2594467810817722490413025)
                      ·
                        rfl

theorem cell23_5052708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_5052708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052708 prefixEnd_5052708 := by exact prefixLift 5052708
  have htrace : WordTrace (prefixWord ++ tailWord_5052708) baseStart_5052708 baseEnd_5052708 := by
    simpa [prefixWord, tailWord_5052708, baseEnd_5052708] using wordTrace_append hprefix tailTrace_5052708
  have hstable : (prefixWord ++ tailWord_5052708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052708).length < 2 ^ (prefixWord ++ tailWord_5052708).sum := by decide
  have hdescent : baseEnd_5052708 < baseStart_5052708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052754 : List Nat := [3, 2, 2, 1, 1, 1, 13]
def baseStart_5052754 : Nat := 118140960795 + 5052754 * 2 ^ 59
def prefixEnd_5052754 : Nat := 4983230072969 + 3 ^ 40 * 5052754 * 2
def baseEnd_5052754 : Nat := 32030758406516411239973

theorem tailTrace_5052754 : CollatzResearch.WordTrace tailWord_5052754 prefixEnd_5052754 32030758406516411239973 := by
  unfold tailWord_5052754
  simp only [CollatzResearch.WordTrace]
  refine ⟨46072269584185668631503329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122859385557828449684008877 46072269584185668631503329)
  ·
    refine ⟨34554202188139251473627497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46072269584185668631503329 34554202188139251473627497)
    ·
      refine ⟨25915651641104438605220623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34554202188139251473627497 25915651641104438605220623)
      ·
        refine ⟨38873477461656657907830935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25915651641104438605220623 38873477461656657907830935)
        ·
          refine ⟨58310216192484986861746403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38873477461656657907830935 58310216192484986861746403)
          ·
            refine ⟨87465324288727480292619605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58310216192484986861746403 87465324288727480292619605)
            ·
              refine ⟨32030758406516411239973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 87465324288727480292619605 32030758406516411239973)
              ·
                rfl

theorem cell23_5052754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 13].length) (baseStart_5052754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052754 prefixEnd_5052754 := by exact prefixLift 5052754
  have htrace : WordTrace (prefixWord ++ tailWord_5052754) baseStart_5052754 baseEnd_5052754 := by
    simpa [prefixWord, tailWord_5052754, baseEnd_5052754] using wordTrace_append hprefix tailTrace_5052754
  have hstable : (prefixWord ++ tailWord_5052754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052754).length < 2 ^ (prefixWord ++ tailWord_5052754).sum := by decide
  have hdescent : baseEnd_5052754 < baseStart_5052754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052766 : List Nat := [4, 4, 2, 1, 1, 2, 2, 1, 6]
def baseStart_5052766 : Nat := 118140960795 + 5052766 * 2 ^ 59
def prefixEnd_5052766 : Nat := 4983230072969 + 3 ^ 40 * 5052766 * 2
def baseEnd_5052766 : Nat := 288277510299520362609751

theorem tailTrace_5052766 : CollatzResearch.WordTrace tailWord_5052766 prefixEnd_5052766 288277510299520362609751 := by
  unfold tailWord_5052766
  simp only [CollatzResearch.WordTrace]
  refine ⟨23036189501587400071931269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122859677341799467050300101 23036189501587400071931269)
  ·
    refine ⟨4319285531547637513487113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23036189501587400071931269 4319285531547637513487113)
    ·
      refine ⟨3239464148660728135115335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4319285531547637513487113 3239464148660728135115335)
      ·
        refine ⟨4859196222991092202673003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3239464148660728135115335 4859196222991092202673003)
        ·
          refine ⟨7288794334486638304009505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4859196222991092202673003 7288794334486638304009505)
          ·
            refine ⟨5466595750864978728007129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7288794334486638304009505 5466595750864978728007129)
            ·
              refine ⟨4099946813148734046005347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5466595750864978728007129 4099946813148734046005347)
              ·
                refine ⟨6149920219723101069008021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4099946813148734046005347 6149920219723101069008021)
                ·
                  refine ⟨288277510299520362609751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6149920219723101069008021 288277510299520362609751)
                  ·
                    rfl

theorem cell23_5052766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_5052766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052766 prefixEnd_5052766 := by exact prefixLift 5052766
  have htrace : WordTrace (prefixWord ++ tailWord_5052766) baseStart_5052766 baseEnd_5052766 := by
    simpa [prefixWord, tailWord_5052766, baseEnd_5052766] using wordTrace_append hprefix tailTrace_5052766
  have hstable : (prefixWord ++ tailWord_5052766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052766).length < 2 ^ (prefixWord ++ tailWord_5052766).sum := by decide
  have hdescent : baseEnd_5052766 < baseStart_5052766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052775 : List Nat := [1, 1, 5, 1, 3, 1, 4, 1, 2, 4]
def baseStart_5052775 : Nat := 118140960795 + 5052775 * 2 ^ 59
def prefixEnd_5052775 : Nat := 4983230072969 + 3 ^ 40 * 5052775 * 2
def baseEnd_5052775 : Nat := 864834071340524576091739

theorem tailTrace_5052775 : CollatzResearch.WordTrace tailWord_5052775 prefixEnd_5052775 864834071340524576091739 := by
  unfold tailWord_5052775
  simp only [CollatzResearch.WordTrace]
  refine ⟨184289844269666595112527779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122859896179777730075018519 184289844269666595112527779)
  ·
    refine ⟨276434766404499892668791669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184289844269666595112527779 276434766404499892668791669)
    ·
      refine ⟨25915759350421864937699219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 276434766404499892668791669 25915759350421864937699219)
      ·
        refine ⟨38873639025632797406548829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25915759350421864937699219 38873639025632797406548829)
        ·
          refine ⟨14577614634612299027455811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38873639025632797406548829 14577614634612299027455811)
          ·
            refine ⟨21866421951918448541183717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14577614634612299027455811 21866421951918448541183717)
            ·
              refine ⟨4099954115984709101471947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21866421951918448541183717 4099954115984709101471947)
              ·
                refine ⟨6149931173977063652207921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4099954115984709101471947 6149931173977063652207921)
                ·
                  refine ⟨4612448380482797739155941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6149931173977063652207921 4612448380482797739155941)
                  ·
                    refine ⟨864834071340524576091739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4612448380482797739155941 864834071340524576091739)
                    ·
                      rfl

theorem cell23_5052775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_5052775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052775 prefixEnd_5052775 := by exact prefixLift 5052775
  have htrace : WordTrace (prefixWord ++ tailWord_5052775) baseStart_5052775 baseEnd_5052775 := by
    simpa [prefixWord, tailWord_5052775, baseEnd_5052775] using wordTrace_append hprefix tailTrace_5052775
  have hstable : (prefixWord ++ tailWord_5052775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052775).length < 2 ^ (prefixWord ++ tailWord_5052775).sum := by decide
  have hdescent : baseEnd_5052775 < baseStart_5052775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052802 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_5052802 : Nat := 118140960795 + 5052802 * 2 ^ 59
def prefixEnd_5052802 : Nat := 4983230072969 + 3 ^ 40 * 5052802 * 2
def baseEnd_5052802 : Nat := 2594516077999245122637593

theorem tailTrace_5052802 : CollatzResearch.WordTrace tailWord_5052802 prefixEnd_5052802 2594516077999245122637593 := by
  unfold tailWord_5052802
  simp only [CollatzResearch.WordTrace]
  refine ⟨46072707260142194680940165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122860552693712519149173773 46072707260142194680940165)
  ·
    refine ⟨8638632611276661502676281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46072707260142194680940165 8638632611276661502676281)
    ·
      refine ⟨6478974458457496127007211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8638632611276661502676281 6478974458457496127007211)
      ·
        refine ⟨9718461687686244190510817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6478974458457496127007211 9718461687686244190510817)
        ·
          refine ⟨7288846265764683142883113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9718461687686244190510817 7288846265764683142883113)
          ·
            refine ⟨5466634699323512357162335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7288846265764683142883113 5466634699323512357162335)
            ·
              refine ⟨8199952048985268535743503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5466634699323512357162335 8199952048985268535743503)
              ·
                refine ⟨12299928073477902803615255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8199952048985268535743503 12299928073477902803615255)
                ·
                  refine ⟨18449892110216854205422883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12299928073477902803615255 18449892110216854205422883)
                  ·
                    refine ⟨27674838165325281308134325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18449892110216854205422883 27674838165325281308134325)
                    ·
                      refine ⟨2594516077999245122637593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27674838165325281308134325 2594516077999245122637593)
                      ·
                        rfl

theorem cell23_5052802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_5052802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052802 prefixEnd_5052802 := by exact prefixLift 5052802
  have htrace : WordTrace (prefixWord ++ tailWord_5052802) baseStart_5052802 baseEnd_5052802 := by
    simpa [prefixWord, tailWord_5052802, baseEnd_5052802] using wordTrace_append hprefix tailTrace_5052802
  have hstable : (prefixWord ++ tailWord_5052802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052802).length < 2 ^ (prefixWord ++ tailWord_5052802).sum := by decide
  have hdescent : baseEnd_5052802 < baseStart_5052802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052831 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 2, 6]
def baseStart_5052831 : Nat := 118140960795 + 5052831 * 2 ^ 59
def prefixEnd_5052831 : Nat := 4983230072969 + 3 ^ 40 * 5052831 * 2
def baseEnd_5052831 : Nat := 864843656312741836391653

theorem tailTrace_5052831 : CollatzResearch.WordTrace tailWord_5052831 prefixEnd_5052831 864843656312741836391653 := by
  unfold tailWord_5052831
  simp only [CollatzResearch.WordTrace]
  refine ⟨184291886757463716676566347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122861257838309144451044231 184291886757463716676566347)
  ·
    refine ⟨276437830136195575014849521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184291886757463716676566347 276437830136195575014849521)
    ·
      refine ⟨207328372602146681261137141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276437830136195575014849521 207328372602146681261137141)
      ·
        refine ⟨19437034931451251368231607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 207328372602146681261137141 19437034931451251368231607)
        ·
          refine ⟨29155552397176877052347411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19437034931451251368231607 29155552397176877052347411)
          ·
            refine ⟨43733328595765315578521117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29155552397176877052347411 43733328595765315578521117)
            ·
              refine ⟨16399998223411993341945419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43733328595765315578521117 16399998223411993341945419)
              ·
                refine ⟨24599997335117990012918129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16399998223411993341945419 24599997335117990012918129)
                ·
                  refine ⟨18449998001338492509688597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24599997335117990012918129 18449998001338492509688597)
                  ·
                    refine ⟨864843656312741836391653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18449998001338492509688597 864843656312741836391653)
                    ·
                      rfl

theorem cell23_5052831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 6].length) (baseStart_5052831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052831 prefixEnd_5052831 := by exact prefixLift 5052831
  have htrace : WordTrace (prefixWord ++ tailWord_5052831) baseStart_5052831 baseEnd_5052831 := by
    simpa [prefixWord, tailWord_5052831, baseEnd_5052831] using wordTrace_append hprefix tailTrace_5052831
  have hstable : (prefixWord ++ tailWord_5052831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052831).length < 2 ^ (prefixWord ++ tailWord_5052831).sum := by decide
  have hdescent : baseEnd_5052831 < baseStart_5052831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052872 : List Nat := [2, 1, 3, 1, 3, 2, 3, 2, 2, 2, 2]
def baseStart_5052872 : Nat := 118140960795 + 5052872 * 2 ^ 59
def prefixEnd_5052872 : Nat := 4983230072969 + 3 ^ 40 * 5052872 * 2
def baseEnd_5052872 : Nat := 2594552021645059848762271

theorem tailTrace_5052872 : CollatzResearch.WordTrace tailWord_5052872 prefixEnd_5052872 2594552021645059848762271 := by
  unfold tailWord_5052872
  simp only [CollatzResearch.WordTrace]
  refine ⟨92146691075157590339404435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122862254766876787119205913 92146691075157590339404435)
  ·
    refine ⟨138220036612736385509106653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92146691075157590339404435 138220036612736385509106653)
    ·
      refine ⟨51832513729776144565914995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138220036612736385509106653 51832513729776144565914995)
      ·
        refine ⟨77748770594664216848872493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51832513729776144565914995 77748770594664216848872493)
        ·
          refine ⟨29155788972999081318327185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77748770594664216848872493 29155788972999081318327185)
          ·
            refine ⟨21866841729749310988745389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29155788972999081318327185 21866841729749310988745389)
            ·
              refine ⟨8200065648655991620779521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21866841729749310988745389 8200065648655991620779521)
              ·
                refine ⟨6150049236491993715584641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8200065648655991620779521 6150049236491993715584641)
                ·
                  refine ⟨4612536927368995286688481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6150049236491993715584641 4612536927368995286688481)
                  ·
                    refine ⟨3459402695526746465016361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4612536927368995286688481 3459402695526746465016361)
                    ·
                      refine ⟨2594552021645059848762271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3459402695526746465016361 2594552021645059848762271)
                      ·
                        rfl

theorem cell23_5052872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_5052872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052872 prefixEnd_5052872 := by exact prefixLift 5052872
  have htrace : WordTrace (prefixWord ++ tailWord_5052872) baseStart_5052872 baseEnd_5052872 := by
    simpa [prefixWord, tailWord_5052872, baseEnd_5052872] using wordTrace_append hprefix tailTrace_5052872
  have hstable : (prefixWord ++ tailWord_5052872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052872).length < 2 ^ (prefixWord ++ tailWord_5052872).sum := by decide
  have hdescent : baseEnd_5052872 < baseStart_5052872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052918 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_5052918 : Nat := 118140960795 + 5052918 * 2 ^ 59
def prefixEnd_5052918 : Nat := 4983230072969 + 3 ^ 40 * 5052918 * 2
def baseEnd_5052918 : Nat := 2594575641755166668787059

theorem tailTrace_5052918 : CollatzResearch.WordTrace tailWord_5052918 prefixEnd_5052918 2594575641755166668787059 := by
  unfold tailWord_5052918
  simp only [CollatzResearch.WordTrace]
  refine ⟨11518441244259283158436463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122863373272099020356655605 11518441244259283158436463)
  ·
    refine ⟨17277661866388924737654695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11518441244259283158436463 17277661866388924737654695)
    ·
      refine ⟨25916492799583387106482043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17277661866388924737654695 25916492799583387106482043)
      ·
        refine ⟨38874739199375080659723065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25916492799583387106482043 38874739199375080659723065)
        ·
          refine ⟨29156054399531310494792299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38874739199375080659723065 29156054399531310494792299)
          ·
            refine ⟨43734081599296965742188449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29156054399531310494792299 43734081599296965742188449)
            ·
              refine ⟨32800561199472724306641337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43734081599296965742188449 32800561199472724306641337)
              ·
                refine ⟨24600420899604543229981003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32800561199472724306641337 24600420899604543229981003)
                ·
                  refine ⟨36900631349406814844971505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24600420899604543229981003 36900631349406814844971505)
                  ·
                    refine ⟨27675473512055111133728629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36900631349406814844971505 27675473512055111133728629)
                    ·
                      refine ⟨2594575641755166668787059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27675473512055111133728629 2594575641755166668787059)
                      ·
                        rfl

theorem cell23_5052918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_5052918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052918 prefixEnd_5052918 := by exact prefixLift 5052918
  have htrace : WordTrace (prefixWord ++ tailWord_5052918) baseStart_5052918 baseEnd_5052918 := by
    simpa [prefixWord, tailWord_5052918, baseEnd_5052918] using wordTrace_append hprefix tailTrace_5052918
  have hstable : (prefixWord ++ tailWord_5052918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052918).length < 2 ^ (prefixWord ++ tailWord_5052918).sum := by decide
  have hdescent : baseEnd_5052918 < baseStart_5052918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052982 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_5052982 : Nat := 118140960795 + 5052982 * 2 ^ 59
def prefixEnd_5052982 : Nat := 4983230072969 + 3 ^ 40 * 5052982 * 2
def baseEnd_5052982 : Nat := 2594608504517054418386765

theorem tailTrace_5052982 : CollatzResearch.WordTrace tailWord_5052982 prefixEnd_5052982 2594608504517054418386765 := by
  unfold tailWord_5052982
  simp only [CollatzResearch.WordTrace]
  refine ⟨11518587136244791841582075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122864929453277779643542133 11518587136244791841582075)
  ·
    refine ⟨17277880704367187762373113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11518587136244791841582075 17277880704367187762373113)
    ·
      refine ⟨12958410528275390821779835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17277880704367187762373113 12958410528275390821779835)
      ·
        refine ⟨19437615792413086232669753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12958410528275390821779835 19437615792413086232669753)
        ·
          refine ⟨14578211844309814674502315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19437615792413086232669753 14578211844309814674502315)
          ·
            refine ⟨21867317766464722011753473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14578211844309814674502315 21867317766464722011753473)
            ·
              refine ⟨16400488324848541508815105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21867317766464722011753473 16400488324848541508815105)
              ·
                refine ⟨12300366243636406131611329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16400488324848541508815105 12300366243636406131611329)
                ·
                  refine ⟨9225274682727304598708497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12300366243636406131611329 9225274682727304598708497)
                  ·
                    refine ⟨6918956012045478449031373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9225274682727304598708497 6918956012045478449031373)
                    ·
                      refine ⟨2594608504517054418386765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6918956012045478449031373 2594608504517054418386765)
                      ·
                        rfl

theorem cell23_5052982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_5052982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052982 prefixEnd_5052982 := by exact prefixLift 5052982
  have htrace : WordTrace (prefixWord ++ tailWord_5052982) baseStart_5052982 baseEnd_5052982 := by
    simpa [prefixWord, tailWord_5052982, baseEnd_5052982] using wordTrace_append hprefix tailTrace_5052982
  have hstable : (prefixWord ++ tailWord_5052982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052982).length < 2 ^ (prefixWord ++ tailWord_5052982).sum := by decide
  have hdescent : baseEnd_5052982 < baseStart_5052982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052989 : List Nat := [1, 4, 1, 3, 2, 1, 4, 2, 1, 4]
def baseStart_5052989 : Nat := 118140960795 + 5052989 * 2 ^ 59
def prefixEnd_5052989 : Nat := 4983230072969 + 3 ^ 40 * 5052989 * 2
def baseEnd_5052989 : Nat := 864870699627211963666411

theorem tailTrace_5052989 : CollatzResearch.WordTrace tailWord_5052989 prefixEnd_5052989 864870699627211963666411 := by
  unfold tailWord_5052989
  simp only [CollatzResearch.WordTrace]
  refine ⟨184297649490891309660818021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122865099660594206440545347 184297649490891309660818021)
  ·
    refine ⟨34555809279542120561403379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184297649490891309660818021 34555809279542120561403379)
    ·
      refine ⟨51833713919313180842105069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34555809279542120561403379 51833713919313180842105069)
      ·
        refine ⟨19437642719742442815789401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51833713919313180842105069 19437642719742442815789401)
        ·
          refine ⟨14578232039806832111842051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19437642719742442815789401 14578232039806832111842051)
          ·
            refine ⟨21867348059710248167763077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14578232039806832111842051 21867348059710248167763077)
            ·
              refine ⟨4100127761195671531455577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21867348059710248167763077 4100127761195671531455577)
              ·
                refine ⟨3075095820896753648591683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4100127761195671531455577 3075095820896753648591683)
                ·
                  refine ⟨4612643731345130472887525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3075095820896753648591683 4612643731345130472887525)
                  ·
                    refine ⟨864870699627211963666411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4612643731345130472887525 864870699627211963666411)
                    ·
                      rfl

theorem cell23_5052989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_5052989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052989 prefixEnd_5052989 := by exact prefixLift 5052989
  have htrace : WordTrace (prefixWord ++ tailWord_5052989) baseStart_5052989 baseEnd_5052989 := by
    simpa [prefixWord, tailWord_5052989, baseEnd_5052989] using wordTrace_append hprefix tailTrace_5052989
  have hstable : (prefixWord ++ tailWord_5052989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052989).length < 2 ^ (prefixWord ++ tailWord_5052989).sum := by decide
  have hdescent : baseEnd_5052989 < baseStart_5052989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5052996 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_5052996 : Nat := 118140960795 + 5052996 * 2 ^ 59
def prefixEnd_5052996 : Nat := 4983230072969 + 3 ^ 40 * 5052996 * 2
def baseEnd_5052996 : Nat := 2594615693246217363611701

theorem tailTrace_5052996 : CollatzResearch.WordTrace tailWord_5052996 prefixEnd_5052996 2594615693246217363611701 := by
  unfold tailWord_5052996
  simp only [CollatzResearch.WordTrace]
  refine ⟨92148952400932974928161421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122865269867910633237548561 92148952400932974928161421)
  ·
    refine ⟨34555857150349865598060533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92148952400932974928161421 34555857150349865598060533)
    ·
      refine ⟨3239611607845299899818175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34555857150349865598060533 3239611607845299899818175)
      ·
        refine ⟨4859417411767949849727263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3239611607845299899818175 4859417411767949849727263)
        ·
          refine ⟨7289126117651924774590895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4859417411767949849727263 7289126117651924774590895)
          ·
            refine ⟨10933689176477887161886343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7289126117651924774590895 10933689176477887161886343)
            ·
              refine ⟨16400533764716830742829515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10933689176477887161886343 16400533764716830742829515)
              ·
                refine ⟨24600800647075246114244273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16400533764716830742829515 24600800647075246114244273)
                ·
                  refine ⟨18450600485306434585683205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24600800647075246114244273 18450600485306434585683205)
                  ·
                    refine ⟨3459487590994956484815601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18450600485306434585683205 3459487590994956484815601)
                    ·
                      refine ⟨2594615693246217363611701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3459487590994956484815601 2594615693246217363611701)
                      ·
                        rfl

theorem cell23_5052996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_5052996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5052996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5052996 prefixEnd_5052996 := by exact prefixLift 5052996
  have htrace : WordTrace (prefixWord ++ tailWord_5052996) baseStart_5052996 baseEnd_5052996 := by
    simpa [prefixWord, tailWord_5052996, baseEnd_5052996] using wordTrace_append hprefix tailTrace_5052996
  have hstable : (prefixWord ++ tailWord_5052996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5052996).length < 2 ^ (prefixWord ++ tailWord_5052996).sum := by decide
  have hdescent : baseEnd_5052996 < baseStart_5052996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5052996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053012 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_5053012 : Nat := 118140960795 + 5053012 * 2 ^ 59
def prefixEnd_5053012 : Nat := 4983230072969 + 3 ^ 40 * 5053012 * 2
def baseEnd_5053012 : Nat := 2594623908936689301011627

theorem tailTrace_5053012 : CollatzResearch.WordTrace tailWord_5053012 prefixEnd_5053012 2594623908936689301011627 := by
  unfold tailWord_5053012
  simp only [CollatzResearch.WordTrace]
  refine ⟨92149244184903992294452645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122865658913205323059270193 92149244184903992294452645)
  ·
    refine ⟨17277983284669498555209871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92149244184903992294452645 17277983284669498555209871)
    ·
      refine ⟨25916974927004247832814807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17277983284669498555209871 25916974927004247832814807)
      ·
        refine ⟨38875462390506371749222211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25916974927004247832814807 38875462390506371749222211)
        ·
          refine ⟨58313193585759557623833317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38875462390506371749222211 58313193585759557623833317)
          ·
            refine ⟨10933723797329917054468747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58313193585759557623833317 10933723797329917054468747)
            ·
              refine ⟨16400585695994875581703121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10933723797329917054468747 16400585695994875581703121)
              ·
                refine ⟨12300439271996156686277341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16400585695994875581703121 12300439271996156686277341)
                ·
                  refine ⟨4612664726998558757354003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12300439271996156686277341 4612664726998558757354003)
                  ·
                    refine ⟨6918997090497838136031005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4612664726998558757354003 6918997090497838136031005)
                    ·
                      refine ⟨2594623908936689301011627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6918997090497838136031005 2594623908936689301011627)
                      ·
                        rfl

theorem cell23_5053012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_5053012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053012 prefixEnd_5053012 := by exact prefixLift 5053012
  have htrace : WordTrace (prefixWord ++ tailWord_5053012) baseStart_5053012 baseEnd_5053012 := by
    simpa [prefixWord, tailWord_5053012, baseEnd_5053012] using wordTrace_append hprefix tailTrace_5053012
  have hstable : (prefixWord ++ tailWord_5053012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053012).length < 2 ^ (prefixWord ++ tailWord_5053012).sum := by decide
  have hdescent : baseEnd_5053012 < baseStart_5053012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053028 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 1, 6]
def baseStart_5053028 : Nat := 118140960795 + 5053028 * 2 ^ 59
def prefixEnd_5053028 : Nat := 4983230072969 + 3 ^ 40 * 5053028 * 2
def baseEnd_5053028 : Nat := 864877374875720412803851

theorem tailTrace_5053028 : CollatzResearch.WordTrace tailWord_5053028 prefixEnd_5053028 864877374875720412803851 := by
  unfold tailWord_5053028
  simp only [CollatzResearch.WordTrace]
  refine ⟨92149535968875009660743869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122866047958500012880991825 92149535968875009660743869)
  ·
    refine ⟨34556075988328128622778951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92149535968875009660743869 34556075988328128622778951)
    ·
      refine ⟨51834113982492192934168427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34556075988328128622778951 51834113982492192934168427)
      ·
        refine ⟨77751170973738289401252641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51834113982492192934168427 77751170973738289401252641)
        ·
          refine ⟨58313378230303717050939481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77751170973738289401252641 58313378230303717050939481)
          ·
            refine ⟨43735033672727787788204611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58313378230303717050939481 43735033672727787788204611)
            ·
              refine ⟨65602550509091681682306917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43735033672727787788204611 65602550509091681682306917)
              ·
                refine ⟨12300478220454690315432547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65602550509091681682306917 12300478220454690315432547)
                ·
                  refine ⟨18450717330682035473148821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12300478220454690315432547 18450717330682035473148821)
                  ·
                    refine ⟨864877374875720412803851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18450717330682035473148821 864877374875720412803851)
                    ·
                      rfl

theorem cell23_5053028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_5053028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053028 prefixEnd_5053028 := by exact prefixLift 5053028
  have htrace : WordTrace (prefixWord ++ tailWord_5053028) baseStart_5053028 baseEnd_5053028 := by
    simpa [prefixWord, tailWord_5053028, baseEnd_5053028] using wordTrace_append hprefix tailTrace_5053028
  have hstable : (prefixWord ++ tailWord_5053028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053028).length < 2 ^ (prefixWord ++ tailWord_5053028).sum := by decide
  have hdescent : baseEnd_5053028 < baseStart_5053028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053032 : List Nat := [2, 1, 4, 3, 2, 1, 1, 3, 1, 5]
def baseStart_5053032 : Nat := 118140960795 + 5053032 * 2 ^ 59
def prefixEnd_5053032 : Nat := 4983230072969 + 3 ^ 40 * 5053032 * 2
def baseEnd_5053032 : Nat := 864878059516593074253845

theorem tailTrace_5053032 : CollatzResearch.WordTrace tailWord_5053032 prefixEnd_5053032 864878059516593074253845 := by
  unfold tailWord_5053032
  simp only [CollatzResearch.WordTrace]
  refine ⟨92149608914867764002316675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122866145219823685336422233 92149608914867764002316675)
  ·
    refine ⟨138224413372301646003475013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92149608914867764002316675 138224413372301646003475013)
    ·
      refine ⟨25917077507306558625651565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138224413372301646003475013 25917077507306558625651565)
      ·
        refine ⟨9718904065239959484619337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25917077507306558625651565 9718904065239959484619337)
        ·
          refine ⟨7289178048929969613464503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9718904065239959484619337 7289178048929969613464503)
          ·
            refine ⟨10933767073394954420196755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7289178048929969613464503 10933767073394954420196755)
            ·
              refine ⟨16400650610092431630295133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10933767073394954420196755 16400650610092431630295133)
              ·
                refine ⟨6150243978784661861360675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16400650610092431630295133 6150243978784661861360675)
                ·
                  refine ⟨9225365968176992792041013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6150243978784661861360675 9225365968176992792041013)
                  ·
                    refine ⟨864878059516593074253845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9225365968176992792041013 864878059516593074253845)
                    ·
                      rfl

theorem cell23_5053032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_5053032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053032 prefixEnd_5053032 := by exact prefixLift 5053032
  have htrace : WordTrace (prefixWord ++ tailWord_5053032) baseStart_5053032 baseEnd_5053032 := by
    simpa [prefixWord, tailWord_5053032, baseEnd_5053032] using wordTrace_append hprefix tailTrace_5053032
  have hstable : (prefixWord ++ tailWord_5053032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053032).length < 2 ^ (prefixWord ++ tailWord_5053032).sum := by decide
  have hdescent : baseEnd_5053032 < baseStart_5053032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053052 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 3, 2, 2]
def baseStart_5053052 : Nat := 118140960795 + 5053052 * 2 ^ 59
def prefixEnd_5053052 : Nat := 4983230072969 + 3 ^ 40 * 5053052 * 2
def baseEnd_5053052 : Nat := 2594644448162869144511443

theorem tailTrace_5053052 : CollatzResearch.WordTrace tailWord_5053052 prefixEnd_5053052 2594644448162869144511443 := by
  unfold tailWord_5053052
  simp only [CollatzResearch.WordTrace]
  refine ⟨92149973644831535710180705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122866631526442047613574273 92149973644831535710180705)
  ·
    refine ⟨69112480233623651782635529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92149973644831535710180705 69112480233623651782635529)
    ·
      refine ⟨51834360175217738836976647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69112480233623651782635529 51834360175217738836976647)
      ·
        refine ⟨77751540262826608255464971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51834360175217738836976647 77751540262826608255464971)
        ·
          refine ⟨116627310394239912383197457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77751540262826608255464971 116627310394239912383197457)
          ·
            refine ⟨87470482795679934287398093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116627310394239912383197457 87470482795679934287398093)
            ·
              refine ⟨32801431048379975357774285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87470482795679934287398093 32801431048379975357774285)
              ·
                refine ⟨12300536643142490759165357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32801431048379975357774285 12300536643142490759165357)
                ·
                  refine ⟨4612701241178434034687009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12300536643142490759165357 4612701241178434034687009)
                  ·
                    refine ⟨3459525930883825526015257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4612701241178434034687009 3459525930883825526015257)
                    ·
                      refine ⟨2594644448162869144511443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3459525930883825526015257 2594644448162869144511443)
                      ·
                        rfl

theorem cell23_5053052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_5053052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053052 prefixEnd_5053052 := by exact prefixLift 5053052
  have htrace : WordTrace (prefixWord ++ tailWord_5053052) baseStart_5053052 baseEnd_5053052 := by
    simpa [prefixWord, tailWord_5053052, baseEnd_5053052] using wordTrace_append hprefix tailTrace_5053052
  have hstable : (prefixWord ++ tailWord_5053052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053052).length < 2 ^ (prefixWord ++ tailWord_5053052).sum := by decide
  have hdescent : baseEnd_5053052 < baseStart_5053052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053085 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_5053085 : Nat := 118140960795 + 5053085 * 2 ^ 59
def prefixEnd_5053085 : Nat := 4983230072969 + 3 ^ 40 * 5053085 * 2
def baseEnd_5053085 : Nat := 2594661393024467515398791

theorem tailTrace_5053085 : CollatzResearch.WordTrace tailWord_5053085 prefixEnd_5053085 2594661393024467515398791 := by
  unfold tailWord_5053085
  simp only [CollatzResearch.WordTrace]
  refine ⟨184301150898543518056312709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122867433932362345370875139 184301150898543518056312709)
  ·
    refine ⟨34556465793476909635558633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184301150898543518056312709 34556465793476909635558633)
    ·
      refine ⟨25917349345107682226668975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34556465793476909635558633 25917349345107682226668975)
      ·
        refine ⟨38876024017661523340003463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25917349345107682226668975 38876024017661523340003463)
        ·
          refine ⟨58314036026492285010005195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38876024017661523340003463 58314036026492285010005195)
          ·
            refine ⟨87471054039738427515007793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58314036026492285010005195 87471054039738427515007793)
            ·
              refine ⟨65603290529803820636255845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87471054039738427515007793 65603290529803820636255845)
              ·
                refine ⟨12300616974338216369297971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65603290529803820636255845 12300616974338216369297971)
                ·
                  refine ⟨18450925461507324553946957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12300616974338216369297971 18450925461507324553946957)
                  ·
                    refine ⟨6919097048065246707730109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18450925461507324553946957 6919097048065246707730109)
                    ·
                      refine ⟨2594661393024467515398791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6919097048065246707730109 2594661393024467515398791)
                      ·
                        rfl

theorem cell23_5053085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_5053085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053085 prefixEnd_5053085 := by exact prefixLift 5053085
  have htrace : WordTrace (prefixWord ++ tailWord_5053085) baseStart_5053085 baseEnd_5053085 := by
    simpa [prefixWord, tailWord_5053085, baseEnd_5053085] using wordTrace_append hprefix tailTrace_5053085
  have hstable : (prefixWord ++ tailWord_5053085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053085).length < 2 ^ (prefixWord ++ tailWord_5053085).sum := by decide
  have hdescent : baseEnd_5053085 < baseStart_5053085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053119 : List Nat := [1, 1, 2, 2, 2, 4, 4, 1, 2, 1, 3]
def baseStart_5053119 : Nat := 118140960795 + 5053119 * 2 ^ 59
def prefixEnd_5053119 : Nat := 4983230072969 + 3 ^ 40 * 5053119 * 2
def baseEnd_5053119 : Nat := 2594678851366720382373635

theorem tailTrace_5053119 : CollatzResearch.WordTrace tailWord_5053119 prefixEnd_5053119 2594678851366720382373635 := by
  unfold tailWord_5053119
  simp only [CollatzResearch.WordTrace]
  refine ⟨184302390980420341863050411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122868260653613561242033607 184302390980420341863050411)
  ·
    refine ⟨276453586470630512794575617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184302390980420341863050411 276453586470630512794575617)
    ·
      refine ⟨207340189852972884595931713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276453586470630512794575617 207340189852972884595931713)
      ·
        refine ⟨155505142389729663446948785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207340189852972884595931713 155505142389729663446948785)
        ·
          refine ⟨116628856792297247585211589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155505142389729663446948785 116628856792297247585211589)
          ·
            refine ⟨21867910648555733922227173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116628856792297247585211589 21867910648555733922227173)
            ·
              refine ⟨4100233246604200110417595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21867910648555733922227173 4100233246604200110417595)
              ·
                refine ⟨6150349869906300165626393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4100233246604200110417595 6150349869906300165626393)
                ·
                  refine ⟨4612762402429725124219795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6150349869906300165626393 4612762402429725124219795)
                  ·
                    refine ⟨6919143603644587686329693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4612762402429725124219795 6919143603644587686329693)
                    ·
                      refine ⟨2594678851366720382373635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6919143603644587686329693 2594678851366720382373635)
                      ·
                        rfl

theorem cell23_5053119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 2, 1, 3].length) (baseStart_5053119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053119 prefixEnd_5053119 := by exact prefixLift 5053119
  have htrace : WordTrace (prefixWord ++ tailWord_5053119) baseStart_5053119 baseEnd_5053119 := by
    simpa [prefixWord, tailWord_5053119, baseEnd_5053119] using wordTrace_append hprefix tailTrace_5053119
  have hstable : (prefixWord ++ tailWord_5053119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053119).length < 2 ^ (prefixWord ++ tailWord_5053119).sum := by decide
  have hdescent : baseEnd_5053119 < baseStart_5053119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053165 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 7]
def baseStart_5053165 : Nat := 118140960795 + 5053165 * 2 ^ 59
def prefixEnd_5053165 : Nat := 4983230072969 + 3 ^ 40 * 5053165 * 2
def baseEnd_5053165 : Nat := 288300274608536355822047

theorem tailTrace_5053165 : CollatzResearch.WordTrace tailWord_5053165 prefixEnd_5053165 288300274608536355822047 := by
  unfold tailWord_5053165
  simp only [CollatzResearch.WordTrace]
  refine ⟨184304068738253691719224949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122869379158835794479483299 184304068738253691719224949)
  ·
    refine ⟨17278506444211283598677339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184304068738253691719224949 17278506444211283598677339)
    ·
      refine ⟨25917759666316925398016009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17278506444211283598677339 25917759666316925398016009)
      ·
        refine ⟨19438319749737694048512007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25917759666316925398016009 19438319749737694048512007)
        ·
          refine ⟨29157479624606541072768011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19438319749737694048512007 29157479624606541072768011)
          ·
            refine ⟨43736219436909811609152017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29157479624606541072768011 43736219436909811609152017)
            ·
              refine ⟨32802164577682358706864013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43736219436909811609152017 32802164577682358706864013)
              ·
                refine ⟨12300811716630884515074005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32802164577682358706864013 12300811716630884515074005)
                ·
                  refine ⟨288300274608536355822047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12300811716630884515074005 288300274608536355822047)
                  ·
                    rfl

theorem cell23_5053165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_5053165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053165 prefixEnd_5053165 := by exact prefixLift 5053165
  have htrace : WordTrace (prefixWord ++ tailWord_5053165) baseStart_5053165 baseEnd_5053165 := by
    simpa [prefixWord, tailWord_5053165, baseEnd_5053165] using wordTrace_append hprefix tailTrace_5053165
  have hstable : (prefixWord ++ tailWord_5053165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053165).length < 2 ^ (prefixWord ++ tailWord_5053165).sum := by decide
  have hdescent : baseEnd_5053165 < baseStart_5053165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053182 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 7]
def baseStart_5053182 : Nat := 118140960795 + 5053182 * 2 ^ 59
def prefixEnd_5053182 : Nat := 4983230072969 + 3 ^ 40 * 5053182 * 2
def baseEnd_5053182 : Nat := 288301244516439292876205

theorem tailTrace_5053182 : CollatzResearch.WordTrace tailWord_5053182 prefixEnd_5053182 288301244516439292876205 := by
  unfold tailWord_5053182
  simp only [CollatzResearch.WordTrace]
  refine ⟨23038086097399012952824225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122869792519461402415062533 23038086097399012952824225)
  ·
    refine ⟨17278564573049259714618169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23038086097399012952824225 17278564573049259714618169)
    ·
      refine ⟨12958923429786944785963627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17278564573049259714618169 12958923429786944785963627)
      ·
        refine ⟨19438385144680417178945441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12958923429786944785963627 19438385144680417178945441)
        ·
          refine ⟨14578788858510312884209081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19438385144680417178945441 14578788858510312884209081)
          ·
            refine ⟨10934091643882734663156811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14578788858510312884209081 10934091643882734663156811)
            ·
              refine ⟨16401137465824101994735217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10934091643882734663156811 16401137465824101994735217)
              ·
                refine ⟨12300853099368076496051413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16401137465824101994735217 12300853099368076496051413)
                ·
                  refine ⟨288301244516439292876205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12300853099368076496051413 288301244516439292876205)
                  ·
                    rfl

theorem cell23_5053182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_5053182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053182 prefixEnd_5053182 := by exact prefixLift 5053182
  have htrace : WordTrace (prefixWord ++ tailWord_5053182) baseStart_5053182 baseEnd_5053182 := by
    simpa [prefixWord, tailWord_5053182, baseEnd_5053182] using wordTrace_append hprefix tailTrace_5053182
  have hstable : (prefixWord ++ tailWord_5053182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053182).length < 2 ^ (prefixWord ++ tailWord_5053182).sum := by decide
  have hdescent : baseEnd_5053182 < baseStart_5053182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053225 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 7, 4]
def baseStart_5053225 : Nat := 118140960795 + 5053225 * 2 ^ 59
def prefixEnd_5053225 : Nat := 4983230072969 + 3 ^ 40 * 5053225 * 2
def baseEnd_5053225 : Nat := 864911093438698989216049

theorem tailTrace_5053225 : CollatzResearch.WordTrace tailWord_5053225 prefixEnd_5053225 864911093438698989216049 := by
  unfold tailWord_5053225
  simp only [CollatzResearch.WordTrace]
  refine ⟨184306257118036321966409129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122870838078690881310939419 184306257118036321966409129)
  ·
    refine ⟨138229692838527241474806847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184306257118036321966409129 138229692838527241474806847)
    ·
      refine ⟨207344539257790862212210271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138229692838527241474806847 207344539257790862212210271)
      ·
        refine ⟨311016808886686293318315407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207344539257790862212210271 311016808886686293318315407)
        ·
          refine ⟨466525213330029439977473111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311016808886686293318315407 466525213330029439977473111)
          ·
            refine ⟨699787819995044159966209667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466525213330029439977473111 699787819995044159966209667)
            ·
              refine ⟨1049681729992566239949314501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699787819995044159966209667 1049681729992566239949314501)
              ·
                refine ⟨196815324373606169990496469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1049681729992566239949314501 196815324373606169990496469)
                ·
                  refine ⟨4612859165006394609152261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 196815324373606169990496469 4612859165006394609152261)
                  ·
                    refine ⟨864911093438698989216049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4612859165006394609152261 864911093438698989216049)
                    ·
                      rfl

theorem cell23_5053225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 4].length) (baseStart_5053225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053225 prefixEnd_5053225 := by exact prefixLift 5053225
  have htrace : WordTrace (prefixWord ++ tailWord_5053225) baseStart_5053225 baseEnd_5053225 := by
    simpa [prefixWord, tailWord_5053225, baseEnd_5053225] using wordTrace_append hprefix tailTrace_5053225
  have hstable : (prefixWord ++ tailWord_5053225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053225).length < 2 ^ (prefixWord ++ tailWord_5053225).sum := by decide
  have hdescent : baseEnd_5053225 < baseStart_5053225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053276 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 3, 4]
def baseStart_5053276 : Nat := 118140960795 + 5053276 * 2 ^ 59
def prefixEnd_5053276 : Nat := 4983230072969 + 3 ^ 40 * 5053276 * 2
def baseEnd_5053276 : Nat := 864919822609825422703471

theorem tailTrace_5053276 : CollatzResearch.WordTrace tailWord_5053276 prefixEnd_5053276 864919822609825422703471 := by
  unfold tailWord_5053276
  simp only [CollatzResearch.WordTrace]
  refine ⟨92154058620425778838257841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122872078160567705117677121 92154058620425778838257841)
  ·
    refine ⟨69115543965319334128693381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92154058620425778838257841 69115543965319334128693381)
    ·
      refine ⟨12959164493497375149130009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69115543965319334128693381 12959164493497375149130009)
      ·
        refine ⟨9719373370123031361847507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12959164493497375149130009 9719373370123031361847507)
        ·
          refine ⟨14579060055184547042771261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9719373370123031361847507 14579060055184547042771261)
          ·
            refine ⟨5467147520694205141039223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14579060055184547042771261 5467147520694205141039223)
            ·
              refine ⟨8200721281041307711558835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5467147520694205141039223 8200721281041307711558835)
              ·
                refine ⟨12301081921561961567338253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8200721281041307711558835 12301081921561961567338253)
                ·
                  refine ⟨4612905720585735587751845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12301081921561961567338253 4612905720585735587751845)
                  ·
                    refine ⟨864919822609825422703471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4612905720585735587751845 864919822609825422703471)
                    ·
                      rfl

theorem cell23_5053276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_5053276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053276 prefixEnd_5053276 := by exact prefixLift 5053276
  have htrace : WordTrace (prefixWord ++ tailWord_5053276) baseStart_5053276 baseEnd_5053276 := by
    simpa [prefixWord, tailWord_5053276, baseEnd_5053276] using wordTrace_append hprefix tailTrace_5053276
  have hstable : (prefixWord ++ tailWord_5053276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053276).length < 2 ^ (prefixWord ++ tailWord_5053276).sum := by decide
  have hdescent : baseEnd_5053276 < baseStart_5053276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053309 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 2, 3, 2]
def baseStart_5053309 : Nat := 118140960795 + 5053309 * 2 ^ 59
def prefixEnd_5053309 : Nat := 4983230072969 + 3 ^ 40 * 5053309 * 2
def baseEnd_5053309 : Nat := 2594776412691074638997761

theorem tailTrace_5053309 : CollatzResearch.WordTrace tailWord_5053309 prefixEnd_5053309 2594776412691074638997761 := by
  unfold tailWord_5053309
  simp only [CollatzResearch.WordTrace]
  refine ⟨184309320849732004312466981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122872880566488002874977987 184309320849732004312466981)
  ·
    refine ⟨34557997659324750808587559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184309320849732004312466981 34557997659324750808587559)
    ·
      refine ⟨51836996488987126212881339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34557997659324750808587559 51836996488987126212881339)
      ·
        refine ⟨77755494733480689319322009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51836996488987126212881339 77755494733480689319322009)
        ·
          refine ⟨58316621050110516989491507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77755494733480689319322009 58316621050110516989491507)
          ·
            refine ⟨87474931575165775484237261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58316621050110516989491507 87474931575165775484237261)
            ·
              refine ⟨32803099340687165806588973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87474931575165775484237261 32803099340687165806588973)
              ·
                refine ⟨12301162252757687177470865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32803099340687165806588973 12301162252757687177470865)
                ·
                  refine ⟨9225871689568265383103149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12301162252757687177470865 9225871689568265383103149)
                  ·
                    refine ⟨3459701883588099518663681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9225871689568265383103149 3459701883588099518663681)
                    ·
                      refine ⟨2594776412691074638997761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3459701883588099518663681 2594776412691074638997761)
                      ·
                        rfl

theorem cell23_5053309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_5053309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053309 prefixEnd_5053309 := by exact prefixLift 5053309
  have htrace : WordTrace (prefixWord ++ tailWord_5053309) baseStart_5053309 baseEnd_5053309 := by
    simpa [prefixWord, tailWord_5053309, baseEnd_5053309] using wordTrace_append hprefix tailTrace_5053309
  have hstable : (prefixWord ++ tailWord_5053309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053309).length < 2 ^ (prefixWord ++ tailWord_5053309).sum := by decide
  have hdescent : baseEnd_5053309 < baseStart_5053309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053316 : List Nat := [2, 3, 2, 1, 1, 1, 1, 7, 1, 1, 3]
def baseStart_5053316 : Nat := 118140960795 + 5053316 * 2 ^ 59
def prefixEnd_5053316 : Nat := 4983230072969 + 3 ^ 40 * 5053316 * 2
def baseEnd_5053316 : Nat := 2594780007055656111610229

theorem tailTrace_5053316 : CollatzResearch.WordTrace tailWord_5053316 prefixEnd_5053316 2594780007055656111610229 := by
  unfold tailWord_5053316
  simp only [CollatzResearch.WordTrace]
  refine ⟨92154788080353322253985901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122873050773804429671981201 92154788080353322253985901)
  ·
    refine ⟨34558045530132495845244713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92154788080353322253985901 34558045530132495845244713)
    ·
      refine ⟨25918534147599371883933535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34558045530132495845244713 25918534147599371883933535)
      ·
        refine ⟨38877801221399057825900303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25918534147599371883933535 38877801221399057825900303)
        ·
          refine ⟨58316701832098586738850455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38877801221399057825900303 58316701832098586738850455)
          ·
            refine ⟨87475052748147880108275683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58316701832098586738850455 87475052748147880108275683)
            ·
              refine ⟨131212579122221820162413525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87475052748147880108275683 131212579122221820162413525)
              ·
                refine ⟨3075294823177073910056567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 131212579122221820162413525 3075294823177073910056567)
                ·
                  refine ⟨4612942234765610865084851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3075294823177073910056567 4612942234765610865084851)
                  ·
                    refine ⟨6919413352148416297627277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4612942234765610865084851 6919413352148416297627277)
                    ·
                      refine ⟨2594780007055656111610229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6919413352148416297627277 2594780007055656111610229)
                      ·
                        rfl

theorem cell23_5053316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_5053316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053316 prefixEnd_5053316 := by exact prefixLift 5053316
  have htrace : WordTrace (prefixWord ++ tailWord_5053316) baseStart_5053316 baseEnd_5053316 := by
    simpa [prefixWord, tailWord_5053316, baseEnd_5053316] using wordTrace_append hprefix tailTrace_5053316
  have hstable : (prefixWord ++ tailWord_5053316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053316).length < 2 ^ (prefixWord ++ tailWord_5053316).sum := by decide
  have hdescent : baseEnd_5053316 < baseStart_5053316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053332 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_5053332 : Nat := 118140960795 + 5053332 * 2 ^ 59
def prefixEnd_5053332 : Nat := 4983230072969 + 3 ^ 40 * 5053332 * 2
def baseEnd_5053332 : Nat := 864929407582042683003385

theorem tailTrace_5053332 : CollatzResearch.WordTrace tailWord_5053332 prefixEnd_5053332 864929407582042683003385 := by
  unfold tailWord_5053332
  simp only [CollatzResearch.WordTrace]
  refine ⟨92155079864324339620277125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122873439819099119493702833 92155079864324339620277125)
  ·
    refine ⟨17279077474560813678801961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92155079864324339620277125 17279077474560813678801961)
    ·
      refine ⟨12959308105920610259101471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17279077474560813678801961 12959308105920610259101471)
      ·
        refine ⟨19438962158880915388652207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12959308105920610259101471 19438962158880915388652207)
        ·
          refine ⟨29158443238321373082978311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19438962158880915388652207 29158443238321373082978311)
          ·
            refine ⟨43737664857482059624467467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29158443238321373082978311 43737664857482059624467467)
            ·
              refine ⟨65606497286223089436701201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43737664857482059624467467 65606497286223089436701201)
              ·
                refine ⟨49204872964667317077525901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65606497286223089436701201 49204872964667317077525901)
                ·
                  refine ⟨18451827361750243904072213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49204872964667317077525901 18451827361750243904072213)
                  ·
                    refine ⟨864929407582042683003385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18451827361750243904072213 864929407582042683003385)
                    ·
                      rfl

theorem cell23_5053332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_5053332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053332 prefixEnd_5053332 := by exact prefixLift 5053332
  have htrace : WordTrace (prefixWord ++ tailWord_5053332) baseStart_5053332 baseEnd_5053332 := by
    simpa [prefixWord, tailWord_5053332, baseEnd_5053332] using wordTrace_append hprefix tailTrace_5053332
  have hstable : (prefixWord ++ tailWord_5053332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053332).length < 2 ^ (prefixWord ++ tailWord_5053332).sum := by decide
  have hdescent : baseEnd_5053332 < baseStart_5053332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053333 : List Nat := [1, 3, 2, 1, 1, 4, 4, 2, 1, 1, 3]
def baseStart_5053333 : Nat := 118140960795 + 5053333 * 2 ^ 59
def prefixEnd_5053333 : Nat := 4983230072969 + 3 ^ 40 * 5053333 * 2
def baseEnd_5053333 : Nat := 2594788736226782545097651

theorem tailTrace_5053333 : CollatzResearch.WordTrace tailWord_5053333 prefixEnd_5053333 2594788736226782545097651 := by
  unfold tailWord_5053333
  simp only [CollatzResearch.WordTrace]
  refine ⟨184310196201645056411340653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122873464134430037607560435 184310196201645056411340653)
  ·
    refine ⟨69116323575616896154252745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184310196201645056411340653 69116323575616896154252745)
    ·
      refine ⟨51837242681712672115689559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69116323575616896154252745 51837242681712672115689559)
      ·
        refine ⟨77755864022569008173534339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51837242681712672115689559 77755864022569008173534339)
        ·
          refine ⟨116633796033853512260301509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77755864022569008173534339 116633796033853512260301509)
          ·
            refine ⟨21868836756347533548806533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116633796033853512260301509 21868836756347533548806533)
            ·
              refine ⟨4100406891815162540401225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21868836756347533548806533 4100406891815162540401225)
              ·
                refine ⟨3075305168861371905300919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4100406891815162540401225 3075305168861371905300919)
                ·
                  refine ⟨4612957753292057857951379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3075305168861371905300919 4612957753292057857951379)
                  ·
                    refine ⟨6919436629938086786927069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4612957753292057857951379 6919436629938086786927069)
                    ·
                      refine ⟨2594788736226782545097651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6919436629938086786927069 2594788736226782545097651)
                      ·
                        rfl

theorem cell23_5053333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_5053333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053333 prefixEnd_5053333 := by exact prefixLift 5053333
  have htrace : WordTrace (prefixWord ++ tailWord_5053333) baseStart_5053333 baseEnd_5053333 := by
    simpa [prefixWord, tailWord_5053333, baseEnd_5053333] using wordTrace_append hprefix tailTrace_5053333
  have hstable : (prefixWord ++ tailWord_5053333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053333).length < 2 ^ (prefixWord ++ tailWord_5053333).sum := by decide
  have hdescent : baseEnd_5053333 < baseStart_5053333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053373 : List Nat := [1, 4, 1, 2, 4, 2, 2, 1, 1, 1, 4]
def baseStart_5053373 : Nat := 118140960795 + 5053373 * 2 ^ 59
def prefixEnd_5053373 : Nat := 4983230072969 + 3 ^ 40 * 5053373 * 2
def baseEnd_5053373 : Nat := 2594809275452962388597467

theorem tailTrace_5053373 : CollatzResearch.WordTrace tailWord_5053373 prefixEnd_5053373 2594809275452962388597467 := by
  unfold tailWord_5053373
  simp only [CollatzResearch.WordTrace]
  refine ⟨184311655121500143242796773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122874436747666762161864515 184311655121500143242796773)
  ·
    refine ⟨34558435335281276858024395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184311655121500143242796773 34558435335281276858024395)
    ·
      refine ⟨51837653002921915287036593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34558435335281276858024395 51837653002921915287036593)
      ·
        refine ⟨38878239752191436465277445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51837653002921915287036593 38878239752191436465277445)
        ·
          refine ⟨7289669953535894337239521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38878239752191436465277445 7289669953535894337239521)
          ·
            refine ⟨5467252465151920752929641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7289669953535894337239521 5467252465151920752929641)
            ·
              refine ⟨4100439348863940564697231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5467252465151920752929641 4100439348863940564697231)
              ·
                refine ⟨6150659023295910847045847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4100439348863940564697231 6150659023295910847045847)
                ·
                  refine ⟨9225988534943866270568771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6150659023295910847045847 9225988534943866270568771)
                  ·
                    refine ⟨13838982802415799405853157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9225988534943866270568771 13838982802415799405853157)
                    ·
                      refine ⟨2594809275452962388597467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13838982802415799405853157 2594809275452962388597467)
                      ·
                        rfl

theorem cell23_5053373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_5053373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053373 prefixEnd_5053373 := by exact prefixLift 5053373
  have htrace : WordTrace (prefixWord ++ tailWord_5053373) baseStart_5053373 baseEnd_5053373 := by
    simpa [prefixWord, tailWord_5053373, baseEnd_5053373] using wordTrace_append hprefix tailTrace_5053373
  have hstable : (prefixWord ++ tailWord_5053373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053373).length < 2 ^ (prefixWord ++ tailWord_5053373).sum := by decide
  have hdescent : baseEnd_5053373 < baseStart_5053373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053375 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 1, 9]
def baseStart_5053375 : Nat := 118140960795 + 5053375 * 2 ^ 59
def prefixEnd_5053375 : Nat := 4983230072969 + 3 ^ 40 * 5053375 * 2
def baseEnd_5053375 : Nat := 864936767471423793590819

theorem tailTrace_5053375 : CollatzResearch.WordTrace tailWord_5053375 prefixEnd_5053375 864936767471423793590819 := by
  unfold tailWord_5053375
  simp only [CollatzResearch.WordTrace]
  refine ⟨184311728067492897584369579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122874485378328598389579719 184311728067492897584369579)
  ·
    refine ⟨276467592101239346376554369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184311728067492897584369579 276467592101239346376554369)
    ·
      refine ⟨207350694075929509782415777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276467592101239346376554369 207350694075929509782415777)
      ·
        refine ⟨155513020556947132336811833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207350694075929509782415777 155513020556947132336811833)
        ·
          refine ⟨116634765417710349252608875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155513020556947132336811833 116634765417710349252608875)
          ·
            refine ⟨174952148126565523878913313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116634765417710349252608875 174952148126565523878913313)
            ·
              refine ⟨131214111094924142909184985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174952148126565523878913313 131214111094924142909184985)
              ·
                refine ⟨98410583321193107181888739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131214111094924142909184985 98410583321193107181888739)
                ·
                  refine ⟨147615874981789660772833109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98410583321193107181888739 147615874981789660772833109)
                  ·
                    refine ⟨864936767471423793590819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 147615874981789660772833109 864936767471423793590819)
                    ·
                      rfl

theorem cell23_5053375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 9].length) (baseStart_5053375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053375 prefixEnd_5053375 := by exact prefixLift 5053375
  have htrace : WordTrace (prefixWord ++ tailWord_5053375) baseStart_5053375 baseEnd_5053375 := by
    simpa [prefixWord, tailWord_5053375, baseEnd_5053375] using wordTrace_append hprefix tailTrace_5053375
  have hstable : (prefixWord ++ tailWord_5053375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053375).length < 2 ^ (prefixWord ++ tailWord_5053375).sum := by decide
  have hdescent : baseEnd_5053375 < baseStart_5053375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053376 : List Nat := [2, 1, 1, 2, 3, 3, 4, 1, 1, 2, 3]
def baseStart_5053376 : Nat := 118140960795 + 5053376 * 2 ^ 59
def prefixEnd_5053376 : Nat := 4983230072969 + 3 ^ 40 * 5053376 * 2
def baseEnd_5053376 : Nat := 2594810815894925876859953

theorem tailTrace_5053376 : CollatzResearch.WordTrace tailWord_5053376 prefixEnd_5053376 2594810815894925876859953 := by
  unfold tailWord_5053376
  simp only [CollatzResearch.WordTrace]
  refine ⟨92155882270244637377577991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122874509693659516503437321 92155882270244637377577991)
  ·
    refine ⟨138233823405366956066366987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92155882270244637377577991 138233823405366956066366987)
    ·
      refine ⟨207350735108050434099550481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138233823405366956066366987 207350735108050434099550481)
      ·
        refine ⟨155513051331037825574662861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207350735108050434099550481 155513051331037825574662861)
        ·
          refine ⟨58317394249139184590498573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155513051331037825574662861 58317394249139184590498573)
          ·
            refine ⟨21869022843427194221436965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58317394249139184590498573 21869022843427194221436965)
            ·
              refine ⟨4100441783142598916519431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21869022843427194221436965 4100441783142598916519431)
              ·
                refine ⟨6150662674713898374779147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4100441783142598916519431 6150662674713898374779147)
                ·
                  refine ⟨9225994012070847562168721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6150662674713898374779147 9225994012070847562168721)
                  ·
                    refine ⟨6919495509053135671626541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9225994012070847562168721 6919495509053135671626541)
                    ·
                      refine ⟨2594810815894925876859953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6919495509053135671626541 2594810815894925876859953)
                      ·
                        rfl

theorem cell23_5053376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 1, 2, 3].length) (baseStart_5053376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053376 prefixEnd_5053376 := by exact prefixLift 5053376
  have htrace : WordTrace (prefixWord ++ tailWord_5053376) baseStart_5053376 baseEnd_5053376 := by
    simpa [prefixWord, tailWord_5053376, baseEnd_5053376] using wordTrace_append hprefix tailTrace_5053376
  have hstable : (prefixWord ++ tailWord_5053376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053376).length < 2 ^ (prefixWord ++ tailWord_5053376).sum := by decide
  have hdescent : baseEnd_5053376 < baseStart_5053376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053385 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 7]
def baseStart_5053385 : Nat := 118140960795 + 5053385 * 2 ^ 59
def prefixEnd_5053385 : Nat := 4983230072969 + 3 ^ 40 * 5053385 * 2
def baseEnd_5053385 : Nat := 2594815437220816341647411

theorem tailTrace_5053385 : CollatzResearch.WordTrace tailWord_5053385 prefixEnd_5053385 2594815437220816341647411 := by
  unfold tailWord_5053385
  simp only [CollatzResearch.WordTrace]
  refine ⟨184312092797456669292233609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122874728531637779528155739 184312092797456669292233609)
  ·
    refine ⟨138234069598092501969175207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184312092797456669292233609 138234069598092501969175207)
    ·
      refine ⟨207351104397138752953762811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138234069598092501969175207 207351104397138752953762811)
      ·
        refine ⟨311026656595708129430644217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207351104397138752953762811 311026656595708129430644217)
        ·
          refine ⟨233269992446781097072983163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311026656595708129430644217 233269992446781097072983163)
          ·
            refine ⟨349904988670171645609474745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233269992446781097072983163 349904988670171645609474745)
            ·
              refine ⟨262428741502628734207106059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349904988670171645609474745 262428741502628734207106059)
              ·
                refine ⟨393643112253943101310659089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262428741502628734207106059 393643112253943101310659089)
                ·
                  refine ⟨295232334190457325982994317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393643112253943101310659089 295232334190457325982994317)
                  ·
                    refine ⟨110712125321421497243622869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 295232334190457325982994317 110712125321421497243622869)
                    ·
                      refine ⟨2594815437220816341647411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110712125321421497243622869 2594815437220816341647411)
                      ·
                        rfl

theorem cell23_5053385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_5053385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053385 prefixEnd_5053385 := by exact prefixLift 5053385
  have htrace : WordTrace (prefixWord ++ tailWord_5053385) baseStart_5053385 baseEnd_5053385 := by
    simpa [prefixWord, tailWord_5053385, baseEnd_5053385] using wordTrace_append hprefix tailTrace_5053385
  have hstable : (prefixWord ++ tailWord_5053385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053385).length < 2 ^ (prefixWord ++ tailWord_5053385).sum := by decide
  have hdescent : baseEnd_5053385 < baseStart_5053385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053399 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 3, 3, 2]
def baseStart_5053399 : Nat := 118140960795 + 5053399 * 2 ^ 59
def prefixEnd_5053399 : Nat := 4983230072969 + 3 ^ 40 * 5053399 * 2
def baseEnd_5053399 : Nat := 2594822625949979286872347

theorem tailTrace_5053399 : CollatzResearch.WordTrace tailWord_5053399 prefixEnd_5053399 2594822625949979286872347 := by
  unfold tailWord_5053399
  simp only [CollatzResearch.WordTrace]
  refine ⟨184312603419405949683243251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122875068946270633122162167 184312603419405949683243251)
  ·
    refine ⟨276468905129108924524864877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184312603419405949683243251 276468905129108924524864877)
    ·
      refine ⟨103675839423415846696824329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276468905129108924524864877 103675839423415846696824329)
      ·
        refine ⟨77756879567561885022618247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103675839423415846696824329 77756879567561885022618247)
        ·
          refine ⟨116635319351342827533927371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77756879567561885022618247 116635319351342827533927371)
          ·
            refine ⟨174952979027014241300891057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116635319351342827533927371 174952979027014241300891057)
            ·
              refine ⟨131214734270260680975668293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174952979027014241300891057 131214734270260680975668293)
              ·
                refine ⟨24602762675673877682937805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131214734270260680975668293 24602762675673877682937805)
                ·
                  refine ⟨9226036003377704131101677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24602762675673877682937805 9226036003377704131101677)
                  ·
                    refine ⟨3459763501266639049163129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9226036003377704131101677 3459763501266639049163129)
                    ·
                      refine ⟨2594822625949979286872347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3459763501266639049163129 2594822625949979286872347)
                      ·
                        rfl

theorem cell23_5053399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_5053399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053399 prefixEnd_5053399 := by exact prefixLift 5053399
  have htrace : WordTrace (prefixWord ++ tailWord_5053399) baseStart_5053399 baseEnd_5053399 := by
    simpa [prefixWord, tailWord_5053399, baseEnd_5053399] using wordTrace_append hprefix tailTrace_5053399
  have hstable : (prefixWord ++ tailWord_5053399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053399).length < 2 ^ (prefixWord ++ tailWord_5053399).sum := by decide
  have hdescent : baseEnd_5053399 < baseStart_5053399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053413 : List Nat := [1, 3, 1, 6, 2, 1, 2, 7]
def baseStart_5053413 : Nat := 118140960795 + 5053413 * 2 ^ 59
def prefixEnd_5053413 : Nat := 4983230072969 + 3 ^ 40 * 5053413 * 2
def baseEnd_5053413 : Nat := 96104807951079341929529

theorem tailTrace_5053413 : CollatzResearch.WordTrace tailWord_5053413 prefixEnd_5053413 96104807951079341929529 := by
  unfold tailWord_5053413
  simp only [CollatzResearch.WordTrace]
  refine ⟨184313114041355230074252893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122875409360903486716168595 184313114041355230074252893)
  ·
    refine ⟨69117417765508211277844835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184313114041355230074252893 69117417765508211277844835)
    ·
      refine ⟨103676126648262316916767253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69117417765508211277844835 103676126648262316916767253)
      ·
        refine ⟨4859818436637296105473465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 103676126648262316916767253 4859818436637296105473465)
        ·
          refine ⟨3644863827477972079105099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4859818436637296105473465 3644863827477972079105099)
          ·
            refine ⟨5467295741216958118657649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3644863827477972079105099 5467295741216958118657649)
            ·
              refine ⟨4100471805912718588993237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5467295741216958118657649 4100471805912718588993237)
              ·
                refine ⟨96104807951079341929529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4100471805912718588993237 96104807951079341929529)
                ·
                  rfl

theorem cell23_5053413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 7].length) (baseStart_5053413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053413 prefixEnd_5053413 := by exact prefixLift 5053413
  have htrace : WordTrace (prefixWord ++ tailWord_5053413) baseStart_5053413 baseEnd_5053413 := by
    simpa [prefixWord, tailWord_5053413, baseEnd_5053413] using wordTrace_append hprefix tailTrace_5053413
  have hstable : (prefixWord ++ tailWord_5053413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053413).length < 2 ^ (prefixWord ++ tailWord_5053413).sum := by decide
  have hdescent : baseEnd_5053413 < baseStart_5053413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053416 : List Nat := [2, 1, 4, 1, 1, 1, 3, 4, 1, 3, 2]
def baseStart_5053416 : Nat := 118140960795 + 5053416 * 2 ^ 59
def prefixEnd_5053416 : Nat := 4983230072969 + 3 ^ 40 * 5053416 * 2
def baseEnd_5053416 : Nat := 2594831355121105720359769

theorem tailTrace_5053416 : CollatzResearch.WordTrace tailWord_5053416 prefixEnd_5053416 2594831355121105720359769 := by
  unfold tailWord_5053416
  simp only [CollatzResearch.WordTrace]
  refine ⟨92156611730172180793306051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122875482306896241057741401 92156611730172180793306051)
  ·
    refine ⟨138234917595258271189959077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92156611730172180793306051 138234917595258271189959077)
    ·
      refine ⟨25919047049110925848117327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138234917595258271189959077 25919047049110925848117327)
      ·
        refine ⟨38878570573666388772175991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25919047049110925848117327 38878570573666388772175991)
        ·
          refine ⟨58317855860499583158263987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38878570573666388772175991 58317855860499583158263987)
          ·
            refine ⟨87476783790749374737395981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58317855860499583158263987 87476783790749374737395981)
            ·
              refine ⟨32803793921531015526523493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87476783790749374737395981 32803793921531015526523493)
              ·
                refine ⟨6150711360287065411223155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32803793921531015526523493 6150711360287065411223155)
                ·
                  refine ⟨9226067040430598116834733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6150711360287065411223155 9226067040430598116834733)
                  ·
                    refine ⟨3459775140161474293813025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9226067040430598116834733 3459775140161474293813025)
                    ·
                      refine ⟨2594831355121105720359769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3459775140161474293813025 2594831355121105720359769)
                      ·
                        rfl

theorem cell23_5053416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_5053416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053416 prefixEnd_5053416 := by exact prefixLift 5053416
  have htrace : WordTrace (prefixWord ++ tailWord_5053416) baseStart_5053416 baseEnd_5053416 := by
    simpa [prefixWord, tailWord_5053416, baseEnd_5053416] using wordTrace_append hprefix tailTrace_5053416
  have hstable : (prefixWord ++ tailWord_5053416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053416).length < 2 ^ (prefixWord ++ tailWord_5053416).sum := by decide
  have hdescent : baseEnd_5053416 < baseStart_5053416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053432 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 1, 6, 3]
def baseStart_5053432 : Nat := 118140960795 + 5053432 * 2 ^ 59
def prefixEnd_5053432 : Nat := 4983230072969 + 3 ^ 40 * 5053432 * 2
def baseEnd_5053432 : Nat := 2594839570811577657759695

theorem tailTrace_5053432 : CollatzResearch.WordTrace tailWord_5053432 prefixEnd_5053432 2594839570811577657759695 := by
  unfold tailWord_5053432
  simp only [CollatzResearch.WordTrace]
  refine ⟨92156903514143198159597275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122875871352190930879463033 92156903514143198159597275)
  ·
    refine ⟨138235355271214797239395913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92156903514143198159597275 138235355271214797239395913)
    ·
      refine ⟨103676516453411097929546935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138235355271214797239395913 103676516453411097929546935)
      ·
        refine ⟨155514774680116646894320403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103676516453411097929546935 155514774680116646894320403)
        ·
          refine ⟨233272162020174970341480605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155514774680116646894320403 233272162020174970341480605)
          ·
            refine ⟨87477060757565613878055227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233272162020174970341480605 87477060757565613878055227)
            ·
              refine ⟨131215591136348420817082841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87477060757565613878055227 131215591136348420817082841)
              ·
                refine ⟨98411693352261315612812131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131215591136348420817082841 98411693352261315612812131)
                ·
                  refine ⟨147617540028391973419218197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98411693352261315612812131 147617540028391973419218197)
                  ·
                    refine ⟨6919572188830873754025853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 147617540028391973419218197 6919572188830873754025853)
                    ·
                      refine ⟨2594839570811577657759695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6919572188830873754025853 2594839570811577657759695)
                      ·
                        rfl

theorem cell23_5053432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_5053432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053432 prefixEnd_5053432 := by exact prefixLift 5053432
  have htrace : WordTrace (prefixWord ++ tailWord_5053432) baseStart_5053432 baseEnd_5053432 := by
    simpa [prefixWord, tailWord_5053432, baseEnd_5053432] using wordTrace_append hprefix tailTrace_5053432
  have hstable : (prefixWord ++ tailWord_5053432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053432).length < 2 ^ (prefixWord ++ tailWord_5053432).sum := by decide
  have hdescent : baseEnd_5053432 < baseStart_5053432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053486 : List Nat := [4, 1, 3, 1, 1, 1, 2, 5, 5]
def baseStart_5053486 : Nat := 118140960795 + 5053486 * 2 ^ 59
def prefixEnd_5053486 : Nat := 4983230072969 + 3 ^ 40 * 5053486 * 2
def baseEnd_5053486 : Nat := 288318588751880049609383

theorem tailTrace_5053486 : CollatzResearch.WordTrace tailWord_5053486 prefixEnd_5053486 288318588751880049609383 := by
  unfold tailWord_5053486
  simp only [CollatzResearch.WordTrace]
  refine ⟨23039472071261345442707539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122877184380060509027773541 23039472071261345442707539)
  ·
    refine ⟨34559208106892018164061309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23039472071261345442707539 34559208106892018164061309)
    ·
      refine ⟨12959703040084506811522991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34559208106892018164061309 12959703040084506811522991)
      ·
        refine ⟨19439554560126760217284487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12959703040084506811522991 19439554560126760217284487)
        ·
          refine ⟨29159331840190140325926731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19439554560126760217284487 29159331840190140325926731)
          ·
            refine ⟨43738997760285210488890097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29159331840190140325926731 43738997760285210488890097)
            ·
              refine ⟨32804248320213907866667573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43738997760285210488890097 32804248320213907866667573)
              ·
                refine ⟨3075398280020053862500085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32804248320213907866667573 3075398280020053862500085)
                ·
                  refine ⟨288318588751880049609383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3075398280020053862500085 288318588751880049609383)
                  ·
                    rfl

theorem cell23_5053486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_5053486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053486 prefixEnd_5053486 := by exact prefixLift 5053486
  have htrace : WordTrace (prefixWord ++ tailWord_5053486) baseStart_5053486 baseEnd_5053486 := by
    simpa [prefixWord, tailWord_5053486, baseEnd_5053486] using wordTrace_append hprefix tailTrace_5053486
  have hstable : (prefixWord ++ tailWord_5053486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053486).length < 2 ^ (prefixWord ++ tailWord_5053486).sum := by decide
  have hdescent : baseEnd_5053486 < baseStart_5053486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053549 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_5053549 : Nat := 118140960795 + 5053549 * 2 ^ 59
def prefixEnd_5053549 : Nat := 4983230072969 + 3 ^ 40 * 5053549 * 2
def baseEnd_5053549 : Nat := 2594899648048153699996657

theorem tailTrace_5053549 : CollatzResearch.WordTrace tailWord_5053549 prefixEnd_5053549 2594899648048153699996657 := by
  unfold tailWord_5053549
  simp only [CollatzResearch.WordTrace]
  refine ⟨184318074368862525301203701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122878716245908350200802467 184318074368862525301203701)
  ·
    refine ⟨17279819472080861746987847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184318074368862525301203701 17279819472080861746987847)
    ·
      refine ⟨25919729208121292620481771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17279819472080861746987847 25919729208121292620481771)
      ·
        refine ⟨38879593812181938930722657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25919729208121292620481771 38879593812181938930722657)
        ·
          refine ⟨29159695359136454198041993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38879593812181938930722657 29159695359136454198041993)
          ·
            refine ⟨21869771519352340648531495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29159695359136454198041993 21869771519352340648531495)
            ·
              refine ⟨32804657279028510972797243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21869771519352340648531495 32804657279028510972797243)
              ·
                refine ⟨49206985918542766459195865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32804657279028510972797243 49206985918542766459195865)
                ·
                  refine ⟨36905239438907074844396899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49206985918542766459195865 36905239438907074844396899)
                  ·
                    refine ⟨55357859158360612266595349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36905239438907074844396899 55357859158360612266595349)
                    ·
                      refine ⟨2594899648048153699996657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55357859158360612266595349 2594899648048153699996657)
                      ·
                        rfl

theorem cell23_5053549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_5053549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053549 prefixEnd_5053549 := by exact prefixLift 5053549
  have htrace : WordTrace (prefixWord ++ tailWord_5053549) baseStart_5053549 baseEnd_5053549 := by
    simpa [prefixWord, tailWord_5053549, baseEnd_5053549] using wordTrace_append hprefix tailTrace_5053549
  have hstable : (prefixWord ++ tailWord_5053549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053549).length < 2 ^ (prefixWord ++ tailWord_5053549).sum := by decide
  have hdescent : baseEnd_5053549 < baseStart_5053549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053639 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_5053639 : Nat := 118140960795 + 5053639 * 2 ^ 59
def prefixEnd_5053639 : Nat := 4983230072969 + 3 ^ 40 * 5053639 * 2
def baseEnd_5053639 : Nat := 2594945861307058347871243

theorem tailTrace_5053639 : CollatzResearch.WordTrace tailWord_5053639 prefixEnd_5053639 2594945861307058347871243 := by
  unfold tailWord_5053639
  simp only [CollatzResearch.WordTrace]
  refine ⟨184321356938536470671979971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122880904625690980447986647 184321356938536470671979971)
  ·
    refine ⟨276482035407804706007969957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184321356938536470671979971 276482035407804706007969957)
    ·
      refine ⟨51840381638963382376494367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276482035407804706007969957 51840381638963382376494367)
      ·
        refine ⟨77760572458445073564741551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51840381638963382376494367 77760572458445073564741551)
        ·
          refine ⟨116640858687667610347112327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77760572458445073564741551 116640858687667610347112327)
          ·
            refine ⟨174961288031501415520668491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116640858687667610347112327 174961288031501415520668491)
            ·
              refine ⟨262441932047252123281002737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174961288031501415520668491 262441932047252123281002737)
              ·
                refine ⟨196831449035439092460752053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262441932047252123281002737 196831449035439092460752053)
                ·
                  refine ⟨18452948347072414918195505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 196831449035439092460752053 18452948347072414918195505)
                  ·
                    refine ⟨13839711260304311188646629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18452948347072414918195505 13839711260304311188646629)
                    ·
                      refine ⟨2594945861307058347871243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13839711260304311188646629 2594945861307058347871243)
                      ·
                        rfl

theorem cell23_5053639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_5053639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053639 prefixEnd_5053639 := by exact prefixLift 5053639
  have htrace : WordTrace (prefixWord ++ tailWord_5053639) baseStart_5053639 baseEnd_5053639 := by
    simpa [prefixWord, tailWord_5053639, baseEnd_5053639] using wordTrace_append hprefix tailTrace_5053639
  have hstable : (prefixWord ++ tailWord_5053639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053639).length < 2 ^ (prefixWord ++ tailWord_5053639).sum := by decide
  have hdescent : baseEnd_5053639 < baseStart_5053639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053659 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 3]
def baseStart_5053659 : Nat := 118140960795 + 5053659 * 2 ^ 59
def prefixEnd_5053659 : Nat := 4983230072969 + 3 ^ 40 * 5053659 * 2
def baseEnd_5053659 : Nat := 2594956130920148269621151

theorem tailTrace_5053659 : CollatzResearch.WordTrace tailWord_5053659 prefixEnd_5053659 2594956130920148269621151 := by
  unfold tailWord_5053659
  simp only [CollatzResearch.WordTrace]
  refine ⟨184322086398464014087708031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122881390932309342725138687 184322086398464014087708031)
  ·
    refine ⟨276483129597696021131562047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184322086398464014087708031 276483129597696021131562047)
    ·
      refine ⟨414724694396544031697343071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276483129597696021131562047 414724694396544031697343071)
      ·
        refine ⟨622087041594816047546014607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414724694396544031697343071 622087041594816047546014607)
        ·
          refine ⟨933130562392224071319021911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622087041594816047546014607 933130562392224071319021911)
          ·
            refine ⟨1399695843588336106978532867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933130562392224071319021911 1399695843588336106978532867)
            ·
              refine ⟨2099543765382504160467799301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399695843588336106978532867 2099543765382504160467799301)
              ·
                refine ⟨393664456009219530087712369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2099543765382504160467799301 393664456009219530087712369)
                ·
                  refine ⟨295248342006914647565784277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393664456009219530087712369 295248342006914647565784277)
                  ·
                    refine ⟨6919883015787062052323069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 295248342006914647565784277 6919883015787062052323069)
                    ·
                      refine ⟨2594956130920148269621151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6919883015787062052323069 2594956130920148269621151)
                      ·
                        rfl

theorem cell23_5053659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 3].length) (baseStart_5053659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053659 prefixEnd_5053659 := by exact prefixLift 5053659
  have htrace : WordTrace (prefixWord ++ tailWord_5053659) baseStart_5053659 baseEnd_5053659 := by
    simpa [prefixWord, tailWord_5053659, baseEnd_5053659] using wordTrace_append hprefix tailTrace_5053659
  have hstable : (prefixWord ++ tailWord_5053659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053659).length < 2 ^ (prefixWord ++ tailWord_5053659).sum := by decide
  have hdescent : baseEnd_5053659 < baseStart_5053659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053666 : List Nat := [3, 3, 4, 13]
def baseStart_5053666 : Nat := 118140960795 + 5053666 * 2 ^ 59
def prefixEnd_5053666 : Nat := 4983230072969 + 3 ^ 40 * 5053666 * 2
def baseEnd_5053666 : Nat := 1186538511789999882137

theorem tailTrace_5053666 : CollatzResearch.WordTrace tailWord_5053666 prefixEnd_5053666 1186538511789999882137 := by
  unfold tailWord_5053666
  simp only [CollatzResearch.WordTrace]
  refine ⟨46080585427359663570803213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122881561139625769522141901 46080585427359663570803213)
  ·
    refine ⟨17280219535259873839051205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46080585427359663570803213 17280219535259873839051205)
    ·
      refine ⟨3240041162861226344822101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17280219535259873839051205 3240041162861226344822101)
      ·
        refine ⟨1186538511789999882137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3240041162861226344822101 1186538511789999882137)
        ·
          rfl

theorem cell23_5053666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 13].length) (baseStart_5053666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053666 prefixEnd_5053666 := by exact prefixLift 5053666
  have htrace : WordTrace (prefixWord ++ tailWord_5053666) baseStart_5053666 baseEnd_5053666 := by
    simpa [prefixWord, tailWord_5053666, baseEnd_5053666] using wordTrace_append hprefix tailTrace_5053666
  have hstable : (prefixWord ++ tailWord_5053666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053666).length < 2 ^ (prefixWord ++ tailWord_5053666).sum := by decide
  have hdescent : baseEnd_5053666 < baseStart_5053666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053671 : List Nat := [1, 1, 5, 3, 3, 1, 2, 2, 1, 1, 3]
def baseStart_5053671 : Nat := 118140960795 + 5053671 * 2 ^ 59
def prefixEnd_5053671 : Nat := 4983230072969 + 3 ^ 40 * 5053671 * 2
def baseEnd_5053671 : Nat := 2594962292688002222671097

theorem tailTrace_5053671 : CollatzResearch.WordTrace tailWord_5053671 prefixEnd_5053671 2594962292688002222671097 := by
  unfold tailWord_5053671
  simp only [CollatzResearch.WordTrace]
  refine ⟨184322524074420540137144867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122881682716280360091429911 184322524074420540137144867)
  ·
    refine ⟨276483786111630810205717301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184322524074420540137144867 276483786111630810205717301)
    ·
      refine ⟨25920354947965388456785997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 276483786111630810205717301 25920354947965388456785997)
      ·
        refine ⟨9720133105487020671294749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25920354947965388456785997 9720133105487020671294749)
        ·
          refine ⟨3645049914557632751735531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9720133105487020671294749 3645049914557632751735531)
          ·
            refine ⟨5467574871836449127603297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3645049914557632751735531 5467574871836449127603297)
            ·
              refine ⟨4100681153877336845702473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5467574871836449127603297 4100681153877336845702473)
              ·
                refine ⟨3075510865408002634276855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4100681153877336845702473 3075510865408002634276855)
                ·
                  refine ⟨4613266298112003951415283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3075510865408002634276855 4613266298112003951415283)
                  ·
                    refine ⟨6919899447168005927122925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4613266298112003951415283 6919899447168005927122925)
                    ·
                      refine ⟨2594962292688002222671097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6919899447168005927122925 2594962292688002222671097)
                      ·
                        rfl

theorem cell23_5053671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_5053671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053671 prefixEnd_5053671 := by exact prefixLift 5053671
  have htrace : WordTrace (prefixWord ++ tailWord_5053671) baseStart_5053671 baseEnd_5053671 := by
    simpa [prefixWord, tailWord_5053671, baseEnd_5053671] using wordTrace_append hprefix tailTrace_5053671
  have hstable : (prefixWord ++ tailWord_5053671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053671).length < 2 ^ (prefixWord ++ tailWord_5053671).sum := by decide
  have hdescent : baseEnd_5053671 < baseStart_5053671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053720 : List Nat := [2, 1, 2, 3, 1, 4, 1, 3, 1, 3, 2]
def baseStart_5053720 : Nat := 118140960795 + 5053720 * 2 ^ 59
def prefixEnd_5053720 : Nat := 4983230072969 + 3 ^ 40 * 5053720 * 2
def baseEnd_5053720 : Nat := 2594987453240072530958371

theorem tailTrace_5053720 : CollatzResearch.WordTrace tailWord_5053720 prefixEnd_5053720 2594987453240072530958371 := by
  unfold tailWord_5053720
  simp only [CollatzResearch.WordTrace]
  refine ⟨92162155625621510752839307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122882874167495347670452409 92162155625621510752839307)
  ·
    refine ⟨138243233438432266129258961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92162155625621510752839307 138243233438432266129258961)
    ·
      refine ⟨103682425078824199596944221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138243233438432266129258961 103682425078824199596944221)
      ·
        refine ⟨38880909404559074848854083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103682425078824199596944221 38880909404559074848854083)
        ·
          refine ⟨58321364106838612273281125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38880909404559074848854083 58321364106838612273281125)
          ·
            refine ⟨10935255770032239801240211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58321364106838612273281125 10935255770032239801240211)
            ·
              refine ⟨16402883655048359701860317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10935255770032239801240211 16402883655048359701860317)
              ·
                refine ⟨6151081370643134888197619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16402883655048359701860317 6151081370643134888197619)
                ·
                  refine ⟨9226622055964702332296429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6151081370643134888197619 9226622055964702332296429)
                  ·
                    refine ⟨3459983270986763374611161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9226622055964702332296429 3459983270986763374611161)
                    ·
                      refine ⟨2594987453240072530958371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3459983270986763374611161 2594987453240072530958371)
                      ·
                        rfl

theorem cell23_5053720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_5053720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053720 prefixEnd_5053720 := by exact prefixLift 5053720
  have htrace : WordTrace (prefixWord ++ tailWord_5053720) baseStart_5053720 baseEnd_5053720 := by
    simpa [prefixWord, tailWord_5053720, baseEnd_5053720] using wordTrace_append hprefix tailTrace_5053720
  have hstable : (prefixWord ++ tailWord_5053720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053720).length < 2 ^ (prefixWord ++ tailWord_5053720).sum := by decide
  have hdescent : baseEnd_5053720 < baseStart_5053720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053727 : List Nat := [1, 1, 2, 4, 4, 2, 1, 2, 2, 1, 3]
def baseStart_5053727 : Nat := 118140960795 + 5053727 * 2 ^ 59
def prefixEnd_5053727 : Nat := 4983230072969 + 3 ^ 40 * 5053727 * 2
def baseEnd_5053727 : Nat := 2594991047604654003570839

theorem tailTrace_5053727 : CollatzResearch.WordTrace tailWord_5053727 prefixEnd_5053727 2594991047604654003570839 := by
  unfold tailWord_5053727
  simp only [CollatzResearch.WordTrace]
  refine ⟨184324566562217661701183435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122883044374811774467455623 184324566562217661701183435)
  ·
    refine ⟨276486849843326492551775153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184324566562217661701183435 276486849843326492551775153)
    ·
      refine ⟨207365137382494869413831365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276486849843326492551775153 207365137382494869413831365)
      ·
        refine ⟨38880963259217788015093381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207365137382494869413831365 38880963259217788015093381)
        ·
          refine ⟨7290180611103335252830009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38880963259217788015093381 7290180611103335252830009)
          ·
            refine ⟨5467635458327501439622507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7290180611103335252830009 5467635458327501439622507)
            ·
              refine ⟨8201453187491252159433761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5467635458327501439622507 8201453187491252159433761)
              ·
                refine ⟨6151089890618439119575321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8201453187491252159433761 6151089890618439119575321)
                ·
                  refine ⟨4613317417963829339681491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6151089890618439119575321 4613317417963829339681491)
                  ·
                    refine ⟨6919976126945744009522237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4613317417963829339681491 6919976126945744009522237)
                    ·
                      refine ⟨2594991047604654003570839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6919976126945744009522237 2594991047604654003570839)
                      ·
                        rfl

theorem cell23_5053727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_5053727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053727 prefixEnd_5053727 := by exact prefixLift 5053727
  have htrace : WordTrace (prefixWord ++ tailWord_5053727) baseStart_5053727 baseEnd_5053727 := by
    simpa [prefixWord, tailWord_5053727, baseEnd_5053727] using wordTrace_append hprefix tailTrace_5053727
  have hstable : (prefixWord ++ tailWord_5053727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053727).length < 2 ^ (prefixWord ++ tailWord_5053727).sum := by decide
  have hdescent : baseEnd_5053727 < baseStart_5053727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053756 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 7]
def baseStart_5053756 : Nat := 118140960795 + 5053756 * 2 ^ 59
def prefixEnd_5053756 : Nat := 4983230072969 + 3 ^ 40 * 5053756 * 2
def baseEnd_5053756 : Nat := 288333993171514932234245

theorem tailTrace_5053756 : CollatzResearch.WordTrace tailWord_5053756 prefixEnd_5053756 288333993171514932234245 := by
  unfold tailWord_5053756
  simp only [CollatzResearch.WordTrace]
  refine ⟨92162812139556299826994561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122883749519408399769326081 92162812139556299826994561)
  ·
    refine ⟨69122109104667224870245921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92162812139556299826994561 69122109104667224870245921)
    ·
      refine ⟨51841581828500418652684441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69122109104667224870245921 51841581828500418652684441)
      ·
        refine ⟨38881186371375313989513331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51841581828500418652684441 38881186371375313989513331)
        ·
          refine ⟨58321779557062970984269997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38881186371375313989513331 58321779557062970984269997)
          ·
            refine ⟨21870667333898614119101249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58321779557062970984269997 21870667333898614119101249)
            ·
              refine ⟨16403000500423960589325937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21870667333898614119101249 16403000500423960589325937)
              ·
                refine ⟨12302250375317970441994453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16403000500423960589325937 12302250375317970441994453)
                ·
                  refine ⟨288333993171514932234245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12302250375317970441994453 288333993171514932234245)
                  ·
                    rfl

theorem cell23_5053756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 7].length) (baseStart_5053756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053756 prefixEnd_5053756 := by exact prefixLift 5053756
  have htrace : WordTrace (prefixWord ++ tailWord_5053756) baseStart_5053756 baseEnd_5053756 := by
    simpa [prefixWord, tailWord_5053756, baseEnd_5053756] using wordTrace_append hprefix tailTrace_5053756
  have hstable : (prefixWord ++ tailWord_5053756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053756).length < 2 ^ (prefixWord ++ tailWord_5053756).sum := by decide
  have hdescent : baseEnd_5053756 < baseStart_5053756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053786 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 4, 5]
def baseStart_5053786 : Nat := 118140960795 + 5053786 * 2 ^ 59
def prefixEnd_5053786 : Nat := 4983230072969 + 3 ^ 40 * 5053786 * 2
def baseEnd_5053786 : Nat := 865007114321089757577689

theorem tailTrace_5053786 : CollatzResearch.WordTrace tailWord_5053786 prefixEnd_5053786 865007114321089757577689 := by
  unfold tailWord_5053786
  simp only [CollatzResearch.WordTrace]
  refine ⟨46081679617250978694395303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122884478979335943185054141 46081679617250978694395303)
  ·
    refine ⟨69122519425876468041592955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46081679617250978694395303 69122519425876468041592955)
    ·
      refine ⟨103683779138814702062389433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69122519425876468041592955 103683779138814702062389433)
      ·
        refine ⟨77762834354111026546792075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103683779138814702062389433 77762834354111026546792075)
        ·
          refine ⟨116644251531166539820188113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77762834354111026546792075 116644251531166539820188113)
          ·
            refine ⟨87483188648374904865141085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116644251531166539820188113 87483188648374904865141085)
            ·
              refine ⟨32806195743140589324427907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87483188648374904865141085 32806195743140589324427907)
              ·
                refine ⟨49209293614710883986641861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32806195743140589324427907 49209293614710883986641861)
                ·
                  refine ⟨9226742552758290747495349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49209293614710883986641861 9226742552758290747495349)
                  ·
                    refine ⟨865007114321089757577689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9226742552758290747495349 865007114321089757577689)
                    ·
                      rfl

theorem cell23_5053786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_5053786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053786 prefixEnd_5053786 := by exact prefixLift 5053786
  have htrace : WordTrace (prefixWord ++ tailWord_5053786) baseStart_5053786 baseEnd_5053786 := by
    simpa [prefixWord, tailWord_5053786, baseEnd_5053786] using wordTrace_append hprefix tailTrace_5053786
  have hstable : (prefixWord ++ tailWord_5053786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053786).length < 2 ^ (prefixWord ++ tailWord_5053786).sum := by decide
  have hdescent : baseEnd_5053786 < baseStart_5053786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
