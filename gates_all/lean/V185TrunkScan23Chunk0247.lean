import V185TrunkScan23Chunk0246

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1461224 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_1461224 : Nat := 118140960795 + 1461224 * 2 ^ 59
def prefixEnd_1461224 : Nat := 4983230072969 + 3 ^ 40 * 1461224 * 2
def baseEnd_1461224 : Nat := 750310255885496188079959

theorem tailTrace_1461224 : CollatzResearch.WordTrace tailWord_1461224 prefixEnd_1461224 750310255885496188079959 := by
  unfold tailWord_1461224
  simp only [CollatzResearch.WordTrace]
  refine ⟨26647608829121240018023363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35530145105494986690697817 26647608829121240018023363)
  ·
    refine ⟨39971413243681860027035045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26647608829121240018023363 39971413243681860027035045)
    ·
      refine ⟨7494639983190348755069071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39971413243681860027035045 7494639983190348755069071)
      ·
        refine ⟨11241959974785523132603607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7494639983190348755069071 11241959974785523132603607)
        ·
          refine ⟨16862939962178284698905411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11241959974785523132603607 16862939962178284698905411)
          ·
            refine ⟨25294409943267427048358117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16862939962178284698905411 25294409943267427048358117)
            ·
              refine ⟨4742701864362642571567147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25294409943267427048358117 4742701864362642571567147)
              ·
                refine ⟨7114052796543963857350721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4742701864362642571567147 7114052796543963857350721)
                ·
                  refine ⟨5335539597407972893013041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7114052796543963857350721 5335539597407972893013041)
                  ·
                    refine ⟨4001654698055979669759781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5335539597407972893013041 4001654698055979669759781)
                    ·
                      refine ⟨750310255885496188079959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4001654698055979669759781 750310255885496188079959)
                      ·
                        rfl

theorem cell23_1461224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_1461224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461224 prefixEnd_1461224 := by exact prefixLift 1461224
  have htrace : WordTrace (prefixWord ++ tailWord_1461224) baseStart_1461224 baseEnd_1461224 := by
    simpa [prefixWord, tailWord_1461224, baseEnd_1461224] using wordTrace_append hprefix tailTrace_1461224
  have hstable : (prefixWord ++ tailWord_1461224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461224).length < 2 ^ (prefixWord ++ tailWord_1461224).sum := by decide
  have hdescent : baseEnd_1461224 < baseStart_1461224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461257 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 7]
def baseStart_1461257 : Nat := 118140960795 + 1461257 * 2 ^ 59
def prefixEnd_1461257 : Nat := 4983230072969 + 3 ^ 40 * 1461257 * 2
def baseEnd_1461257 : Nat := 750327200747094558967307

theorem tailTrace_1461257 : CollatzResearch.WordTrace tailWord_1461257 prefixEnd_1461257 750327200747094558967307 := by
  unfold tailWord_1461257
  simp only [CollatzResearch.WordTrace]
  refine ⟨53296421267122926671998025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35530947511415284447998683 53296421267122926671998025)
  ·
    refine ⟨39972315950342195003998519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53296421267122926671998025 39972315950342195003998519)
    ·
      refine ⟨59958473925513292505997779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39972315950342195003998519 59958473925513292505997779)
      ·
        refine ⟨89937710888269938758996669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59958473925513292505997779 89937710888269938758996669)
        ·
          refine ⟨33726641583101227034623751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89937710888269938758996669 33726641583101227034623751)
          ·
            refine ⟨50589962374651840551935627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33726641583101227034623751 50589962374651840551935627)
            ·
              refine ⟨75884943561977760827903441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50589962374651840551935627 75884943561977760827903441)
              ·
                refine ⟨56913707671483320620927581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75884943561977760827903441 56913707671483320620927581)
                ·
                  refine ⟨21342640376806245232847843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56913707671483320620927581 21342640376806245232847843)
                  ·
                    refine ⟨32013960565209367849271765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21342640376806245232847843 32013960565209367849271765)
                    ·
                      refine ⟨750327200747094558967307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32013960565209367849271765 750327200747094558967307)
                      ·
                        rfl

theorem cell23_1461257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_1461257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461257 prefixEnd_1461257 := by exact prefixLift 1461257
  have htrace : WordTrace (prefixWord ++ tailWord_1461257) baseStart_1461257 baseEnd_1461257 := by
    simpa [prefixWord, tailWord_1461257, baseEnd_1461257] using wordTrace_append hprefix tailTrace_1461257
  have hstable : (prefixWord ++ tailWord_1461257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461257).length < 2 ^ (prefixWord ++ tailWord_1461257).sum := by decide
  have hdescent : baseEnd_1461257 < baseStart_1461257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461274 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5]
def baseStart_1461274 : Nat := 118140960795 + 1461274 * 2 ^ 59
def prefixEnd_1461274 : Nat := 4983230072969 + 3 ^ 40 * 1461274 * 2
def baseEnd_1461274 : Nat := 750335929918220992454729

theorem tailTrace_1461274 : CollatzResearch.WordTrace tailWord_1461274 prefixEnd_1461274 750335929918220992454729 := by
  unfold tailWord_1461274
  simp only [CollatzResearch.WordTrace]
  refine ⟨13324260327015334643841719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35531360872040892383577917 13324260327015334643841719)
  ·
    refine ⟨19986390490523001965762579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13324260327015334643841719 19986390490523001965762579)
    ·
      refine ⟨29979585735784502948643869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19986390490523001965762579 29979585735784502948643869)
      ·
        refine ⟨11242344650919188605741451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29979585735784502948643869 11242344650919188605741451)
        ·
          refine ⟨16863516976378782908612177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11242344650919188605741451 16863516976378782908612177)
          ·
            refine ⟨12647637732284087181459133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16863516976378782908612177 12647637732284087181459133)
            ·
              refine ⟨4742864149606532693047175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12647637732284087181459133 4742864149606532693047175)
              ·
                refine ⟨7114296224409799039570763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4742864149606532693047175 7114296224409799039570763)
                ·
                  refine ⟨10671444336614698559356145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7114296224409799039570763 10671444336614698559356145)
                  ·
                    refine ⟨8003583252461023919517109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10671444336614698559356145 8003583252461023919517109)
                    ·
                      refine ⟨750335929918220992454729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8003583252461023919517109 750335929918220992454729)
                      ·
                        rfl

theorem cell23_1461274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_1461274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461274 prefixEnd_1461274 := by exact prefixLift 1461274
  have htrace : WordTrace (prefixWord ++ tailWord_1461274) baseStart_1461274 baseEnd_1461274 := by
    simpa [prefixWord, tailWord_1461274, baseEnd_1461274] using wordTrace_append hprefix tailTrace_1461274
  have hstable : (prefixWord ++ tailWord_1461274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461274).length < 2 ^ (prefixWord ++ tailWord_1461274).sum := by decide
  have hdescent : baseEnd_1461274 < baseStart_1461274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461301 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 4, 4, 2]
def baseStart_1461301 : Nat := 118140960795 + 1461301 * 2 ^ 59
def prefixEnd_1461301 : Nat := 4983230072969 + 3 ^ 40 * 1461301 * 2
def baseEnd_1461301 : Nat := 750349793895892386817105

theorem tailTrace_1461301 : CollatzResearch.WordTrace tailWord_1461301 prefixEnd_1461301 750349793895892386817105 := by
  unfold tailWord_1461301
  simp only [CollatzResearch.WordTrace]
  refine ⟨53298026078963522186599757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35532017385975681457733171 53298026078963522186599757)
  ·
    refine ⟨19986759779611320819974909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53298026078963522186599757 19986759779611320819974909)
    ·
      refine ⟨7495034917354245307490591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19986759779611320819974909 7495034917354245307490591)
      ·
        refine ⟨11242552376031367961235887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7495034917354245307490591 11242552376031367961235887)
        ·
          refine ⟨16863828564047051941853831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11242552376031367961235887 16863828564047051941853831)
          ·
            refine ⟨25295742846070577912780747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16863828564047051941853831 25295742846070577912780747)
            ·
              refine ⟨37943614269105866869171121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25295742846070577912780747 37943614269105866869171121)
              ·
                refine ⟨28457710701829400151878341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37943614269105866869171121 28457710701829400151878341)
                ·
                  refine ⟨5335820756593012528477189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28457710701829400151878341 5335820756593012528477189)
                  ·
                    refine ⟨1000466391861189849089473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5335820756593012528477189 1000466391861189849089473)
                    ·
                      refine ⟨750349793895892386817105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000466391861189849089473 750349793895892386817105)
                      ·
                        rfl

theorem cell23_1461301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_1461301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461301 prefixEnd_1461301 := by exact prefixLift 1461301
  have htrace : WordTrace (prefixWord ++ tailWord_1461301) baseStart_1461301 baseEnd_1461301 := by
    simpa [prefixWord, tailWord_1461301, baseEnd_1461301] using wordTrace_append hprefix tailTrace_1461301
  have hstable : (prefixWord ++ tailWord_1461301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461301).length < 2 ^ (prefixWord ++ tailWord_1461301).sum := by decide
  have hdescent : baseEnd_1461301 < baseStart_1461301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461352 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 2, 1, 4]
def baseStart_1461352 : Nat := 118140960795 + 1461352 * 2 ^ 59
def prefixEnd_1461352 : Nat := 4983230072969 + 3 ^ 40 * 1461352 * 2
def baseEnd_1461352 : Nat := 750375981409271687279371

theorem tailTrace_1461352 : CollatzResearch.WordTrace tailWord_1461352 prefixEnd_1461352 750375981409271687279371 := by
  unfold tailWord_1461352
  simp only [CollatzResearch.WordTrace]
  refine ⟨26649943100889378948353155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35533257467852505264470873 26649943100889378948353155)
  ·
    refine ⟨39974914651334068422529733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26649943100889378948353155 39974914651334068422529733)
    ·
      refine ⟨7495296497125137829224325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39974914651334068422529733 7495296497125137829224325)
      ·
        refine ⟨1405368093210963342979561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7495296497125137829224325 1405368093210963342979561)
        ·
          refine ⟨1054026069908222507234671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1405368093210963342979561 1054026069908222507234671)
          ·
            refine ⟨1581039104862333760852007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054026069908222507234671 1581039104862333760852007)
            ·
              refine ⟨2371558657293500641278011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1581039104862333760852007 2371558657293500641278011)
              ·
                refine ⟨3557337985940250961917017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2371558657293500641278011 3557337985940250961917017)
                ·
                  refine ⟨2668003489455188221437763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3557337985940250961917017 2668003489455188221437763)
                  ·
                    refine ⟨4002005234182782332156645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2668003489455188221437763 4002005234182782332156645)
                    ·
                      refine ⟨750375981409271687279371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4002005234182782332156645 750375981409271687279371)
                      ·
                        rfl

theorem cell23_1461352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_1461352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461352 prefixEnd_1461352 := by exact prefixLift 1461352
  have htrace : WordTrace (prefixWord ++ tailWord_1461352) baseStart_1461352 baseEnd_1461352 := by
    simpa [prefixWord, tailWord_1461352, baseEnd_1461352] using wordTrace_append hprefix tailTrace_1461352
  have hstable : (prefixWord ++ tailWord_1461352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461352).length < 2 ^ (prefixWord ++ tailWord_1461352).sum := by decide
  have hdescent : baseEnd_1461352 < baseStart_1461352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461385 : List Nat := [1, 2, 1, 1, 4, 3, 2, 4, 1, 1, 3]
def baseStart_1461385 : Nat := 118140960795 + 1461385 * 2 ^ 59
def prefixEnd_1461385 : Nat := 4983230072969 + 3 ^ 40 * 1461385 * 2
def baseEnd_1461385 : Nat := 750392926270870058166719

theorem tailTrace_1461385 : CollatzResearch.WordTrace tailWord_1461385 prefixEnd_1461385 750392926270870058166719 := by
  unfold tailWord_1461385
  simp only [CollatzResearch.WordTrace]
  refine ⟨53301089810659204532657609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35534059873772803021771739 53301089810659204532657609)
  ·
    refine ⟨39975817357994403399493207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53301089810659204532657609 39975817357994403399493207)
    ·
      refine ⟨59963726036991605099239811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39975817357994403399493207 59963726036991605099239811)
      ·
        refine ⟨89945589055487407648859717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59963726036991605099239811 89945589055487407648859717)
        ·
          refine ⟨16864797947903888934161197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89945589055487407648859717 16864797947903888934161197)
          ·
            refine ⟨6324299230463958350310449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16864797947903888934161197 6324299230463958350310449)
            ·
              refine ⟨4743224422847968762732837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6324299230463958350310449 4743224422847968762732837)
              ·
                refine ⟨889354579283994143012407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4743224422847968762732837 889354579283994143012407)
                ·
                  refine ⟨1334031868925991214518611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889354579283994143012407 1334031868925991214518611)
                  ·
                    refine ⟨2001047803388986821777917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1334031868925991214518611 2001047803388986821777917)
                    ·
                      refine ⟨750392926270870058166719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2001047803388986821777917 750392926270870058166719)
                      ·
                        rfl

theorem cell23_1461385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 1, 1, 3].length) (baseStart_1461385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461385 prefixEnd_1461385 := by exact prefixLift 1461385
  have htrace : WordTrace (prefixWord ++ tailWord_1461385) baseStart_1461385 baseEnd_1461385 := by
    simpa [prefixWord, tailWord_1461385, baseEnd_1461385] using wordTrace_append hprefix tailTrace_1461385
  have hstable : (prefixWord ++ tailWord_1461385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461385).length < 2 ^ (prefixWord ++ tailWord_1461385).sum := by decide
  have hdescent : baseEnd_1461385 < baseStart_1461385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461408 : List Nat := [2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 4]
def baseStart_1461408 : Nat := 118140960795 + 1461408 * 2 ^ 59
def prefixEnd_1461408 : Nat := 4983230072969 + 3 ^ 40 * 1461408 * 2
def baseEnd_1461408 : Nat := 750404736325923468179113

theorem tailTrace_1461408 : CollatzResearch.WordTrace tailWord_1461408 prefixEnd_1461408 750404736325923468179113 := by
  unfold tailWord_1461408
  simp only [CollatzResearch.WordTrace]
  refine ⟨26650964344787939730372439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35534619126383919640496585 26650964344787939730372439)
  ·
    refine ⟨39976446517181909595558659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26650964344787939730372439 39976446517181909595558659)
    ·
      refine ⟨59964669775772864393337989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39976446517181909595558659 59964669775772864393337989)
      ·
        refine ⟨11243375582957412073750873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59964669775772864393337989 11243375582957412073750873)
        ·
          refine ⟨8432531687218059055313155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11243375582957412073750873 8432531687218059055313155)
          ·
            refine ⟨12648797530827088582969733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8432531687218059055313155 12648797530827088582969733)
            ·
              refine ⟨2371649537030079109306825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12648797530827088582969733 2371649537030079109306825)
              ·
                refine ⟨1778737152772559331980119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2371649537030079109306825 1778737152772559331980119)
                ·
                  refine ⟨2668105729158838997970179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778737152772559331980119 2668105729158838997970179)
                  ·
                    refine ⟨4002158593738258496955269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2668105729158838997970179 4002158593738258496955269)
                    ·
                      refine ⟨750404736325923468179113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4002158593738258496955269 750404736325923468179113)
                      ·
                        rfl

theorem cell23_1461408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_1461408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461408 prefixEnd_1461408 := by exact prefixLift 1461408
  have htrace : WordTrace (prefixWord ++ tailWord_1461408) baseStart_1461408 baseEnd_1461408 := by
    simpa [prefixWord, tailWord_1461408, baseEnd_1461408] using wordTrace_append hprefix tailTrace_1461408
  have hstable : (prefixWord ++ tailWord_1461408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461408).length < 2 ^ (prefixWord ++ tailWord_1461408).sum := by decide
  have hdescent : baseEnd_1461408 < baseStart_1461408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461411 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 3]
def baseStart_1461411 : Nat := 118140960795 + 1461411 * 2 ^ 59
def prefixEnd_1461411 : Nat := 4983230072969 + 3 ^ 40 * 1461411 * 2
def baseEnd_1461411 : Nat := 750406276767886956441599

theorem tailTrace_1461411 : CollatzResearch.WordTrace tailWord_1461411 prefixEnd_1461411 750406276767886956441599 := by
  unfold tailWord_1461411
  simp only [CollatzResearch.WordTrace]
  refine ⟨53302038108565010973104087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35534692072376673982069391 53302038108565010973104087)
  ·
    refine ⟨79953057162847516459656131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53302038108565010973104087 79953057162847516459656131)
    ·
      refine ⟨119929585744271274689484197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79953057162847516459656131 119929585744271274689484197)
      ·
        refine ⟨22486797327050864004278287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119929585744271274689484197 22486797327050864004278287)
        ·
          refine ⟨33730195990576296006417431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22486797327050864004278287 33730195990576296006417431)
          ·
            refine ⟨50595293985864444009626147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33730195990576296006417431 50595293985864444009626147)
            ·
              refine ⟨75892940978796666014439221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50595293985864444009626147 75892940978796666014439221)
              ·
                refine ⟨7114963216762187438853677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75892940978796666014439221 7114963216762187438853677)
                ·
                  refine ⟨2668111206285820289570129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7114963216762187438853677 2668111206285820289570129)
                  ·
                    refine ⟨2001083404714365217177597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2668111206285820289570129 2001083404714365217177597)
                    ·
                      refine ⟨750406276767886956441599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2001083404714365217177597 750406276767886956441599)
                      ·
                        rfl

theorem cell23_1461411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_1461411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461411 prefixEnd_1461411 := by exact prefixLift 1461411
  have htrace : WordTrace (prefixWord ++ tailWord_1461411) baseStart_1461411 baseEnd_1461411 := by
    simpa [prefixWord, tailWord_1461411, baseEnd_1461411] using wordTrace_append hprefix tailTrace_1461411
  have hstable : (prefixWord ++ tailWord_1461411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461411).length < 2 ^ (prefixWord ++ tailWord_1461411).sum := by decide
  have hdescent : baseEnd_1461411 < baseStart_1461411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461458 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_1461458 : Nat := 118140960795 + 1461458 * 2 ^ 59
def prefixEnd_1461458 : Nat := 4983230072969 + 3 ^ 40 * 1461458 * 2
def baseEnd_1461458 : Nat := 750430410358648272553883

theorem tailTrace_1461458 : CollatzResearch.WordTrace tailWord_1461458 prefixEnd_1461458 750430410358648272553883 := by
  unfold tailWord_1461458
  simp only [CollatzResearch.WordTrace]
  refine ⟨13325938084848684500016257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35535834892929825333376685 13325938084848684500016257)
  ·
    refine ⟨9994453563636513375012193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13325938084848684500016257 9994453563636513375012193)
    ·
      refine ⟨7495840172727385031259145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9994453563636513375012193 7495840172727385031259145)
      ·
        refine ⟨5621880129545538773444359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7495840172727385031259145 5621880129545538773444359)
        ·
          refine ⟨8432820194318308160166539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5621880129545538773444359 8432820194318308160166539)
          ·
            refine ⟨12649230291477462240249809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8432820194318308160166539 12649230291477462240249809)
            ·
              refine ⟨9486922718608096680187357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12649230291477462240249809 9486922718608096680187357)
              ·
                refine ⟨3557596019478036255070259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9486922718608096680187357 3557596019478036255070259)
                ·
                  refine ⟨5336394029217054382605389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3557596019478036255070259 5336394029217054382605389)
                  ·
                    refine ⟨2001147760956395393477021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5336394029217054382605389 2001147760956395393477021)
                    ·
                      refine ⟨750430410358648272553883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2001147760956395393477021 750430410358648272553883)
                      ·
                        rfl

theorem cell23_1461458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_1461458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461458 prefixEnd_1461458 := by exact prefixLift 1461458
  have htrace : WordTrace (prefixWord ++ tailWord_1461458) baseStart_1461458 baseEnd_1461458 := by
    simpa [prefixWord, tailWord_1461458, baseEnd_1461458] using wordTrace_append hprefix tailTrace_1461458
  have hstable : (prefixWord ++ tailWord_1461458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461458).length < 2 ^ (prefixWord ++ tailWord_1461458).sum := by decide
  have hdescent : baseEnd_1461458 < baseStart_1461458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461462 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1461462 : Nat := 118140960795 + 1461462 * 2 ^ 59
def prefixEnd_1461462 : Nat := 4983230072969 + 3 ^ 40 * 1461462 * 2
def baseEnd_1461462 : Nat := 750432464281266256903865

theorem tailTrace_1461462 : CollatzResearch.WordTrace tailWord_1461462 prefixEnd_1461462 750432464281266256903865 := by
  unfold tailWord_1461462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3331493639461265417700665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35535932154253497788807093 3331493639461265417700665)
  ·
    refine ⟨2498620229595949063275499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3331493639461265417700665 2498620229595949063275499)
    ·
      refine ⟨3747930344393923594913249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2498620229595949063275499 3747930344393923594913249)
      ·
        refine ⟨2810947758295442696184937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3747930344393923594913249 2810947758295442696184937)
        ·
          refine ⟨2108210818721582022138703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2810947758295442696184937 2108210818721582022138703)
          ·
            refine ⟨3162316228082373033208055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108210818721582022138703 3162316228082373033208055)
            ·
              refine ⟨4743474342123559549812083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3162316228082373033208055 4743474342123559549812083)
              ·
                refine ⟨7115211513185339324718125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4743474342123559549812083 7115211513185339324718125)
                ·
                  refine ⟨2668204317444502246769297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7115211513185339324718125 2668204317444502246769297)
                  ·
                    refine ⟨2001153238083376685076973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2668204317444502246769297 2001153238083376685076973)
                    ·
                      refine ⟨750432464281266256903865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2001153238083376685076973 750432464281266256903865)
                      ·
                        rfl

theorem cell23_1461462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1461462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461462 prefixEnd_1461462 := by exact prefixLift 1461462
  have htrace : WordTrace (prefixWord ++ tailWord_1461462) baseStart_1461462 baseEnd_1461462 := by
    simpa [prefixWord, tailWord_1461462, baseEnd_1461462] using wordTrace_append hprefix tailTrace_1461462
  have hstable : (prefixWord ++ tailWord_1461462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461462).length < 2 ^ (prefixWord ++ tailWord_1461462).sum := by decide
  have hdescent : baseEnd_1461462 < baseStart_1461462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461498 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2]
def baseStart_1461498 : Nat := 118140960795 + 1461498 * 2 ^ 59
def prefixEnd_1461498 : Nat := 4983230072969 + 3 ^ 40 * 1461498 * 2
def baseEnd_1461498 : Nat := 750450949584828116053699

theorem tailTrace_1461498 : CollatzResearch.WordTrace tailWord_1461498 prefixEnd_1461498 750450949584828116053699 := by
  unfold tailWord_1461498
  simp only [CollatzResearch.WordTrace]
  refine ⟨13326302814812456207880287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35536807506166549887680765 13326302814812456207880287)
  ·
    refine ⟨19989454222218684311820431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13326302814812456207880287 19989454222218684311820431)
    ·
      refine ⟨29984181333328026467730647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19989454222218684311820431 29984181333328026467730647)
      ·
        refine ⟨44976271999992039701595971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29984181333328026467730647 44976271999992039701595971)
        ·
          refine ⟨67464407999988059552393957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44976271999992039701595971 67464407999988059552393957)
          ·
            refine ⟨12649576499997761166073867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67464407999988059552393957 12649576499997761166073867)
            ·
              refine ⟨18974364749996641749110801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12649576499997761166073867 18974364749996641749110801)
              ·
                refine ⟨14230773562497481311833101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18974364749996641749110801 14230773562497481311833101)
                ·
                  refine ⟨5336540085936555491937413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14230773562497481311833101 5336540085936555491937413)
                  ·
                    refine ⟨1000601266113104154738265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5336540085936555491937413 1000601266113104154738265)
                    ·
                      refine ⟨750450949584828116053699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000601266113104154738265 750450949584828116053699)
                      ·
                        rfl

theorem cell23_1461498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2].length) (baseStart_1461498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461498 prefixEnd_1461498 := by exact prefixLift 1461498
  have htrace : WordTrace (prefixWord ++ tailWord_1461498) baseStart_1461498 baseEnd_1461498 := by
    simpa [prefixWord, tailWord_1461498, baseEnd_1461498] using wordTrace_append hprefix tailTrace_1461498
  have hstable : (prefixWord ++ tailWord_1461498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461498).length < 2 ^ (prefixWord ++ tailWord_1461498).sum := by decide
  have hdescent : baseEnd_1461498 < baseStart_1461498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461508 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 2, 6]
def baseStart_1461508 : Nat := 118140960795 + 1461508 * 2 ^ 59
def prefixEnd_1461508 : Nat := 4983230072969 + 3 ^ 40 * 1461508 * 2
def baseEnd_1461508 : Nat := 250152028130457692309551

theorem tailTrace_1461508 : CollatzResearch.WordTrace tailWord_1461508 prefixEnd_1461508 250152028130457692309551 := by
  unfold tailWord_1461508
  simp only [CollatzResearch.WordTrace]
  refine ⟨26652787994606798269692589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35537050659475731026256785 26652787994606798269692589)
  ·
    refine ⟨9994795497977549351134721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26652787994606798269692589 9994795497977549351134721)
    ·
      refine ⟨7496096623483162013351041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9994795497977549351134721 7496096623483162013351041)
      ·
        refine ⟨5622072467612371510013281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7496096623483162013351041 5622072467612371510013281)
        ·
          refine ⟨4216554350709278632509961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5622072467612371510013281 4216554350709278632509961)
          ·
            refine ⟨3162415763031958974382471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4216554350709278632509961 3162415763031958974382471)
            ·
              refine ⟨4743623644547938461573707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3162415763031958974382471 4743623644547938461573707)
              ·
                refine ⟨7115435466821907692360561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4743623644547938461573707 7115435466821907692360561)
                ·
                  refine ⟨5336576600116430769270421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7115435466821907692360561 5336576600116430769270421)
                  ·
                    refine ⟨250152028130457692309551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5336576600116430769270421 250152028130457692309551)
                    ·
                      rfl

theorem cell23_1461508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_1461508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461508 prefixEnd_1461508 := by exact prefixLift 1461508
  have htrace : WordTrace (prefixWord ++ tailWord_1461508) baseStart_1461508 baseEnd_1461508 := by
    simpa [prefixWord, tailWord_1461508, baseEnd_1461508] using wordTrace_append hprefix tailTrace_1461508
  have hstable : (prefixWord ++ tailWord_1461508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461508).length < 2 ^ (prefixWord ++ tailWord_1461508).sum := by decide
  have hdescent : baseEnd_1461508 < baseStart_1461508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461515 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 1, 4, 2]
def baseStart_1461515 : Nat := 118140960795 + 1461515 * 2 ^ 59
def prefixEnd_1461515 : Nat := 4983230072969 + 3 ^ 40 * 1461515 * 2
def baseEnd_1461515 : Nat := 750459678755954549541121

theorem tailTrace_1461515 : CollatzResearch.WordTrace tailWord_1461515 prefixEnd_1461515 750459678755954549541121 := by
  unfold tailWord_1461515
  simp only [CollatzResearch.WordTrace]
  refine ⟨53305831300188236734889999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35537220866792157823259999 53305831300188236734889999)
  ·
    refine ⟨79958746950282355102334999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53305831300188236734889999 79958746950282355102334999)
    ·
      refine ⟨119938120425423532653502499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79958746950282355102334999 119938120425423532653502499)
      ·
        refine ⟨179907180638135298980253749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119938120425423532653502499 179907180638135298980253749)
        ·
          refine ⟨16866298184825184279398789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179907180638135298980253749 16866298184825184279398789)
          ·
            refine ⟨3162430909654722052387273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16866298184825184279398789 3162430909654722052387273)
            ·
              refine ⟨2371823182241041539290455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3162430909654722052387273 2371823182241041539290455)
              ·
                refine ⟨3557734773361562308935683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2371823182241041539290455 3557734773361562308935683)
                ·
                  refine ⟨5336602160042343463403525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3557734773361562308935683 5336602160042343463403525)
                  ·
                    refine ⟨1000612905007939399388161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5336602160042343463403525 1000612905007939399388161)
                    ·
                      refine ⟨750459678755954549541121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000612905007939399388161 750459678755954549541121)
                      ·
                        rfl

theorem cell23_1461515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 4, 2].length) (baseStart_1461515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461515 prefixEnd_1461515 := by exact prefixLift 1461515
  have htrace : WordTrace (prefixWord ++ tailWord_1461515) baseStart_1461515 baseEnd_1461515 := by
    simpa [prefixWord, tailWord_1461515, baseEnd_1461515] using wordTrace_append hprefix tailTrace_1461515
  have hstable : (prefixWord ++ tailWord_1461515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461515).length < 2 ^ (prefixWord ++ tailWord_1461515).sum := by decide
  have hdescent : baseEnd_1461515 < baseStart_1461515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461521 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 7]
def baseStart_1461521 : Nat := 118140960795 + 1461521 * 2 ^ 59
def prefixEnd_1461521 : Nat := 4983230072969 + 3 ^ 40 * 1461521 * 2
def baseEnd_1461521 : Nat := 83384751071097947340677

theorem tailTrace_1461521 : CollatzResearch.WordTrace tailWord_1461521 prefixEnd_1461521 83384751071097947340677 := by
  unfold tailWord_1461521
  simp only [CollatzResearch.WordTrace]
  refine ⟨53306050138166499759608417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35537366758777666506405611 53306050138166499759608417)
  ·
    refine ⟨39979537603624874819706313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53306050138166499759608417 39979537603624874819706313)
    ·
      refine ⟨29984653202718656114779735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39979537603624874819706313 29984653202718656114779735)
      ·
        refine ⟨44976979804077984172169603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29984653202718656114779735 44976979804077984172169603)
        ·
          refine ⟨67465469706116976258254405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44976979804077984172169603 67465469706116976258254405)
          ·
            refine ⟨12649775569896933048422701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67465469706116976258254405 12649775569896933048422701)
            ·
              refine ⟨4743665838711349893158513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12649775569896933048422701 4743665838711349893158513)
              ·
                refine ⟨3557749379033512419868885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4743665838711349893158513 3557749379033512419868885)
                ·
                  refine ⟨83384751071097947340677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3557749379033512419868885 83384751071097947340677)
                  ·
                    rfl

theorem cell23_1461521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 7].length) (baseStart_1461521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461521 prefixEnd_1461521 := by exact prefixLift 1461521
  have htrace : WordTrace (prefixWord ++ tailWord_1461521) baseStart_1461521 baseEnd_1461521 := by
    simpa [prefixWord, tailWord_1461521, baseEnd_1461521] using wordTrace_append hprefix tailTrace_1461521
  have hstable : (prefixWord ++ tailWord_1461521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461521).length < 2 ^ (prefixWord ++ tailWord_1461521).sum := by decide
  have hdescent : baseEnd_1461521 < baseStart_1461521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461531 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 3]
def baseStart_1461531 : Nat := 118140960795 + 1461531 * 2 ^ 59
def prefixEnd_1461531 : Nat := 4983230072969 + 3 ^ 40 * 1461531 * 2
def baseEnd_1461531 : Nat := 750467894446426486941047

theorem tailTrace_1461531 : CollatzResearch.WordTrace tailWord_1461531 prefixEnd_1461531 750467894446426486941047 := by
  unfold tailWord_1461531
  simp only [CollatzResearch.WordTrace]
  refine ⟨53306414868130271467472447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35537609912086847644981631 53306414868130271467472447)
  ·
    refine ⟨79959622302195407201208671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53306414868130271467472447 79959622302195407201208671)
    ·
      refine ⟨119939433453293110801813007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79959622302195407201208671 119939433453293110801813007)
      ·
        refine ⟨179909150179939666202719511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119939433453293110801813007 179909150179939666202719511)
        ·
          refine ⟨269863725269909499304079267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179909150179939666202719511 269863725269909499304079267)
          ·
            refine ⟨404795587904864248956118901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269863725269909499304079267 404795587904864248956118901)
            ·
              refine ⟨37949586366081023339636147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 404795587904864248956118901 37949586366081023339636147)
              ·
                refine ⟨56924379549121535009454221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37949586366081023339636147 56924379549121535009454221)
                ·
                  refine ⟨21346642330920575628545333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56924379549121535009454221 21346642330920575628545333)
                  ·
                    refine ⟨2001247718523803965176125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21346642330920575628545333 2001247718523803965176125)
                    ·
                      refine ⟨750467894446426486941047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2001247718523803965176125 750467894446426486941047)
                      ·
                        rfl

theorem cell23_1461531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 3].length) (baseStart_1461531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461531 prefixEnd_1461531 := by exact prefixLift 1461531
  have htrace : WordTrace (prefixWord ++ tailWord_1461531) baseStart_1461531 baseEnd_1461531 := by
    simpa [prefixWord, tailWord_1461531, baseEnd_1461531] using wordTrace_append hprefix tailTrace_1461531
  have hstable : (prefixWord ++ tailWord_1461531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461531).length < 2 ^ (prefixWord ++ tailWord_1461531).sum := by decide
  have hdescent : baseEnd_1461531 < baseStart_1461531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461536 : List Nat := [2, 1, 1, 5, 4, 1, 2, 1, 1, 3, 2]
def baseStart_1461536 : Nat := 118140960795 + 1461536 * 2 ^ 59
def prefixEnd_1461536 : Nat := 4983230072969 + 3 ^ 40 * 1461536 * 2
def baseEnd_1461536 : Nat := 750470461849698967378525

theorem tailTrace_1461536 : CollatzResearch.WordTrace tailWord_1461536 prefixEnd_1461536 750470461849698967378525 := by
  unfold tailWord_1461536
  simp only [CollatzResearch.WordTrace]
  refine ⟨26653298616556078660702231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35537731488741438214269641 26653298616556078660702231)
  ·
    refine ⟨39979947924834117991053347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26653298616556078660702231 39979947924834117991053347)
    ·
      refine ⟨59969921887251176986580021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39979947924834117991053347 59969921887251176986580021)
      ·
        refine ⟨5622180176929797842491877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59969921887251176986580021 5622180176929797842491877)
        ·
          refine ⟨1054158783174337095467227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5622180176929797842491877 1054158783174337095467227)
          ·
            refine ⟨1581238174761505643200841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054158783174337095467227 1581238174761505643200841)
            ·
              refine ⟨1185928631071129232400631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1581238174761505643200841 1185928631071129232400631)
              ·
                refine ⟨1778892946606693848600947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185928631071129232400631 1778892946606693848600947)
                ·
                  refine ⟨2668339419910040772901421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778892946606693848600947 2668339419910040772901421)
                  ·
                    refine ⟨1000627282466265289838033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2668339419910040772901421 1000627282466265289838033)
                    ·
                      refine ⟨750470461849698967378525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000627282466265289838033 750470461849698967378525)
                      ·
                        rfl

theorem cell23_1461536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_1461536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461536 prefixEnd_1461536 := by exact prefixLift 1461536
  have htrace : WordTrace (prefixWord ++ tailWord_1461536) baseStart_1461536 baseEnd_1461536 := by
    simpa [prefixWord, tailWord_1461536, baseEnd_1461536] using wordTrace_append hprefix tailTrace_1461536
  have hstable : (prefixWord ++ tailWord_1461536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461536).length < 2 ^ (prefixWord ++ tailWord_1461536).sum := by decide
  have hdescent : baseEnd_1461536 < baseStart_1461536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461549 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_1461549 : Nat := 118140960795 + 1461549 * 2 ^ 59
def prefixEnd_1461549 : Nat := 4983230072969 + 3 ^ 40 * 1461549 * 2
def baseEnd_1461549 : Nat := 750477137098207416515965

theorem tailTrace_1461549 : CollatzResearch.WordTrace tailWord_1461549 prefixEnd_1461549 750477137098207416515965 := by
  unfold tailWord_1461549
  simp only [CollatzResearch.WordTrace]
  refine ⟨53307071382065060541627701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35538047588043373694418467 53307071382065060541627701)
  ·
    refine ⟨4997537942068599425777597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53307071382065060541627701 4997537942068599425777597)
    ·
      refine ⟨1874076728275724784666599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4997537942068599425777597 1874076728275724784666599)
      ·
        refine ⟨2811115092413587176999899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1874076728275724784666599 2811115092413587176999899)
        ·
          refine ⟨4216672638620380765499849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2811115092413587176999899 4216672638620380765499849)
          ·
            refine ⟨3162504478965285574124887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4216672638620380765499849 3162504478965285574124887)
            ·
              refine ⟨4743756718447928361187331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3162504478965285574124887 4743756718447928361187331)
              ·
                refine ⟨7115635077671892541780997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4743756718447928361187331 7115635077671892541780997)
                ·
                  refine ⟨1334181577063479851583937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7115635077671892541780997 1334181577063479851583937)
                  ·
                    refine ⟨1000636182797609888687953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1334181577063479851583937 1000636182797609888687953)
                    ·
                      refine ⟨750477137098207416515965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000636182797609888687953 750477137098207416515965)
                      ·
                        rfl

theorem cell23_1461549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_1461549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461549 prefixEnd_1461549 := by exact prefixLift 1461549
  have htrace : WordTrace (prefixWord ++ tailWord_1461549) baseStart_1461549 baseEnd_1461549 := by
    simpa [prefixWord, tailWord_1461549, baseEnd_1461549] using wordTrace_append hprefix tailTrace_1461549
  have hstable : (prefixWord ++ tailWord_1461549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461549).length < 2 ^ (prefixWord ++ tailWord_1461549).sum := by decide
  have hdescent : baseEnd_1461549 < baseStart_1461549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461551 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 4, 5]
def baseStart_1461551 : Nat := 118140960795 + 1461551 * 2 ^ 59
def prefixEnd_1461551 : Nat := 4983230072969 + 3 ^ 40 * 1461551 * 2
def baseEnd_1461551 : Nat := 250159388019838802896985

theorem tailTrace_1461551 : CollatzResearch.WordTrace tailWord_1461551 prefixEnd_1461551 250159388019838802896985 := by
  unfold tailWord_1461551
  simp only [CollatzResearch.WordTrace]
  refine ⟨53307144328057814883200507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35538096218705209922133671 53307144328057814883200507)
  ·
    refine ⟨79960716492086722324800761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53307144328057814883200507 79960716492086722324800761)
    ·
      refine ⟨59970537369065041743600571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79960716492086722324800761 59970537369065041743600571)
      ·
        refine ⟨89955806053597562615400857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59970537369065041743600571 89955806053597562615400857)
        ·
          refine ⟨67466854540198171961550643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89955806053597562615400857 67466854540198171961550643)
          ·
            refine ⟨101200281810297257942325965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67466854540198171961550643 101200281810297257942325965)
            ·
              refine ⟨37950105678861471728372237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101200281810297257942325965 37950105678861471728372237)
              ·
                refine ⟨14231289629573051898139589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37950105678861471728372237 14231289629573051898139589)
                ·
                  refine ⟨2668366805544947230901173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14231289629573051898139589 2668366805544947230901173)
                  ·
                    refine ⟨250159388019838802896985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2668366805544947230901173 250159388019838802896985)
                    ·
                      rfl

theorem cell23_1461551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 5].length) (baseStart_1461551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461551 prefixEnd_1461551 := by exact prefixLift 1461551
  have htrace : WordTrace (prefixWord ++ tailWord_1461551) baseStart_1461551 baseEnd_1461551 := by
    simpa [prefixWord, tailWord_1461551, baseEnd_1461551] using wordTrace_append hprefix tailTrace_1461551
  have hstable : (prefixWord ++ tailWord_1461551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461551).length < 2 ^ (prefixWord ++ tailWord_1461551).sum := by decide
  have hdescent : baseEnd_1461551 < baseStart_1461551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461588 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_1461588 : Nat := 118140960795 + 1461588 * 2 ^ 59
def prefixEnd_1461588 : Nat := 4983230072969 + 3 ^ 40 * 1461588 * 2
def baseEnd_1461588 : Nat := 750497162843732763928285

theorem tailTrace_1461588 : CollatzResearch.WordTrace tailWord_1461588 prefixEnd_1461588 750497162843732763928285 := by
  unfold tailWord_1461588
  simp only [CollatzResearch.WordTrace]
  refine ⟨26654246914461885101148709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35538995885949180134864945 26654246914461885101148709)
  ·
    refine ⟨4997671296461603456465383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26654246914461885101148709 4997671296461603456465383)
    ·
      refine ⟨7496506944692405184698075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4997671296461603456465383 7496506944692405184698075)
      ·
        refine ⟨11244760417038607777047113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7496506944692405184698075 11244760417038607777047113)
        ·
          refine ⟨8433570312778955832785335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11244760417038607777047113 8433570312778955832785335)
          ·
            refine ⟨12650355469168433749178003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8433570312778955832785335 12650355469168433749178003)
            ·
              refine ⟨18975533203752650623767005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12650355469168433749178003 18975533203752650623767005)
              ·
                refine ⟨7115824951407243983912627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18975533203752650623767005 7115824951407243983912627)
                ·
                  refine ⟨10673737427110865975868941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7115824951407243983912627 10673737427110865975868941)
                  ·
                    refine ⟨4002651535166574740950853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10673737427110865975868941 4002651535166574740950853)
                    ·
                      refine ⟨750497162843732763928285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4002651535166574740950853 750497162843732763928285)
                      ·
                        rfl

theorem cell23_1461588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_1461588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461588 prefixEnd_1461588 := by exact prefixLift 1461588
  have htrace : WordTrace (prefixWord ++ tailWord_1461588) baseStart_1461588 baseEnd_1461588 := by
    simpa [prefixWord, tailWord_1461588, baseEnd_1461588] using wordTrace_append hprefix tailTrace_1461588
  have hstable : (prefixWord ++ tailWord_1461588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461588).length < 2 ^ (prefixWord ++ tailWord_1461588).sum := by decide
  have hdescent : baseEnd_1461588 < baseStart_1461588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461601 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_1461601 : Nat := 118140960795 + 1461601 * 2 ^ 59
def prefixEnd_1461601 : Nat := 4983230072969 + 3 ^ 40 * 1461601 * 2
def baseEnd_1461601 : Nat := 750503838092241213065725

theorem tailTrace_1461601 : CollatzResearch.WordTrace tailWord_1461601 prefixEnd_1461601 750503838092241213065725 := by
  unfold tailWord_1461601
  simp only [CollatzResearch.WordTrace]
  refine ⟨53308967977876673422520657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35539311985251115615013771 53308967977876673422520657)
  ·
    refine ⟨39981725983407505066890493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53308967977876673422520657 39981725983407505066890493)
    ·
      refine ⟨14993147243777814400083935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39981725983407505066890493 14993147243777814400083935)
      ·
        refine ⟨22489720865666721600125903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14993147243777814400083935 22489720865666721600125903)
        ·
          refine ⟨33734581298500082400188855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22489720865666721600125903 33734581298500082400188855)
          ·
            refine ⟨50601871947750123600283283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33734581298500082400188855 50601871947750123600283283)
            ·
              refine ⟨75902807921625185400424925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50601871947750123600283283 75902807921625185400424925)
              ·
                refine ⟨28463552970609444525159347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75902807921625185400424925 28463552970609444525159347)
                ·
                  refine ⟨42695329455914166787739021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28463552970609444525159347 42695329455914166787739021)
                  ·
                    refine ⟨16010748545967812545402133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42695329455914166787739021 16010748545967812545402133)
                    ·
                      refine ⟨750503838092241213065725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16010748545967812545402133 750503838092241213065725)
                      ·
                        rfl

theorem cell23_1461601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_1461601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461601 prefixEnd_1461601 := by exact prefixLift 1461601
  have htrace : WordTrace (prefixWord ++ tailWord_1461601) baseStart_1461601 baseEnd_1461601 := by
    simpa [prefixWord, tailWord_1461601, baseEnd_1461601] using wordTrace_append hprefix tailTrace_1461601
  have hstable : (prefixWord ++ tailWord_1461601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461601).length < 2 ^ (prefixWord ++ tailWord_1461601).sum := by decide
  have hdescent : baseEnd_1461601 < baseStart_1461601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461628 : List Nat := [2, 2, 2, 1, 1, 1, 5, 3, 6]
def baseStart_1461628 : Nat := 118140960795 + 1461628 * 2 ^ 59
def prefixEnd_1461628 : Nat := 4983230072969 + 3 ^ 40 * 1461628 * 2
def baseEnd_1461628 : Nat := 83390855785545845269789

theorem tailTrace_1461628 : CollatzResearch.WordTrace tailWord_1461628 prefixEnd_1461628 83390855785545845269789 := by
  unfold tailWord_1461628
  simp only [CollatzResearch.WordTrace]
  refine ⟨26654976374389428516876769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35539968499185904689169025 26654976374389428516876769)
  ·
    refine ⟨19991232280792071387657577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26654976374389428516876769 19991232280792071387657577)
    ·
      refine ⟨14993424210594053540743183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19991232280792071387657577 14993424210594053540743183)
      ·
        refine ⟨22490136315891080311114775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14993424210594053540743183 22490136315891080311114775)
        ·
          refine ⟨33735204473836620466672163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22490136315891080311114775 33735204473836620466672163)
          ·
            refine ⟨50602806710754930700008245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33735204473836620466672163 50602806710754930700008245)
            ·
              refine ⟨4744013129133274753125773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50602806710754930700008245 4744013129133274753125773)
              ·
                refine ⟨1779004923424978032422165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4744013129133274753125773 1779004923424978032422165)
                ·
                  refine ⟨83390855785545845269789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1779004923424978032422165 83390855785545845269789)
                  ·
                    rfl

theorem cell23_1461628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 6].length) (baseStart_1461628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461628 prefixEnd_1461628 := by exact prefixLift 1461628
  have htrace : WordTrace (prefixWord ++ tailWord_1461628) baseStart_1461628 baseEnd_1461628 := by
    simpa [prefixWord, tailWord_1461628, baseEnd_1461628] using wordTrace_append hprefix tailTrace_1461628
  have hstable : (prefixWord ++ tailWord_1461628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461628).length < 2 ^ (prefixWord ++ tailWord_1461628).sum := by decide
  have hdescent : baseEnd_1461628 < baseStart_1461628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461651 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 7]
def baseStart_1461651 : Nat := 118140960795 + 1461651 * 2 ^ 59
def prefixEnd_1461651 : Nat := 4983230072969 + 3 ^ 40 * 1461651 * 2
def baseEnd_1461651 : Nat := 750529512124966017440495

theorem tailTrace_1461651 : CollatzResearch.WordTrace tailWord_1461651 prefixEnd_1461651 750529512124966017440495 := by
  unfold tailWord_1461651
  simp only [CollatzResearch.WordTrace]
  refine ⟨53310791627695531961840807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35540527751797021307893871 53310791627695531961840807)
  ·
    refine ⟨79966187441543297942761211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53310791627695531961840807 79966187441543297942761211)
    ·
      refine ⟨119949281162314946914141817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79966187441543297942761211 119949281162314946914141817)
      ·
        refine ⟨89961960871736210185606363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119949281162314946914141817 89961960871736210185606363)
        ·
          refine ⟨134942941307604315278409545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89961960871736210185606363 134942941307604315278409545)
          ·
            refine ⟨101207205980703236458807159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134942941307604315278409545 101207205980703236458807159)
            ·
              refine ⟨151810808971054854688210739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101207205980703236458807159 151810808971054854688210739)
              ·
                refine ⟨227716213456582282032316109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151810808971054854688210739 227716213456582282032316109)
                ·
                  refine ⟨85393580046218355762118541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227716213456582282032316109 85393580046218355762118541)
                  ·
                    refine ⟨32022592517331883410794453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85393580046218355762118541 32022592517331883410794453)
                    ·
                      refine ⟨750529512124966017440495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32022592517331883410794453 750529512124966017440495)
                      ·
                        rfl

theorem cell23_1461651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_1461651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461651 prefixEnd_1461651 := by exact prefixLift 1461651
  have htrace : WordTrace (prefixWord ++ tailWord_1461651) baseStart_1461651 baseEnd_1461651 := by
    simpa [prefixWord, tailWord_1461651, baseEnd_1461651] using wordTrace_append hprefix tailTrace_1461651
  have hstable : (prefixWord ++ tailWord_1461651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461651).length < 2 ^ (prefixWord ++ tailWord_1461651).sum := by decide
  have hdescent : baseEnd_1461651 < baseStart_1461651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461666 : List Nat := [3, 3, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_1461666 : Nat := 118140960795 + 1461666 * 2 ^ 59
def prefixEnd_1461666 : Nat := 4983230072969 + 3 ^ 40 * 1461666 * 2
def baseEnd_1461666 : Nat := 250179071444927819584309

theorem tailTrace_1461666 : CollatzResearch.WordTrace tailWord_1461666 prefixEnd_1461666 250179071444927819584309 := by
  unfold tailWord_1461666
  simp only [CollatzResearch.WordTrace]
  refine ⟨13327834680660297380909213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35540892481760793015757901 13327834680660297380909213)
  ·
    refine ⟨4997938005247611517840955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13327834680660297380909213 4997938005247611517840955)
    ·
      refine ⟨7496907007871417276761433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4997938005247611517840955 7496907007871417276761433)
      ·
        refine ⟨5622680255903562957571075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7496907007871417276761433 5622680255903562957571075)
        ·
          refine ⟨8434020383855344436356613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5622680255903562957571075 8434020383855344436356613)
          ·
            refine ⟨1581378821972877081816865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8434020383855344436356613 1581378821972877081816865)
            ·
              refine ⟨1186034116479657811362649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1581378821972877081816865 1186034116479657811362649)
              ·
                refine ⟨889525587359743358521987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1186034116479657811362649 889525587359743358521987)
                ·
                  refine ⟨1334288381039615037782981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889525587359743358521987 1334288381039615037782981)
                  ·
                    refine ⟨250179071444927819584309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1334288381039615037782981 250179071444927819584309)
                    ·
                      rfl

theorem cell23_1461666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_1461666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461666 prefixEnd_1461666 := by exact prefixLift 1461666
  have htrace : WordTrace (prefixWord ++ tailWord_1461666) baseStart_1461666 baseEnd_1461666 := by
    simpa [prefixWord, tailWord_1461666, baseEnd_1461666] using wordTrace_append hprefix tailTrace_1461666
  have hstable : (prefixWord ++ tailWord_1461666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461666).length < 2 ^ (prefixWord ++ tailWord_1461666).sum := by decide
  have hdescent : baseEnd_1461666 < baseStart_1461666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461688 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 1, 6]
def baseStart_1461688 : Nat := 118140960795 + 1461688 * 2 ^ 59
def prefixEnd_1461688 : Nat := 4983230072969 + 3 ^ 40 * 1461688 * 2
def baseEnd_1461688 : Nat := 250182836969727457559275

theorem tailTrace_1461688 : CollatzResearch.WordTrace tailWord_1461688 prefixEnd_1461688 250182836969727457559275 := by
  unfold tailWord_1461688
  simp only [CollatzResearch.WordTrace]
  refine ⟨26656070564280743640468859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35541427419040991520625145 26656070564280743640468859)
  ·
    refine ⟨39984105846421115460703289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26656070564280743640468859 39984105846421115460703289)
    ·
      refine ⟨29988079384815836595527467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39984105846421115460703289 29988079384815836595527467)
      ·
        refine ⟨44982119077223754893291201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29988079384815836595527467 44982119077223754893291201)
        ·
          refine ⟨33736589307917816169968401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44982119077223754893291201 33736589307917816169968401)
          ·
            refine ⟨25302441980938362127476301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33736589307917816169968401 25302441980938362127476301)
            ·
              refine ⟨9488415742851885797803613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25302441980938362127476301 9488415742851885797803613)
              ·
                refine ⟨3558155903569457174176355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9488415742851885797803613 3558155903569457174176355)
                ·
                  refine ⟨5337233855354185761264533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3558155903569457174176355 5337233855354185761264533)
                  ·
                    refine ⟨250182836969727457559275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5337233855354185761264533 250182836969727457559275)
                    ·
                      rfl

theorem cell23_1461688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_1461688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461688 prefixEnd_1461688 := by exact prefixLift 1461688
  have htrace : WordTrace (prefixWord ++ tailWord_1461688) baseStart_1461688 baseEnd_1461688 := by
    simpa [prefixWord, tailWord_1461688, baseEnd_1461688] using wordTrace_append hprefix tailTrace_1461688
  have hstable : (prefixWord ++ tailWord_1461688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461688).length < 2 ^ (prefixWord ++ tailWord_1461688).sum := by decide
  have hdescent : baseEnd_1461688 < baseStart_1461688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461722 : List Nat := [3, 1, 1, 2, 3, 2, 3, 2, 2, 4]
def baseStart_1461722 : Nat := 118140960795 + 1461722 * 2 ^ 59
def prefixEnd_1461722 : Nat := 4983230072969 + 3 ^ 40 * 1461722 * 2
def baseEnd_1461722 : Nat := 250188656417145079884223

theorem tailTrace_1461722 : CollatzResearch.WordTrace tailWord_1461722 prefixEnd_1461722 250188656417145079884223 := by
  unfold tailWord_1461722
  simp only [CollatzResearch.WordTrace]
  refine ⟨13328345302609577771918855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35542254140292207391783613 13328345302609577771918855)
  ·
    refine ⟨19992517953914366657878283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13328345302609577771918855 19992517953914366657878283)
    ·
      refine ⟨29988776930871549986817425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19992517953914366657878283 29988776930871549986817425)
      ·
        refine ⟨22491582698153662490113069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29988776930871549986817425 22491582698153662490113069)
        ·
          refine ⟨8434343511807623433792401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22491582698153662490113069 8434343511807623433792401)
          ·
            refine ⟨6325757633855717575344301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8434343511807623433792401 6325757633855717575344301)
            ·
              refine ⟨2372159112695894090754113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6325757633855717575344301 2372159112695894090754113)
              ·
                refine ⟨1779119334521920568065585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2372159112695894090754113 1779119334521920568065585)
                ·
                  refine ⟨1334339500891440426049189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1779119334521920568065585 1334339500891440426049189)
                  ·
                    refine ⟨250188656417145079884223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1334339500891440426049189 250188656417145079884223)
                    ·
                      rfl

theorem cell23_1461722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_1461722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461722 prefixEnd_1461722 := by exact prefixLift 1461722
  have htrace : WordTrace (prefixWord ++ tailWord_1461722) baseStart_1461722 baseEnd_1461722 := by
    simpa [prefixWord, tailWord_1461722, baseEnd_1461722] using wordTrace_append hprefix tailTrace_1461722
  have hstable : (prefixWord ++ tailWord_1461722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461722).length < 2 ^ (prefixWord ++ tailWord_1461722).sum := by decide
  have hdescent : baseEnd_1461722 < baseStart_1461722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461729 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 3, 2, 2]
def baseStart_1461729 : Nat := 118140960795 + 1461729 * 2 ^ 59
def prefixEnd_1461729 : Nat := 4983230072969 + 3 ^ 40 * 1461729 * 2
def baseEnd_1461729 : Nat := 750569563616016712265137

theorem tailTrace_1461729 : CollatzResearch.WordTrace tailWord_1461729 prefixEnd_1461729 750569563616016712265137 := by
  unfold tailWord_1461729
  simp only [CollatzResearch.WordTrace]
  refine ⟨53313636521412951283180241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35542424347608634188786827 53313636521412951283180241)
  ·
    refine ⟨39985227391059713462385181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53313636521412951283180241 39985227391059713462385181)
    ·
      refine ⟨14994460271647392548394443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39985227391059713462385181 14994460271647392548394443)
      ·
        refine ⟨22491690407471088822591665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14994460271647392548394443 22491690407471088822591665)
        ·
          refine ⟨16868767805603316616943749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22491690407471088822591665 16868767805603316616943749)
          ·
            refine ⟨3162893963550621865676953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16868767805603316616943749 3162893963550621865676953)
            ·
              refine ⟨2372170472662966399257715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3162893963550621865676953 2372170472662966399257715)
              ·
                refine ⟨3558255708994449598886573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2372170472662966399257715 3558255708994449598886573)
                ·
                  refine ⟨1334345890872918599582465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3558255708994449598886573 1334345890872918599582465)
                  ·
                    refine ⟨1000759418154688949686849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1334345890872918599582465 1000759418154688949686849)
                    ·
                      refine ⟨750569563616016712265137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000759418154688949686849 750569563616016712265137)
                      ·
                        rfl

theorem cell23_1461729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_1461729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461729 prefixEnd_1461729 := by exact prefixLift 1461729
  have htrace : WordTrace (prefixWord ++ tailWord_1461729) baseStart_1461729 baseEnd_1461729 := by
    simpa [prefixWord, tailWord_1461729, baseEnd_1461729] using wordTrace_append hprefix tailTrace_1461729
  have hstable : (prefixWord ++ tailWord_1461729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461729).length < 2 ^ (prefixWord ++ tailWord_1461729).sum := by decide
  have hdescent : baseEnd_1461729 < baseStart_1461729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461749 : List Nat := [1, 3, 5, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1461749 : Nat := 118140960795 + 1461749 * 2 ^ 59
def prefixEnd_1461749 : Nat := 4983230072969 + 3 ^ 40 * 1461749 * 2
def baseEnd_1461749 : Nat := 750579833229106634015045

theorem tailTrace_1461749 : CollatzResearch.WordTrace tailWord_1461749 prefixEnd_1461749 750579833229106634015045 := by
  unfold tailWord_1461749
  simp only [CollatzResearch.WordTrace]
  refine ⟨53314365981340494698908301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35542910654226996465938867 53314365981340494698908301)
  ·
    refine ⟨19992887243002685512090613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53314365981340494698908301 19992887243002685512090613)
    ·
      refine ⟨1874333179031501766758495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19992887243002685512090613 1874333179031501766758495)
      ·
        refine ⟨2811499768547252650137743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1874333179031501766758495 2811499768547252650137743)
        ·
          refine ⟨4217249652820878975206615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2811499768547252650137743 4217249652820878975206615)
          ·
            refine ⟨6325874479231318462809923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4217249652820878975206615 6325874479231318462809923)
            ·
              refine ⟨9488811718846977694214885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6325874479231318462809923 9488811718846977694214885)
              ·
                refine ⟨1779152197283808317665291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9488811718846977694214885 1779152197283808317665291)
                ·
                  refine ⟨2668728295925712476497937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1779152197283808317665291 2668728295925712476497937)
                  ·
                    refine ⟨2001546221944284357373453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2668728295925712476497937 2001546221944284357373453)
                    ·
                      refine ⟨750579833229106634015045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2001546221944284357373453 750579833229106634015045)
                      ·
                        rfl

theorem cell23_1461749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1461749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461749 prefixEnd_1461749 := by exact prefixLift 1461749
  have htrace : WordTrace (prefixWord ++ tailWord_1461749) baseStart_1461749 baseEnd_1461749 := by
    simpa [prefixWord, tailWord_1461749, baseEnd_1461749] using wordTrace_append hprefix tailTrace_1461749
  have hstable : (prefixWord ++ tailWord_1461749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461749).length < 2 ^ (prefixWord ++ tailWord_1461749).sum := by decide
  have hdescent : baseEnd_1461749 < baseStart_1461749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461780 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_1461780 : Nat := 118140960795 + 1461780 * 2 ^ 59
def prefixEnd_1461780 : Nat := 4983230072969 + 3 ^ 40 * 1461780 * 2
def baseEnd_1461780 : Nat := 750595751129396012727403

theorem tailTrace_1461780 : CollatzResearch.WordTrace tailWord_1461780 prefixEnd_1461780 750595751129396012727403 := by
  unfold tailWord_1461780
  simp only [CollatzResearch.WordTrace]
  refine ⟨26657748322114093496643397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35543664429485457995524529 26657748322114093496643397)
  ·
    refine ⟨4998327810396392530620637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26657748322114093496643397 4998327810396392530620637)
    ·
      refine ⟨1874372928898647198982739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4998327810396392530620637 1874372928898647198982739)
      ·
        refine ⟨2811559393347970798474109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1874372928898647198982739 2811559393347970798474109)
        ·
          refine ⟨1054334772505489049427791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2811559393347970798474109 1054334772505489049427791)
          ·
            refine ⟨1581502158758233574141687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054334772505489049427791 1581502158758233574141687)
            ·
              refine ⟨2372253238137350361212531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1581502158758233574141687 2372253238137350361212531)
              ·
                refine ⟨3558379857206025541818797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2372253238137350361212531 3558379857206025541818797)
                ·
                  refine ⟨1334392446452259578182049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3558379857206025541818797 1334392446452259578182049)
                  ·
                    refine ⟨1000794334839194683636537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1334392446452259578182049 1000794334839194683636537)
                    ·
                      refine ⟨750595751129396012727403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000794334839194683636537 750595751129396012727403)
                      ·
                        rfl

theorem cell23_1461780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_1461780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461780 prefixEnd_1461780 := by exact prefixLift 1461780
  have htrace : WordTrace (prefixWord ++ tailWord_1461780) baseStart_1461780 baseEnd_1461780 := by
    simpa [prefixWord, tailWord_1461780, baseEnd_1461780] using wordTrace_append hprefix tailTrace_1461780
  have hstable : (prefixWord ++ tailWord_1461780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461780).length < 2 ^ (prefixWord ++ tailWord_1461780).sum := by decide
  have hdescent : baseEnd_1461780 < baseStart_1461780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461785 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 2, 8, 2]
def baseStart_1461785 : Nat := 118140960795 + 1461785 * 2 ^ 59
def prefixEnd_1461785 : Nat := 4983230072969 + 3 ^ 40 * 1461785 * 2
def baseEnd_1461785 : Nat := 750598318532668493164879

theorem tailTrace_1461785 : CollatzResearch.WordTrace tailWord_1461785 prefixEnd_1461785 750598318532668493164879 := by
  unfold tailWord_1461785
  simp only [CollatzResearch.WordTrace]
  refine ⟨53315679009210072847218809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35543786006140048564812539 53315679009210072847218809)
  ·
    refine ⟨39986759256907554635414107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53315679009210072847218809 39986759256907554635414107)
    ·
      refine ⟨59980138885361331953121161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39986759256907554635414107 59980138885361331953121161)
      ·
        refine ⟨44985104164020998964840871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59980138885361331953121161 44985104164020998964840871)
        ·
          refine ⟨67477656246031498447261307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44985104164020998964840871 67477656246031498447261307)
          ·
            refine ⟨101216484369047247670891961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67477656246031498447261307 101216484369047247670891961)
            ·
              refine ⟨75912363276785435753168971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101216484369047247670891961 75912363276785435753168971)
              ·
                refine ⟨113868544915178153629753457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75912363276785435753168971 113868544915178153629753457)
                ·
                  refine ⟨85401408686383615222315093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113868544915178153629753457 85401408686383615222315093)
                  ·
                    refine ⟨1000797758043557990886505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85401408686383615222315093 1000797758043557990886505)
                    ·
                      refine ⟨750598318532668493164879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000797758043557990886505 750598318532668493164879)
                      ·
                        rfl

theorem cell23_1461785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 8, 2].length) (baseStart_1461785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461785 prefixEnd_1461785 := by exact prefixLift 1461785
  have htrace : WordTrace (prefixWord ++ tailWord_1461785) baseStart_1461785 baseEnd_1461785 := by
    simpa [prefixWord, tailWord_1461785, baseEnd_1461785] using wordTrace_append hprefix tailTrace_1461785
  have hstable : (prefixWord ++ tailWord_1461785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461785).length < 2 ^ (prefixWord ++ tailWord_1461785).sum := by decide
  have hdescent : baseEnd_1461785 < baseStart_1461785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461806 : List Nat := [4, 1, 3, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_1461806 : Nat := 118140960795 + 1461806 * 2 ^ 59
def prefixEnd_1461806 : Nat := 4983230072969 + 3 ^ 40 * 1461806 * 2
def baseEnd_1461806 : Nat := 750609101626412911002283

theorem tailTrace_1461806 : CollatzResearch.WordTrace tailWord_1461806 prefixEnd_1461806 750609101626412911002283 := by
  unfold tailWord_1461806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6664555617766749179216659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35544296628089328955822181 6664555617766749179216659)
  ·
    refine ⟨9996833426650123768824989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6664555617766749179216659 9996833426650123768824989)
    ·
      refine ⟨3748812534993796413309371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9996833426650123768824989 3748812534993796413309371)
      ·
        refine ⟨5623218802490694619964057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3748812534993796413309371 5623218802490694619964057)
        ·
          refine ⟨4217414101868020964973043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5623218802490694619964057 4217414101868020964973043)
          ·
            refine ⟨6326121152802031447459565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4217414101868020964973043 6326121152802031447459565)
            ·
              refine ⟨2372295432300761792797337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6326121152802031447459565 2372295432300761792797337)
              ·
                refine ⟨1779221574225571344598003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2372295432300761792797337 1779221574225571344598003)
                ·
                  refine ⟨2668832361338357016897005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1779221574225571344598003 2668832361338357016897005)
                  ·
                    refine ⟨1000812135501883881336377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2668832361338357016897005 1000812135501883881336377)
                    ·
                      refine ⟨750609101626412911002283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000812135501883881336377 750609101626412911002283)
                      ·
                        rfl

theorem cell23_1461806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_1461806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461806 prefixEnd_1461806 := by exact prefixLift 1461806
  have htrace : WordTrace (prefixWord ++ tailWord_1461806) baseStart_1461806 baseEnd_1461806 := by
    simpa [prefixWord, tailWord_1461806, baseEnd_1461806] using wordTrace_append hprefix tailTrace_1461806
  have hstable : (prefixWord ++ tailWord_1461806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461806).length < 2 ^ (prefixWord ++ tailWord_1461806).sum := by decide
  have hdescent : baseEnd_1461806 < baseStart_1461806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461808 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 9]
def baseStart_1461808 : Nat := 118140960795 + 1461808 * 2 ^ 59
def prefixEnd_1461808 : Nat := 4983230072969 + 3 ^ 40 * 1461808 * 2
def baseEnd_1461808 : Nat := 83401125398635767019697

theorem tailTrace_1461808 : CollatzResearch.WordTrace tailWord_1461808 prefixEnd_1461808 83401125398635767019697 := by
  unfold tailWord_1461808
  simp only [CollatzResearch.WordTrace]
  refine ⟨26658258944063373887653039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35544345258751165183537385 26658258944063373887653039)
  ·
    refine ⟨39987388416095060831479559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26658258944063373887653039 39987388416095060831479559)
    ·
      refine ⟨59981082624142591247219339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39987388416095060831479559 59981082624142591247219339)
      ·
        refine ⟨89971623936213886870829009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59981082624142591247219339 89971623936213886870829009)
        ·
          refine ⟨67478717952160415153121757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89971623936213886870829009 67478717952160415153121757)
          ·
            refine ⟨25304519232060155682420659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67478717952160415153121757 25304519232060155682420659)
            ·
              refine ⟨37956778848090233523630989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25304519232060155682420659 37956778848090233523630989)
              ·
                refine ⟨14233792068033837571361621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37956778848090233523630989 14233792068033837571361621)
                ·
                  refine ⟨83401125398635767019697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14233792068033837571361621 83401125398635767019697)
                  ·
                    rfl

theorem cell23_1461808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 9].length) (baseStart_1461808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461808 prefixEnd_1461808 := by exact prefixLift 1461808
  have htrace : WordTrace (prefixWord ++ tailWord_1461808) baseStart_1461808 baseEnd_1461808 := by
    simpa [prefixWord, tailWord_1461808, baseEnd_1461808] using wordTrace_append hprefix tailTrace_1461808
  have hstable : (prefixWord ++ tailWord_1461808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461808).length < 2 ^ (prefixWord ++ tailWord_1461808).sum := by decide
  have hdescent : baseEnd_1461808 < baseStart_1461808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461835 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 3]
def baseStart_1461835 : Nat := 118140960795 + 1461835 * 2 ^ 59
def prefixEnd_1461835 : Nat := 4983230072969 + 3 ^ 40 * 1461835 * 2
def baseEnd_1461835 : Nat := 750623992565393297539649

theorem tailTrace_1461835 : CollatzResearch.WordTrace tailWord_1461835 prefixEnd_1461835 750623992565393297539649 := by
  unfold tailWord_1461835
  simp only [CollatzResearch.WordTrace]
  refine ⟨53317502659028931386538959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35545001772685954257692639 53317502659028931386538959)
  ·
    refine ⟨79976253988543397079808439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53317502659028931386538959 79976253988543397079808439)
    ·
      refine ⟨119964380982815095619712659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79976253988543397079808439 119964380982815095619712659)
      ·
        refine ⟨179946571474222643429568989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119964380982815095619712659 179946571474222643429568989)
        ·
          refine ⟨67479964302833491286088371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179946571474222643429568989 67479964302833491286088371)
          ·
            refine ⟨101219946454250236929132557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67479964302833491286088371 101219946454250236929132557)
            ·
              refine ⟨37957479920343838848424709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101219946454250236929132557 37957479920343838848424709)
              ·
                refine ⟨7117027485064469784079633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37957479920343838848424709 7117027485064469784079633)
                ·
                  refine ⟨5337770613798352338059725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7117027485064469784079633 5337770613798352338059725)
                  ·
                    refine ⟨2001663980174382126772397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5337770613798352338059725 2001663980174382126772397)
                    ·
                      refine ⟨750623992565393297539649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2001663980174382126772397 750623992565393297539649)
                      ·
                        rfl

theorem cell23_1461835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 3].length) (baseStart_1461835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461835 prefixEnd_1461835 := by exact prefixLift 1461835
  have htrace : WordTrace (prefixWord ++ tailWord_1461835) baseStart_1461835 baseEnd_1461835 := by
    simpa [prefixWord, tailWord_1461835, baseEnd_1461835] using wordTrace_append hprefix tailTrace_1461835
  have hstable : (prefixWord ++ tailWord_1461835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461835).length < 2 ^ (prefixWord ++ tailWord_1461835).sum := by decide
  have hdescent : baseEnd_1461835 < baseStart_1461835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461836 : List Nat := [2, 2, 1, 3, 1, 4, 2, 2, 2, 2, 2]
def baseStart_1461836 : Nat := 118140960795 + 1461836 * 2 ^ 59
def prefixEnd_1461836 : Nat := 4983230072969 + 3 ^ 40 * 1461836 * 2
def baseEnd_1461836 : Nat := 750624506046047793627145

theorem tailTrace_1461836 : CollatzResearch.WordTrace tailWord_1461836 prefixEnd_1461836 750624506046047793627145 := by
  unfold tailWord_1461836
  simp only [CollatzResearch.WordTrace]
  refine ⟨26658769566012654278662681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35545026088016872371550241 26658769566012654278662681)
  ·
    refine ⟨19994077174509490708997011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26658769566012654278662681 19994077174509490708997011)
    ·
      refine ⟨29991115761764236063495517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19994077174509490708997011 29991115761764236063495517)
      ·
        refine ⟨11246668410661588523810819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29991115761764236063495517 11246668410661588523810819)
        ·
          refine ⟨16870002615992382785716229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11246668410661588523810819 16870002615992382785716229)
          ·
            refine ⟨3163125490498571772321793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16870002615992382785716229 3163125490498571772321793)
            ·
              refine ⟨2372344117873928829241345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3163125490498571772321793 2372344117873928829241345)
              ·
                refine ⟨1779258088405446621931009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2372344117873928829241345 1779258088405446621931009)
                ·
                  refine ⟨1334443566304084966448257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1779258088405446621931009 1334443566304084966448257)
                  ·
                    refine ⟨1000832674728063724836193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1334443566304084966448257 1000832674728063724836193)
                    ·
                      refine ⟨750624506046047793627145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000832674728063724836193 750624506046047793627145)
                      ·
                        rfl

theorem cell23_1461836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_1461836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461836 prefixEnd_1461836 := by exact prefixLift 1461836
  have htrace : WordTrace (prefixWord ++ tailWord_1461836) baseStart_1461836 baseEnd_1461836 := by
    simpa [prefixWord, tailWord_1461836, baseEnd_1461836] using wordTrace_append hprefix tailTrace_1461836
  have hstable : (prefixWord ++ tailWord_1461836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461836).length < 2 ^ (prefixWord ++ tailWord_1461836).sum := by decide
  have hdescent : baseEnd_1461836 < baseStart_1461836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461846 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1461846 : Nat := 118140960795 + 1461846 * 2 ^ 59
def prefixEnd_1461846 : Nat := 4983230072969 + 3 ^ 40 * 1461846 * 2
def baseEnd_1461846 : Nat := 250209880284197584834033

theorem tailTrace_1461846 : CollatzResearch.WordTrace tailWord_1461846 prefixEnd_1461846 250209880284197584834033 := by
  unfold tailWord_1461846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3332368991374317516574337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35545269241326053510126261 3332368991374317516574337)
  ·
    refine ⟨2499276743530738137430753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3332368991374317516574337 2499276743530738137430753)
    ·
      refine ⟨1874457557648053603073065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2499276743530738137430753 1874457557648053603073065)
      ·
        refine ⟨1405843168236040202304799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1874457557648053603073065 1405843168236040202304799)
        ·
          refine ⟨2108764752354060303457199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405843168236040202304799 2108764752354060303457199)
          ·
            refine ⟨3163147128531090455185799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108764752354060303457199 3163147128531090455185799)
            ·
              refine ⟨4744720692796635682778699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3163147128531090455185799 4744720692796635682778699)
              ·
                refine ⟨7117081039194953524168049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4744720692796635682778699 7117081039194953524168049)
                ·
                  refine ⟨5337810779396215143126037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7117081039194953524168049 5337810779396215143126037)
                  ·
                    refine ⟨250209880284197584834033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5337810779396215143126037 250209880284197584834033)
                    ·
                      rfl

theorem cell23_1461846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1461846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461846 prefixEnd_1461846 := by exact prefixLift 1461846
  have htrace : WordTrace (prefixWord ++ tailWord_1461846) baseStart_1461846 baseEnd_1461846 := by
    simpa [prefixWord, tailWord_1461846, baseEnd_1461846] using wordTrace_append hprefix tailTrace_1461846
  have hstable : (prefixWord ++ tailWord_1461846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461846).length < 2 ^ (prefixWord ++ tailWord_1461846).sum := by decide
  have hdescent : baseEnd_1461846 < baseStart_1461846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461852 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1461852 : Nat := 118140960795 + 1461852 * 2 ^ 59
def prefixEnd_1461852 : Nat := 4983230072969 + 3 ^ 40 * 1461852 * 2
def baseEnd_1461852 : Nat := 750632721736519731027071

theorem tailTrace_1461852 : CollatzResearch.WordTrace tailWord_1461852 prefixEnd_1461852 750632721736519731027071 := by
  unfold tailWord_1461852
  simp only [CollatzResearch.WordTrace]
  refine ⟨26659061349983671644953905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35545415133311562193271873 26659061349983671644953905)
  ·
    refine ⟨19994296012487753733715429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26659061349983671644953905 19994296012487753733715429)
    ·
      refine ⟨3748930502341453825071643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19994296012487753733715429 3748930502341453825071643)
      ·
        refine ⟨5623395753512180737607465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3748930502341453825071643 5623395753512180737607465)
        ·
          refine ⟨4217546815134135553205599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5623395753512180737607465 4217546815134135553205599)
          ·
            refine ⟨6326320222701203329808399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4217546815134135553205599 6326320222701203329808399)
            ·
              refine ⟨9489480334051804994712599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6326320222701203329808399 9489480334051804994712599)
              ·
                refine ⟨14234220501077707492068899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9489480334051804994712599 14234220501077707492068899)
                ·
                  refine ⟨21351330751616561238103349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14234220501077707492068899 21351330751616561238103349)
                  ·
                    refine ⟨2001687257964052616072189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21351330751616561238103349 2001687257964052616072189)
                    ·
                      refine ⟨750632721736519731027071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2001687257964052616072189 750632721736519731027071)
                      ·
                        rfl

theorem cell23_1461852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1461852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461852 prefixEnd_1461852 := by exact prefixLift 1461852
  have htrace : WordTrace (prefixWord ++ tailWord_1461852) baseStart_1461852 baseEnd_1461852 := by
    simpa [prefixWord, tailWord_1461852, baseEnd_1461852] using wordTrace_append hprefix tailTrace_1461852
  have hstable : (prefixWord ++ tailWord_1461852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461852).length < 2 ^ (prefixWord ++ tailWord_1461852).sum := by decide
  have hdescent : baseEnd_1461852 < baseStart_1461852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461853 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_1461853 : Nat := 118140960795 + 1461853 * 2 ^ 59
def prefixEnd_1461853 : Nat := 4983230072969 + 3 ^ 40 * 1461853 * 2
def baseEnd_1461853 : Nat := 750633235217174227114567

theorem tailTrace_1461853 : CollatzResearch.WordTrace tailWord_1461853 prefixEnd_1461853 750633235217174227114567 := by
  unfold tailWord_1461853
  simp only [CollatzResearch.WordTrace]
  refine ⟨53318159172963720460694213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35545439448642480307129475 53318159172963720460694213)
  ·
    refine ⟨9997154844930697586380165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53318159172963720460694213 9997154844930697586380165)
    ·
      refine ⟨1874466533424505797446281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9997154844930697586380165 1874466533424505797446281)
      ·
        refine ⟨1405849900068379348084711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1874466533424505797446281 1405849900068379348084711)
        ·
          refine ⟨2108774850102569022127067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405849900068379348084711 2108774850102569022127067)
          ·
            refine ⟨3163162275153853533190601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108774850102569022127067 3163162275153853533190601)
            ·
              refine ⟨2372371706365390149892951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3163162275153853533190601 2372371706365390149892951)
              ·
                refine ⟨3558557559548085224839427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2372371706365390149892951 3558557559548085224839427)
                ·
                  refine ⟨5337836339322127837259141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3558557559548085224839427 5337836339322127837259141)
                  ·
                    refine ⟨1000844313622898969486089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5337836339322127837259141 1000844313622898969486089)
                    ·
                      refine ⟨750633235217174227114567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000844313622898969486089 750633235217174227114567)
                      ·
                        rfl

theorem cell23_1461853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_1461853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461853 prefixEnd_1461853 := by exact prefixLift 1461853
  have htrace : WordTrace (prefixWord ++ tailWord_1461853) baseStart_1461853 baseEnd_1461853 := by
    simpa [prefixWord, tailWord_1461853, baseEnd_1461853] using wordTrace_append hprefix tailTrace_1461853
  have hstable : (prefixWord ++ tailWord_1461853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461853).length < 2 ^ (prefixWord ++ tailWord_1461853).sum := by decide
  have hdescent : baseEnd_1461853 < baseStart_1461853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461872 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 2, 5]
def baseStart_1461872 : Nat := 118140960795 + 1461872 * 2 ^ 59
def prefixEnd_1461872 : Nat := 4983230072969 + 3 ^ 40 * 1461872 * 2
def baseEnd_1461872 : Nat := 250214330449869884258993

theorem tailTrace_1461872 : CollatzResearch.WordTrace tailWord_1461872 prefixEnd_1461872 250214330449869884258993 := by
  unfold tailWord_1461872
  simp only [CollatzResearch.WordTrace]
  refine ⟨26659426079947443352817935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35545901439929924470423913 26659426079947443352817935)
  ·
    refine ⟨39989139119921165029226903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26659426079947443352817935 39989139119921165029226903)
    ·
      refine ⟨59983708679881747543840355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39989139119921165029226903 59983708679881747543840355)
      ·
        refine ⟨89975563019822621315760533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59983708679881747543840355 89975563019822621315760533)
        ·
          refine ⟨4217604516554185374176275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89975563019822621315760533 4217604516554185374176275)
          ·
            refine ⟨6326406774831278061264413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4217604516554185374176275 6326406774831278061264413)
            ·
              refine ⟨2372402540561729272974155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6326406774831278061264413 2372402540561729272974155)
              ·
                refine ⟨3558603810842593909461233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2372402540561729272974155 3558603810842593909461233)
                ·
                  refine ⟨2668952858131945432095925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3558603810842593909461233 2668952858131945432095925)
                  ·
                    refine ⟨250214330449869884258993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2668952858131945432095925 250214330449869884258993)
                    ·
                      rfl

theorem cell23_1461872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 2, 5].length) (baseStart_1461872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461872 prefixEnd_1461872 := by exact prefixLift 1461872
  have htrace : WordTrace (prefixWord ++ tailWord_1461872) baseStart_1461872 baseEnd_1461872 := by
    simpa [prefixWord, tailWord_1461872, baseEnd_1461872] using wordTrace_append hprefix tailTrace_1461872
  have hstable : (prefixWord ++ tailWord_1461872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461872).length < 2 ^ (prefixWord ++ tailWord_1461872).sum := by decide
  have hdescent : baseEnd_1461872 < baseStart_1461872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461912 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 1, 4, 3]
def baseStart_1461912 : Nat := 118140960795 + 1461912 * 2 ^ 59
def prefixEnd_1461912 : Nat := 4983230072969 + 3 ^ 40 * 1461912 * 2
def baseEnd_1461912 : Nat := 750663530575789496276795

theorem tailTrace_1461912 : CollatzResearch.WordTrace tailWord_1461912 prefixEnd_1461912 750663530575789496276795 := by
  unfold tailWord_1461912
  simp only [CollatzResearch.WordTrace]
  refine ⟨26660155539874986768545995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35546874053166649024727993 26660155539874986768545995)
  ·
    refine ⟨39990233309812480152818993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26660155539874986768545995 39990233309812480152818993)
    ·
      refine ⟨29992674982359360114614245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39990233309812480152818993 29992674982359360114614245)
      ·
        refine ⟨5623626559192380021490171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29992674982359360114614245 5623626559192380021490171)
        ·
          refine ⟨8435439838788570032235257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5623626559192380021490171 8435439838788570032235257)
          ·
            refine ⟨6326579879091427524176443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8435439838788570032235257 6326579879091427524176443)
            ·
              refine ⟨9489869818637141286264665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6326579879091427524176443 9489869818637141286264665)
              ·
                refine ⟨7117402363977855964698499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9489869818637141286264665 7117402363977855964698499)
                ·
                  refine ⟨10676103545966783947047749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7117402363977855964698499 10676103545966783947047749)
                  ·
                    refine ⟨2001769414868771990071453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10676103545966783947047749 2001769414868771990071453)
                    ·
                      refine ⟨750663530575789496276795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2001769414868771990071453 750663530575789496276795)
                      ·
                        rfl

theorem cell23_1461912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_1461912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461912 prefixEnd_1461912 := by exact prefixLift 1461912
  have htrace : WordTrace (prefixWord ++ tailWord_1461912) baseStart_1461912 baseEnd_1461912 := by
    simpa [prefixWord, tailWord_1461912, baseEnd_1461912] using wordTrace_append hprefix tailTrace_1461912
  have hstable : (prefixWord ++ tailWord_1461912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461912).length < 2 ^ (prefixWord ++ tailWord_1461912).sum := by decide
  have hdescent : baseEnd_1461912 < baseStart_1461912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461992 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 3, 6]
def baseStart_1461992 : Nat := 118140960795 + 1461992 * 2 ^ 59
def prefixEnd_1461992 : Nat := 4983230072969 + 3 ^ 40 * 1461992 * 2
def baseEnd_1461992 : Nat := 250234869676049727758809

theorem tailTrace_1461992 : CollatzResearch.WordTrace tailWord_1461992 prefixEnd_1461992 250234869676049727758809 := by
  unfold tailWord_1461992
  simp only [CollatzResearch.WordTrace]
  refine ⟨26661614459730073600002115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35548819279640098133336153 26661614459730073600002115)
  ·
    refine ⟨39992421689595110400003173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26661614459730073600002115 39992421689595110400003173)
    ·
      refine ⟨7498579066799083200000595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39992421689595110400003173 7498579066799083200000595)
      ·
        refine ⟨11247868600198624800000893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7498579066799083200000595 11247868600198624800000893)
        ·
          refine ⟨4217950725074484300000335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11247868600198624800000893 4217950725074484300000335)
          ·
            refine ⟨6326926087611726450000503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4217950725074484300000335 6326926087611726450000503)
            ·
              refine ⟨9490389131417589675000755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6326926087611726450000503 9490389131417589675000755)
              ·
                refine ⟨14235583697126384512501133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9490389131417589675000755 14235583697126384512501133)
                ·
                  refine ⟨5338343886422394192187925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14235583697126384512501133 5338343886422394192187925)
                  ·
                    refine ⟨250234869676049727758809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5338343886422394192187925 250234869676049727758809)
                    ·
                      rfl

theorem cell23_1461992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_1461992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461992 prefixEnd_1461992 := by exact prefixLift 1461992
  have htrace : WordTrace (prefixWord ++ tailWord_1461992) baseStart_1461992 baseEnd_1461992 := by
    simpa [prefixWord, tailWord_1461992, baseEnd_1461992] using wordTrace_append hprefix tailTrace_1461992
  have hstable : (prefixWord ++ tailWord_1461992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461992).length < 2 ^ (prefixWord ++ tailWord_1461992).sum := by decide
  have hdescent : baseEnd_1461992 < baseStart_1461992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462012 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_1462012 : Nat := 118140960795 + 1462012 * 2 ^ 59
def prefixEnd_1462012 : Nat := 4983230072969 + 3 ^ 40 * 1462012 * 2
def baseEnd_1462012 : Nat := 750714878641239105026335

theorem tailTrace_1462012 : CollatzResearch.WordTrace tailWord_1462012 prefixEnd_1462012 750714878641239105026335 := by
  unfold tailWord_1462012
  simp only [CollatzResearch.WordTrace]
  refine ⟨26661979189693845307866145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35549305586258460410488193 26661979189693845307866145)
  ·
    refine ⟨19996484392270383980899609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26661979189693845307866145 19996484392270383980899609)
    ·
      refine ⟨14997363294202787985674707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19996484392270383980899609 14997363294202787985674707)
      ·
        refine ⟨22496044941304181978512061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14997363294202787985674707 22496044941304181978512061)
        ·
          refine ⟨8436016852989068241942023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22496044941304181978512061 8436016852989068241942023)
          ·
            refine ⟨12654025279483602362913035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8436016852989068241942023 12654025279483602362913035)
            ·
              refine ⟨18981037919225403544369553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12654025279483602362913035 18981037919225403544369553)
              ·
                refine ⟨14235778439419052658277165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18981037919225403544369553 14235778439419052658277165)
                ·
                  refine ⟨5338416914782144746853937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14235778439419052658277165 5338416914782144746853937)
                  ·
                    refine ⟨4003812686086608560140453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5338416914782144746853937 4003812686086608560140453)
                    ·
                      refine ⟨750714878641239105026335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4003812686086608560140453 750714878641239105026335)
                      ·
                        rfl

theorem cell23_1462012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_1462012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462012 prefixEnd_1462012 := by exact prefixLift 1462012
  have htrace : WordTrace (prefixWord ++ tailWord_1462012) baseStart_1462012 baseEnd_1462012 := by
    simpa [prefixWord, tailWord_1462012, baseEnd_1462012] using wordTrace_append hprefix tailTrace_1462012
  have hstable : (prefixWord ++ tailWord_1462012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462012).length < 2 ^ (prefixWord ++ tailWord_1462012).sum := by decide
  have hdescent : baseEnd_1462012 < baseStart_1462012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462039 : List Nat := [1, 1, 3, 4, 2, 2, 3, 7]
def baseStart_1462039 : Nat := 118140960795 + 1462039 * 2 ^ 59
def prefixEnd_1462039 : Nat := 4983230072969 + 3 ^ 40 * 1462039 * 2
def baseEnd_1462039 : Nat := 27804768245144833310693

theorem tailTrace_1462039 : CollatzResearch.WordTrace tailWord_1462039 prefixEnd_1462039 27804768245144833310693 := by
  unfold tailWord_1462039
  simp only [CollatzResearch.WordTrace]
  refine ⟨53324943150289874226965171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35549962100193249484643447 53324943150289874226965171)
  ·
    refine ⟨79987414725434811340447757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53324943150289874226965171 79987414725434811340447757)
    ·
      refine ⟨29995280522038054252667909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79987414725434811340447757 29995280522038054252667909)
      ·
        refine ⟨5624115097882135172375233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29995280522038054252667909 5624115097882135172375233)
        ·
          refine ⟨4218086323411601379281425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5624115097882135172375233 4218086323411601379281425)
          ·
            refine ⟨3163564742558701034461069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4218086323411601379281425 3163564742558701034461069)
            ·
              refine ⟨1186336778459512887922901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3163564742558701034461069 1186336778459512887922901)
              ·
                refine ⟨27804768245144833310693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1186336778459512887922901 27804768245144833310693)
                ·
                  rfl

theorem cell23_1462039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 7].length) (baseStart_1462039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462039 prefixEnd_1462039 := by exact prefixLift 1462039
  have htrace : WordTrace (prefixWord ++ tailWord_1462039) baseStart_1462039 baseEnd_1462039 := by
    simpa [prefixWord, tailWord_1462039, baseEnd_1462039] using wordTrace_append hprefix tailTrace_1462039
  have hstable : (prefixWord ++ tailWord_1462039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462039).length < 2 ^ (prefixWord ++ tailWord_1462039).sum := by decide
  have hdescent : baseEnd_1462039 < baseStart_1462039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462049 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 1, 3, 3]
def baseStart_1462049 : Nat := 118140960795 + 1462049 * 2 ^ 59
def prefixEnd_1462049 : Nat := 4983230072969 + 3 ^ 40 * 1462049 * 2
def baseEnd_1462049 : Nat := 750733877425455460263665

theorem tailTrace_1462049 : CollatzResearch.WordTrace tailWord_1462049 prefixEnd_1462049 750733877425455460263665 := by
  unfold tailWord_1462049
  simp only [CollatzResearch.WordTrace]
  refine ⟨53325307880253645934829201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35550205253502430623219467 53325307880253645934829201)
  ·
    refine ⟨39993980910190234451121901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53325307880253645934829201 39993980910190234451121901)
    ·
      refine ⟨14997742841321337919170713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39993980910190234451121901 14997742841321337919170713)
      ·
        refine ⟨11248307130991003439378035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14997742841321337919170713 11248307130991003439378035)
        ·
          refine ⟨16872460696486505159067053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11248307130991003439378035 16872460696486505159067053)
          ·
            refine ⟨6327172761182439434650145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16872460696486505159067053 6327172761182439434650145)
            ·
              refine ⟨4745379570886829575987609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6327172761182439434650145 4745379570886829575987609)
              ·
                refine ⟨3559034678165122181990707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4745379570886829575987609 3559034678165122181990707)
                ·
                  refine ⟨5338552017247683272986061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3559034678165122181990707 5338552017247683272986061)
                  ·
                    refine ⟨2001957006467881227369773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5338552017247683272986061 2001957006467881227369773)
                    ·
                      refine ⟨750733877425455460263665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2001957006467881227369773 750733877425455460263665)
                      ·
                        rfl

theorem cell23_1462049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_1462049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462049 prefixEnd_1462049 := by exact prefixLift 1462049
  have htrace : WordTrace (prefixWord ++ tailWord_1462049) baseStart_1462049 baseEnd_1462049 := by
    simpa [prefixWord, tailWord_1462049, baseEnd_1462049] using wordTrace_append hprefix tailTrace_1462049
  have hstable : (prefixWord ++ tailWord_1462049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462049).length < 2 ^ (prefixWord ++ tailWord_1462049).sum := by decide
  have hdescent : baseEnd_1462049 < baseStart_1462049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462050 : List Nat := [3, 3, 1, 1, 2, 1, 4, 3, 1, 2, 2]
def baseStart_1462050 : Nat := 118140960795 + 1462050 * 2 ^ 59
def prefixEnd_1462050 : Nat := 4983230072969 + 3 ^ 40 * 1462050 * 2
def baseEnd_1462050 : Nat := 750734390906109956351161

theorem tailTrace_1462050 : CollatzResearch.WordTrace tailWord_1462050 prefixEnd_1462050 750734390906109956351161 := by
  unfold tailWord_1462050
  simp only [CollatzResearch.WordTrace]
  refine ⟨13331336088312505776403901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35550229568833348737077069 13331336088312505776403901)
  ·
    refine ⟨4999251033117189666151463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13331336088312505776403901 4999251033117189666151463)
    ·
      refine ⟨7498876549675784499227195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4999251033117189666151463 7498876549675784499227195)
      ·
        refine ⟨11248314824513676748840793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7498876549675784499227195 11248314824513676748840793)
        ·
          refine ⟨8436236118385257561630595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11248314824513676748840793 8436236118385257561630595)
          ·
            refine ⟨12654354177577886342445893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8436236118385257561630595 12654354177577886342445893)
            ·
              refine ⟨2372691408295853689208605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12654354177577886342445893 2372691408295853689208605)
              ·
                refine ⟨889759278110945133453227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2372691408295853689208605 889759278110945133453227)
                ·
                  refine ⟨1334638917166417700179841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889759278110945133453227 1334638917166417700179841)
                  ·
                    refine ⟨1000979187874813275134881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1334638917166417700179841 1000979187874813275134881)
                    ·
                      refine ⟨750734390906109956351161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000979187874813275134881 750734390906109956351161)
                      ·
                        rfl

theorem cell23_1462050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_1462050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462050 prefixEnd_1462050 := by exact prefixLift 1462050
  have htrace : WordTrace (prefixWord ++ tailWord_1462050) baseStart_1462050 baseEnd_1462050 := by
    simpa [prefixWord, tailWord_1462050, baseEnd_1462050] using wordTrace_append hprefix tailTrace_1462050
  have hstable : (prefixWord ++ tailWord_1462050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462050).length < 2 ^ (prefixWord ++ tailWord_1462050).sum := by decide
  have hdescent : baseEnd_1462050 < baseStart_1462050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462053 : List Nat := [1, 3, 1, 2, 3, 4, 2, 1, 1, 2, 3]
def baseStart_1462053 : Nat := 118140960795 + 1462053 * 2 ^ 59
def prefixEnd_1462053 : Nat := 4983230072969 + 3 ^ 40 * 1462053 * 2
def baseEnd_1462053 : Nat := 750735931348073444613647

theorem tailTrace_1462053 : CollatzResearch.WordTrace tailWord_1462053 prefixEnd_1462053 750735931348073444613647 := by
  unfold tailWord_1462053
  simp only [CollatzResearch.WordTrace]
  refine ⟨53325453772239154617974813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35550302514826103078649875 53325453772239154617974813)
  ·
    refine ⟨19997045164589682981740555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53325453772239154617974813 19997045164589682981740555)
    ·
      refine ⟨29995567746884524472610833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19997045164589682981740555 29995567746884524472610833)
      ·
        refine ⟨22496675810163393354458125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29995567746884524472610833 22496675810163393354458125)
        ·
          refine ⟨8436253428811272507921797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22496675810163393354458125 8436253428811272507921797)
          ·
            refine ⟨1581797517902113595235337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8436253428811272507921797 1581797517902113595235337)
            ·
              refine ⟨1186348138426585196426503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1581797517902113595235337 1186348138426585196426503)
              ·
                refine ⟨1779522207639877794639755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186348138426585196426503 1779522207639877794639755)
                ·
                  refine ⟨2669283311459816691959633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1779522207639877794639755 2669283311459816691959633)
                  ·
                    refine ⟨2001962483594862518969725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2669283311459816691959633 2001962483594862518969725)
                    ·
                      refine ⟨750735931348073444613647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2001962483594862518969725 750735931348073444613647)
                      ·
                        rfl

theorem cell23_1462053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_1462053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462053 prefixEnd_1462053 := by exact prefixLift 1462053
  have htrace : WordTrace (prefixWord ++ tailWord_1462053) baseStart_1462053 baseEnd_1462053 := by
    simpa [prefixWord, tailWord_1462053, baseEnd_1462053] using wordTrace_append hprefix tailTrace_1462053
  have hstable : (prefixWord ++ tailWord_1462053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462053).length < 2 ^ (prefixWord ++ tailWord_1462053).sum := by decide
  have hdescent : baseEnd_1462053 < baseStart_1462053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462066 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3]
def baseStart_1462066 : Nat := 118140960795 + 1462066 * 2 ^ 59
def prefixEnd_1462066 : Nat := 4983230072969 + 3 ^ 40 * 1462066 * 2
def baseEnd_1462066 : Nat := 750742606596581893751087

theorem tailTrace_1462066 : CollatzResearch.WordTrace tailWord_1462066 prefixEnd_1462066 750742606596581893751087 := by
  unfold tailWord_1462066
  simp only [CollatzResearch.WordTrace]
  refine ⟨13331481980298014459549513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35550618614128038558798701 13331481980298014459549513)
  ·
    refine ⟨9998611485223510844662135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13331481980298014459549513 9998611485223510844662135)
    ·
      refine ⟨14997917227835266266993203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9998611485223510844662135 14997917227835266266993203)
      ·
        refine ⟨22496875841752899400489805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14997917227835266266993203 22496875841752899400489805)
        ·
          refine ⟨8436328440657337275183677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22496875841752899400489805 8436328440657337275183677)
          ·
            refine ⟨3163623165246501478193879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8436328440657337275183677 3163623165246501478193879)
            ·
              refine ⟨4745434747869752217290819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3163623165246501478193879 4745434747869752217290819)
              ·
                refine ⟨7118152121804628325936229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4745434747869752217290819 7118152121804628325936229)
                ·
                  refine ⟨1334653522838367811113043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7118152121804628325936229 1334653522838367811113043)
                  ·
                    refine ⟨2001980284257551716669565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1334653522838367811113043 2001980284257551716669565)
                    ·
                      refine ⟨750742606596581893751087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2001980284257551716669565 750742606596581893751087)
                      ·
                        rfl

theorem cell23_1462066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_1462066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462066 prefixEnd_1462066 := by exact prefixLift 1462066
  have htrace : WordTrace (prefixWord ++ tailWord_1462066) baseStart_1462066 baseEnd_1462066 := by
    simpa [prefixWord, tailWord_1462066, baseEnd_1462066] using wordTrace_append hprefix tailTrace_1462066
  have hstable : (prefixWord ++ tailWord_1462066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462066).length < 2 ^ (prefixWord ++ tailWord_1462066).sum := by decide
  have hdescent : baseEnd_1462066 < baseStart_1462066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462083 : List Nat := [1, 1, 1, 3, 1, 6, 3, 1, 2, 1, 3]
def baseStart_1462083 : Nat := 118140960795 + 1462083 * 2 ^ 59
def prefixEnd_1462083 : Nat := 4983230072969 + 3 ^ 40 * 1462083 * 2
def baseEnd_1462083 : Nat := 750751335767708327238509

theorem tailTrace_1462083 : CollatzResearch.WordTrace tailWord_1462083 prefixEnd_1462083 750751335767708327238509 := by
  unfold tailWord_1462083
  simp only [CollatzResearch.WordTrace]
  refine ⟨53326547962130469741566903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35551031974753646494377935 53326547962130469741566903)
  ·
    refine ⟨79989821943195704612350355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53326547962130469741566903 79989821943195704612350355)
    ·
      refine ⟨119984732914793556918525533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79989821943195704612350355 119984732914793556918525533)
      ·
        refine ⟨44994274843047583844447075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119984732914793556918525533 44994274843047583844447075)
        ·
          refine ⟨67491412264571375766670613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44994274843047583844447075 67491412264571375766670613)
          ·
            refine ⟨3163659949901783239062685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67491412264571375766670613 3163659949901783239062685)
            ·
              refine ⟨1186372481213168714648507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3163659949901783239062685 1186372481213168714648507)
              ·
                refine ⟨1779558721819753071972761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186372481213168714648507 1779558721819753071972761)
                ·
                  refine ⟨1334669041364814803979571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1779558721819753071972761 1334669041364814803979571)
                  ·
                    refine ⟨2002003562047222205969357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1334669041364814803979571 2002003562047222205969357)
                    ·
                      refine ⟨750751335767708327238509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2002003562047222205969357 750751335767708327238509)
                      ·
                        rfl

theorem cell23_1462083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 2, 1, 3].length) (baseStart_1462083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462083 prefixEnd_1462083 := by exact prefixLift 1462083
  have htrace : WordTrace (prefixWord ++ tailWord_1462083) baseStart_1462083 baseEnd_1462083 := by
    simpa [prefixWord, tailWord_1462083, baseEnd_1462083] using wordTrace_append hprefix tailTrace_1462083
  have hstable : (prefixWord ++ tailWord_1462083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462083).length < 2 ^ (prefixWord ++ tailWord_1462083).sum := by decide
  have hdescent : baseEnd_1462083 < baseStart_1462083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462106 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2]
def baseStart_1462106 : Nat := 118140960795 + 1462106 * 2 ^ 59
def prefixEnd_1462106 : Nat := 4983230072969 + 3 ^ 40 * 1462106 * 2
def baseEnd_1462106 : Nat := 750763145822761737250903

theorem tailTrace_1462106 : CollatzResearch.WordTrace tailWord_1462106 prefixEnd_1462106 750763145822761737250903 := by
  unfold tailWord_1462106
  simp only [CollatzResearch.WordTrace]
  refine ⟨13331846710261786167413543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35551591227364763113102781 13331846710261786167413543)
  ·
    refine ⟨19997770065392679251120315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13331846710261786167413543 19997770065392679251120315)
    ·
      refine ⟨29996655098089018876680473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19997770065392679251120315 29996655098089018876680473)
      ·
        refine ⟨22497491323566764157510355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29996655098089018876680473 22497491323566764157510355)
        ·
          refine ⟨33746236985350146236265533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22497491323566764157510355 33746236985350146236265533)
          ·
            refine ⟨12654838869506304838599575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33746236985350146236265533 12654838869506304838599575)
            ·
              refine ⟨18982258304259457257899363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12654838869506304838599575 18982258304259457257899363)
              ·
                refine ⟨28473387456389185886849045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18982258304259457257899363 28473387456389185886849045)
                ·
                  refine ⟨1334690037018243088446049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28473387456389185886849045 1334690037018243088446049)
                  ·
                    refine ⟨1001017527763682316334537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1334690037018243088446049 1001017527763682316334537)
                    ·
                      refine ⟨750763145822761737250903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1001017527763682316334537 750763145822761737250903)
                      ·
                        rfl

theorem cell23_1462106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_1462106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462106 prefixEnd_1462106 := by exact prefixLift 1462106
  have htrace : WordTrace (prefixWord ++ tailWord_1462106) baseStart_1462106 baseEnd_1462106 := by
    simpa [prefixWord, tailWord_1462106, baseEnd_1462106] using wordTrace_append hprefix tailTrace_1462106
  have hstable : (prefixWord ++ tailWord_1462106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462106).length < 2 ^ (prefixWord ++ tailWord_1462106).sum := by decide
  have hdescent : baseEnd_1462106 < baseStart_1462106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462134 : List Nat := [5, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3]
def baseStart_1462134 : Nat := 118140960795 + 1462134 * 2 ^ 59
def prefixEnd_1462134 : Nat := 4983230072969 + 3 ^ 40 * 1462134 * 2
def baseEnd_1462134 : Nat := 750777523281087627700775

theorem tailTrace_1462134 : CollatzResearch.WordTrace tailWord_1462134 prefixEnd_1462134 750777523281087627700775 := by
  unfold tailWord_1462134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3333025505309106590729591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35552272056630470301115637 3333025505309106590729591)
  ·
    refine ⟨4999538257963659886094387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3333025505309106590729591 4999538257963659886094387)
    ·
      refine ⟨7499307386945489829141581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4999538257963659886094387 7499307386945489829141581)
      ·
        refine ⟨2812240270104558685928093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7499307386945489829141581 2812240270104558685928093)
        ·
          refine ⟨1054590101289209507223035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2812240270104558685928093 1054590101289209507223035)
          ·
            refine ⟨1581885151933814260834553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054590101289209507223035 1581885151933814260834553)
            ·
              refine ⟨1186413863950360695625915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1581885151933814260834553 1186413863950360695625915)
              ·
                refine ⟨1779620795925541043438873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186413863950360695625915 1779620795925541043438873)
                ·
                  refine ⟨1334715596944155782579155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1779620795925541043438873 1334715596944155782579155)
                  ·
                    refine ⟨2002073395416233673868733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1334715596944155782579155 2002073395416233673868733)
                    ·
                      refine ⟨750777523281087627700775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2002073395416233673868733 750777523281087627700775)
                      ·
                        rfl

theorem cell23_1462134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_1462134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462134 prefixEnd_1462134 := by exact prefixLift 1462134
  have htrace : WordTrace (prefixWord ++ tailWord_1462134) baseStart_1462134 baseEnd_1462134 := by
    simpa [prefixWord, tailWord_1462134, baseEnd_1462134] using wordTrace_append hprefix tailTrace_1462134
  have hstable : (prefixWord ++ tailWord_1462134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462134).length < 2 ^ (prefixWord ++ tailWord_1462134).sum := by decide
  have hdescent : baseEnd_1462134 < baseStart_1462134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462174 : List Nat := [4, 3, 1, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_1462174 : Nat := 118140960795 + 1462174 * 2 ^ 59
def prefixEnd_1462174 : Nat := 4983230072969 + 3 ^ 40 * 1462174 * 2
def baseEnd_1462174 : Nat := 750798062507267471200591

theorem tailTrace_1462174 : CollatzResearch.WordTrace tailWord_1462174 prefixEnd_1462174 750798062507267471200591 := by
  unfold tailWord_1462174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6666233375600099035391197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35553244669867194855419717 6666233375600099035391197)
  ·
    refine ⟨2499837515850037138271699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6666233375600099035391197 2499837515850037138271699)
    ·
      refine ⟨3749756273775055707407549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2499837515850037138271699 3749756273775055707407549)
      ·
        refine ⟨1406158602665645890277831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3749756273775055707407549 1406158602665645890277831)
        ·
          refine ⟨2109237903998468835416747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406158602665645890277831 2109237903998468835416747)
          ·
            refine ⟨3163856855997703253125121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109237903998468835416747 3163856855997703253125121)
            ·
              refine ⟨2372892641998277439843841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3163856855997703253125121 2372892641998277439843841)
              ·
                refine ⟨1779669481498708079882881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2372892641998277439843841 1779669481498708079882881)
                ·
                  refine ⟨1334752111124031059912161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1779669481498708079882881 1334752111124031059912161)
                  ·
                    refine ⟨1001064083343023294934121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1334752111124031059912161 1001064083343023294934121)
                    ·
                      refine ⟨750798062507267471200591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1001064083343023294934121 750798062507267471200591)
                      ·
                        rfl

theorem cell23_1462174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_1462174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462174 prefixEnd_1462174 := by exact prefixLift 1462174
  have htrace : WordTrace (prefixWord ++ tailWord_1462174) baseStart_1462174 baseEnd_1462174 := by
    simpa [prefixWord, tailWord_1462174, baseEnd_1462174] using wordTrace_append hprefix tailTrace_1462174
  have hstable : (prefixWord ++ tailWord_1462174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462174).length < 2 ^ (prefixWord ++ tailWord_1462174).sum := by decide
  have hdescent : baseEnd_1462174 < baseStart_1462174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462199 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 3]
def baseStart_1462199 : Nat := 118140960795 + 1462199 * 2 ^ 59
def prefixEnd_1462199 : Nat := 4983230072969 + 3 ^ 40 * 1462199 * 2
def baseEnd_1462199 : Nat := 750810899523629873387975

theorem tailTrace_1462199 : CollatzResearch.WordTrace tailWord_1462199 prefixEnd_1462199 750810899523629873387975 := by
  unfold tailWord_1462199
  simp only [CollatzResearch.WordTrace]
  refine ⟨53330778829710221552789651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35553852553140147701859767 53330778829710221552789651)
  ·
    refine ⟨79996168244565332329184477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53330778829710221552789651 79996168244565332329184477)
    ·
      refine ⟨29998563091711999623444179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79996168244565332329184477 29998563091711999623444179)
      ·
        refine ⟨44997844637567999435166269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29998563091711999623444179 44997844637567999435166269)
        ·
          refine ⟨16874191739087999788187351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44997844637567999435166269 16874191739087999788187351)
          ·
            refine ⟨25311287608631999682281027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16874191739087999788187351 25311287608631999682281027)
            ·
              refine ⟨37966931412947999523421541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25311287608631999682281027 37966931412947999523421541)
              ·
                refine ⟨7118799639927749910641539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37966931412947999523421541 7118799639927749910641539)
                ·
                  refine ⟨10678199459891624865962309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7118799639927749910641539 10678199459891624865962309)
                  ·
                    refine ⟨2002162398729679662367933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10678199459891624865962309 2002162398729679662367933)
                    ·
                      refine ⟨750810899523629873387975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2002162398729679662367933 750810899523629873387975)
                      ·
                        rfl

theorem cell23_1462199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_1462199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462199 prefixEnd_1462199 := by exact prefixLift 1462199
  have htrace : WordTrace (prefixWord ++ tailWord_1462199) baseStart_1462199 baseEnd_1462199 := by
    simpa [prefixWord, tailWord_1462199, baseEnd_1462199] using wordTrace_append hprefix tailTrace_1462199
  have hstable : (prefixWord ++ tailWord_1462199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462199).length < 2 ^ (prefixWord ++ tailWord_1462199).sum := by decide
  have hdescent : baseEnd_1462199 < baseStart_1462199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462206 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_1462206 : Nat := 118140960795 + 1462206 * 2 ^ 59
def prefixEnd_1462206 : Nat := 4983230072969 + 3 ^ 40 * 1462206 * 2
def baseEnd_1462206 : Nat := 250271497962737115333481

theorem tailTrace_1462206 : CollatzResearch.WordTrace tailWord_1462206 prefixEnd_1462206 250271497962737115333481 := by
  unfold tailWord_1462206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6666379267585607718536809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35554022760456574498862981 6666379267585607718536809)
  ·
    refine ⟨4999784450689205788902607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6666379267585607718536809 4999784450689205788902607)
    ·
      refine ⟨7499676676033808683353911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4999784450689205788902607 7499676676033808683353911)
      ·
        refine ⟨11249515014050713025030867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7499676676033808683353911 11249515014050713025030867)
        ·
          refine ⟨16874272521076069537546301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11249515014050713025030867 16874272521076069537546301)
          ·
            refine ⟨6327852195403526076579863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16874272521076069537546301 6327852195403526076579863)
            ·
              refine ⟨9491778293105289114869795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6327852195403526076579863 9491778293105289114869795)
              ·
                refine ⟨14237667439657933672304693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9491778293105289114869795 14237667439657933672304693)
                ·
                  refine ⟨1334781322467931281778565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14237667439657933672304693 1334781322467931281778565)
                  ·
                    refine ⟨250271497962737115333481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1334781322467931281778565 250271497962737115333481)
                    ·
                      rfl

theorem cell23_1462206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_1462206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462206 prefixEnd_1462206 := by exact prefixLift 1462206
  have htrace : WordTrace (prefixWord ++ tailWord_1462206) baseStart_1462206 baseEnd_1462206 := by
    simpa [prefixWord, tailWord_1462206, baseEnd_1462206] using wordTrace_append hprefix tailTrace_1462206
  have hstable : (prefixWord ++ tailWord_1462206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462206).length < 2 ^ (prefixWord ++ tailWord_1462206).sum := by decide
  have hdescent : baseEnd_1462206 < baseStart_1462206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462216 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 1, 4, 3]
def baseStart_1462216 : Nat := 118140960795 + 1462216 * 2 ^ 59
def prefixEnd_1462216 : Nat := 4983230072969 + 3 ^ 40 * 1462216 * 2
def baseEnd_1462216 : Nat := 750819628694756306875397

theorem tailTrace_1462216 : CollatzResearch.WordTrace tailWord_1462216 prefixEnd_1462216 750819628694756306875397 := by
  unfold tailWord_1462216
  simp only [CollatzResearch.WordTrace]
  refine ⟨26665699435324316728079251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35554265913765755637439001 26665699435324316728079251)
  ·
    refine ⟨39998549152986475092118877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26665699435324316728079251 39998549152986475092118877)
    ·
      refine ⟨14999455932369928159544579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39998549152986475092118877 14999455932369928159544579)
      ·
        refine ⟨22499183898554892239316869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14999455932369928159544579 22499183898554892239316869)
        ·
          refine ⟨4218596980979042294871913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22499183898554892239316869 4218596980979042294871913)
          ·
            refine ⟨3163947735734281721153935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4218596980979042294871913 3163947735734281721153935)
            ·
              refine ⟨4745921603601422581730903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3163947735734281721153935 4745921603601422581730903)
              ·
                refine ⟨7118882405402133872596355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4745921603601422581730903 7118882405402133872596355)
                ·
                  refine ⟨10678323608103200808894533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7118882405402133872596355 10678323608103200808894533)
                  ·
                    refine ⟨2002185676519350151667725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10678323608103200808894533 2002185676519350151667725)
                    ·
                      refine ⟨750819628694756306875397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2002185676519350151667725 750819628694756306875397)
                      ·
                        rfl

theorem cell23_1462216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_1462216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462216 prefixEnd_1462216 := by exact prefixLift 1462216
  have htrace : WordTrace (prefixWord ++ tailWord_1462216) baseStart_1462216 baseEnd_1462216 := by
    simpa [prefixWord, tailWord_1462216, baseEnd_1462216] using wordTrace_append hprefix tailTrace_1462216
  have hstable : (prefixWord ++ tailWord_1462216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462216).length < 2 ^ (prefixWord ++ tailWord_1462216).sum := by decide
  have hdescent : baseEnd_1462216 < baseStart_1462216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462223 : List Nat := [1, 1, 2, 1, 1, 5, 4, 3, 1, 4]
def baseStart_1462223 : Nat := 118140960795 + 1462223 * 2 ^ 59
def prefixEnd_1462223 : Nat := 4983230072969 + 3 ^ 40 * 1462223 * 2
def baseEnd_1462223 : Nat := 250274407686445926495955

theorem tailTrace_1462223 : CollatzResearch.WordTrace tailWord_1462223 prefixEnd_1462223 250274407686445926495955 := by
  unfold tailWord_1462223
  simp only [CollatzResearch.WordTrace]
  refine ⟨53331654181623273651663323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35554436121082182434442215 53331654181623273651663323)
  ·
    refine ⟨79997481272434910477494985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53331654181623273651663323 79997481272434910477494985)
    ·
      refine ⟨59998110954326182858121239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79997481272434910477494985 59998110954326182858121239)
      ·
        refine ⟨89997166431489274287181859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59998110954326182858121239 89997166431489274287181859)
        ·
          refine ⟨134995749647233911430772789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89997166431489274287181859 134995749647233911430772789)
          ·
            refine ⟨12655851529428179196634949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134995749647233911430772789 12655851529428179196634949)
            ·
              refine ⟨2372972161767783599369053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12655851529428179196634949 2372972161767783599369053)
              ·
                refine ⟨889864560662918849763395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2372972161767783599369053 889864560662918849763395)
                ·
                  refine ⟨1334796840994378274645093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889864560662918849763395 1334796840994378274645093)
                  ·
                    refine ⟨250274407686445926495955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1334796840994378274645093 250274407686445926495955)
                    ·
                      rfl

theorem cell23_1462223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 1, 4].length) (baseStart_1462223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462223 prefixEnd_1462223 := by exact prefixLift 1462223
  have htrace : WordTrace (prefixWord ++ tailWord_1462223) baseStart_1462223 baseEnd_1462223 := by
    simpa [prefixWord, tailWord_1462223, baseEnd_1462223] using wordTrace_append hprefix tailTrace_1462223
  have hstable : (prefixWord ++ tailWord_1462223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462223).length < 2 ^ (prefixWord ++ tailWord_1462223).sum := by decide
  have hdescent : baseEnd_1462223 < baseStart_1462223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462239 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 6]
def baseStart_1462239 : Nat := 118140960795 + 1462239 * 2 ^ 59
def prefixEnd_1462239 : Nat := 4983230072969 + 3 ^ 40 * 1462239 * 2
def baseEnd_1462239 : Nat := 750831438749809716887791

theorem tailTrace_1462239 : CollatzResearch.WordTrace tailWord_1462239 prefixEnd_1462239 750831438749809716887791 := by
  unfold tailWord_1462239
  simp only [CollatzResearch.WordTrace]
  refine ⟨53332237749565308384245771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35554825166376872256163847 53332237749565308384245771)
  ·
    refine ⟨79998356624347962576368657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53332237749565308384245771 79998356624347962576368657)
    ·
      refine ⟨59998767468260971932276493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79998356624347962576368657 59998767468260971932276493)
      ·
        refine ⟨22499537800597864474603685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59998767468260971932276493 22499537800597864474603685)
        ·
          refine ⟨4218663337612099588988191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22499537800597864474603685 4218663337612099588988191)
          ·
            refine ⟨6327995006418149383482287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4218663337612099588988191 6327995006418149383482287)
            ·
              refine ⟨9491992509627224075223431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6327995006418149383482287 9491992509627224075223431)
              ·
                refine ⟨14237988764440836112835147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9491992509627224075223431 14237988764440836112835147)
                ·
                  refine ⟨21356983146661254169252721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14237988764440836112835147 21356983146661254169252721)
                  ·
                    refine ⟨16017737359995940626939541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21356983146661254169252721 16017737359995940626939541)
                    ·
                      refine ⟨750831438749809716887791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16017737359995940626939541 750831438749809716887791)
                      ·
                        rfl

theorem cell23_1462239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_1462239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462239 prefixEnd_1462239 := by exact prefixLift 1462239
  have htrace : WordTrace (prefixWord ++ tailWord_1462239) baseStart_1462239 baseEnd_1462239 := by
    simpa [prefixWord, tailWord_1462239, baseEnd_1462239] using wordTrace_append hprefix tailTrace_1462239
  have hstable : (prefixWord ++ tailWord_1462239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462239).length < 2 ^ (prefixWord ++ tailWord_1462239).sum := by decide
  have hdescent : baseEnd_1462239 < baseStart_1462239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462256 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 1, 5, 2]
def baseStart_1462256 : Nat := 118140960795 + 1462256 * 2 ^ 59
def prefixEnd_1462256 : Nat := 4983230072969 + 3 ^ 40 * 1462256 * 2
def baseEnd_1462256 : Nat := 750840167920936150375213

theorem tailTrace_1462256 : CollatzResearch.WordTrace tailWord_1462256 prefixEnd_1462256 750840167920936150375213 := by
  unfold tailWord_1462256
  simp only [CollatzResearch.WordTrace]
  refine ⟨26666428895251860143807311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35555238527002480191743081 26666428895251860143807311)
  ·
    refine ⟨39999643342877790215710967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26666428895251860143807311 39999643342877790215710967)
    ·
      refine ⟨59999465014316685323566451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39999643342877790215710967 59999465014316685323566451)
      ·
        refine ⟨89999197521475027985349677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59999465014316685323566451 89999197521475027985349677)
        ·
          refine ⟨33749699070553135494506129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89999197521475027985349677 33749699070553135494506129)
          ·
            refine ⟨25312274302914851620879597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33749699070553135494506129 25312274302914851620879597)
            ·
              refine ⟨9492102863593069357829849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25312274302914851620879597 9492102863593069357829849)
              ·
                refine ⟨7119077147694802018372387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9492102863593069357829849 7119077147694802018372387)
                ·
                  refine ⟨10678615721542203027558581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7119077147694802018372387 10678615721542203027558581)
                  ·
                    refine ⟨1001120223894581533833617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10678615721542203027558581 1001120223894581533833617)
                    ·
                      refine ⟨750840167920936150375213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1001120223894581533833617 750840167920936150375213)
                      ·
                        rfl

theorem cell23_1462256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 1, 5, 2].length) (baseStart_1462256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462256 prefixEnd_1462256 := by exact prefixLift 1462256
  have htrace : WordTrace (prefixWord ++ tailWord_1462256) baseStart_1462256 baseEnd_1462256 := by
    simpa [prefixWord, tailWord_1462256, baseEnd_1462256] using wordTrace_append hprefix tailTrace_1462256
  have hstable : (prefixWord ++ tailWord_1462256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462256).length < 2 ^ (prefixWord ++ tailWord_1462256).sum := by decide
  have hdescent : baseEnd_1462256 < baseStart_1462256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462273 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 2, 3, 2]
def baseStart_1462273 : Nat := 118140960795 + 1462273 * 2 ^ 59
def prefixEnd_1462273 : Nat := 4983230072969 + 3 ^ 40 * 1462273 * 2
def baseEnd_1462273 : Nat := 750848897092062583862635

theorem tailTrace_1462273 : CollatzResearch.WordTrace tailWord_1462273 prefixEnd_1462273 750848897092062583862635 := by
  unfold tailWord_1462273
  simp only [CollatzResearch.WordTrace]
  refine ⟨53333477831442132190983473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35555651887628088127322315 53333477831442132190983473)
  ·
    refine ⟨40000108373581599143237605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53333477831442132190983473 40000108373581599143237605)
    ·
      refine ⟨7500020320046549839357051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40000108373581599143237605 7500020320046549839357051)
      ·
        refine ⟨11250030480069824759035577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7500020320046549839357051 11250030480069824759035577)
        ·
          refine ⟨8437522860052368569276683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11250030480069824759035577 8437522860052368569276683)
          ·
            refine ⟨12656284290078552853915025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8437522860052368569276683 12656284290078552853915025)
            ·
              refine ⟨9492213217558914640436269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12656284290078552853915025 9492213217558914640436269)
              ·
                refine ⟨3559579956584592990163601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9492213217558914640436269 3559579956584592990163601)
                ·
                  refine ⟨2669684967438444742622701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3559579956584592990163601 2669684967438444742622701)
                  ·
                    refine ⟨1001131862789416778483513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2669684967438444742622701 1001131862789416778483513)
                    ·
                      refine ⟨750848897092062583862635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1001131862789416778483513 750848897092062583862635)
                      ·
                        rfl

theorem cell23_1462273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_1462273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462273 prefixEnd_1462273 := by exact prefixLift 1462273
  have htrace : WordTrace (prefixWord ++ tailWord_1462273) baseStart_1462273 baseEnd_1462273 := by
    simpa [prefixWord, tailWord_1462273, baseEnd_1462273] using wordTrace_append hprefix tailTrace_1462273
  have hstable : (prefixWord ++ tailWord_1462273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462273).length < 2 ^ (prefixWord ++ tailWord_1462273).sum := by decide
  have hdescent : baseEnd_1462273 < baseStart_1462273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462296 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 4, 4]
def baseStart_1462296 : Nat := 118140960795 + 1462296 * 2 ^ 59
def prefixEnd_1462296 : Nat := 4983230072969 + 3 ^ 40 * 1462296 * 2
def baseEnd_1462296 : Nat := 250286902382371997958343

theorem tailTrace_1462296 : CollatzResearch.WordTrace tailWord_1462296 prefixEnd_1462296 250286902382371997958343 := by
  unfold tailWord_1462296
  simp only [CollatzResearch.WordTrace]
  refine ⟨26667158355179403559535371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35556211140239204746047161 26667158355179403559535371)
  ·
    refine ⟨40000737532769105339303057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26667158355179403559535371 40000737532769105339303057)
    ·
      refine ⟨30000553149576829004477293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40000737532769105339303057 30000553149576829004477293)
      ·
        refine ⟨11250207431091310876678985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30000553149576829004477293 11250207431091310876678985)
        ·
          refine ⟨8437655573318483157509239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11250207431091310876678985 8437655573318483157509239)
          ·
            refine ⟨12656483359977724736263859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8437655573318483157509239 12656483359977724736263859)
            ·
              refine ⟨18984725039966587104395789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12656483359977724736263859 18984725039966587104395789)
              ·
                refine ⟨7119271889987470164148421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18984725039966587104395789 7119271889987470164148421)
                ·
                  refine ⟨1334863479372650655777829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7119271889987470164148421 1334863479372650655777829)
                  ·
                    refine ⟨250286902382371997958343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1334863479372650655777829 250286902382371997958343)
                    ·
                      rfl

theorem cell23_1462296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_1462296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462296 prefixEnd_1462296 := by exact prefixLift 1462296
  have htrace : WordTrace (prefixWord ++ tailWord_1462296) baseStart_1462296 baseEnd_1462296 := by
    simpa [prefixWord, tailWord_1462296, baseEnd_1462296] using wordTrace_append hprefix tailTrace_1462296
  have hstable : (prefixWord ++ tailWord_1462296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462296).length < 2 ^ (prefixWord ++ tailWord_1462296).sum := by decide
  have hdescent : baseEnd_1462296 < baseStart_1462296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462299 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 4]
def baseStart_1462299 : Nat := 118140960795 + 1462299 * 2 ^ 59
def prefixEnd_1462299 : Nat := 4983230072969 + 3 ^ 40 * 1462299 * 2
def baseEnd_1462299 : Nat := 750862247589079482137515

theorem tailTrace_1462299 : CollatzResearch.WordTrace tailWord_1462299 prefixEnd_1462299 750862247589079482137515 := by
  unfold tailWord_1462299
  simp only [CollatzResearch.WordTrace]
  refine ⟨53334426129347938631429951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35556284086231959087619967 53334426129347938631429951)
  ·
    refine ⟨80001639194021907947144927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53334426129347938631429951 80001639194021907947144927)
    ·
      refine ⟨120002458791032861920717391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80001639194021907947144927 120002458791032861920717391)
      ·
        refine ⟨180003688186549292881076087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120002458791032861920717391 180003688186549292881076087)
        ·
          refine ⟨270005532279823939321614131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180003688186549292881076087 270005532279823939321614131)
          ·
            refine ⟨405008298419735908982421197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270005532279823939321614131 405008298419735908982421197)
            ·
              refine ⟨151878111907400965868407949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 405008298419735908982421197 151878111907400965868407949)
              ·
                refine ⟨56954291965275362200652981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151878111907400965868407949 56954291965275362200652981)
                ·
                  refine ⟨5339464871744565206311217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56954291965275362200652981 5339464871744565206311217)
                  ·
                    refine ⟨4004598653808423904733413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5339464871744565206311217 4004598653808423904733413)
                    ·
                      refine ⟨750862247589079482137515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4004598653808423904733413 750862247589079482137515)
                      ·
                        rfl

theorem cell23_1462299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 4].length) (baseStart_1462299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462299 prefixEnd_1462299 := by exact prefixLift 1462299
  have htrace : WordTrace (prefixWord ++ tailWord_1462299) baseStart_1462299 baseEnd_1462299 := by
    simpa [prefixWord, tailWord_1462299, baseEnd_1462299] using wordTrace_append hprefix tailTrace_1462299
  have hstable : (prefixWord ++ tailWord_1462299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462299).length < 2 ^ (prefixWord ++ tailWord_1462299).sum := by decide
  have hdescent : baseEnd_1462299 < baseStart_1462299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462306 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_1462306 : Nat := 118140960795 + 1462306 * 2 ^ 59
def prefixEnd_1462306 : Nat := 4983230072969 + 3 ^ 40 * 1462306 * 2
def baseEnd_1462306 : Nat := 750865841953660954749983

theorem tailTrace_1462306 : CollatzResearch.WordTrace tailWord_1462306 prefixEnd_1462306 750865841953660954749983 := by
  unfold tailWord_1462306
  simp only [CollatzResearch.WordTrace]
  refine ⟨13333670360080644706733693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35556454293548385884623181 13333670360080644706733693)
  ·
    refine ⟨5000126385030241765025135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13333670360080644706733693 5000126385030241765025135)
    ·
      refine ⟨7500189577545362647537703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5000126385030241765025135 7500189577545362647537703)
      ·
        refine ⟨11250284366318043971306555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7500189577545362647537703 11250284366318043971306555)
        ·
          refine ⟨16875426549477065956959833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11250284366318043971306555 16875426549477065956959833)
          ·
            refine ⟨12656569912107799467719875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16875426549477065956959833 12656569912107799467719875)
            ·
              refine ⟨18984854868161699201579813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12656569912107799467719875 18984854868161699201579813)
              ·
                refine ⟨3559660287780318600296215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18984854868161699201579813 3559660287780318600296215)
                ·
                  refine ⟨5339490431670477900444323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3559660287780318600296215 5339490431670477900444323)
                  ·
                    refine ⟨8009235647505716850666485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5339490431670477900444323 8009235647505716850666485)
                    ·
                      refine ⟨750865841953660954749983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8009235647505716850666485 750865841953660954749983)
                      ·
                        rfl

theorem cell23_1462306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_1462306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462306 prefixEnd_1462306 := by exact prefixLift 1462306
  have htrace : WordTrace (prefixWord ++ tailWord_1462306) baseStart_1462306 baseEnd_1462306 := by
    simpa [prefixWord, tailWord_1462306, baseEnd_1462306] using wordTrace_append hprefix tailTrace_1462306
  have hstable : (prefixWord ++ tailWord_1462306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462306).length < 2 ^ (prefixWord ++ tailWord_1462306).sum := by decide
  have hdescent : baseEnd_1462306 < baseStart_1462306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462309 : List Nat := [1, 3, 1, 2, 2, 3, 1, 10]
def baseStart_1462309 : Nat := 118140960795 + 1462309 * 2 ^ 59
def prefixEnd_1462309 : Nat := 4983230072969 + 3 ^ 40 * 1462309 * 2
def baseEnd_1462309 : Nat := 27809903051689794185647

theorem tailTrace_1462309 : CollatzResearch.WordTrace tailWord_1462309 prefixEnd_1462309 27809903051689794185647 := by
  unfold tailWord_1462309
  simp only [CollatzResearch.WordTrace]
  refine ⟨53334790859311710339293981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35556527239541140226195987 53334790859311710339293981)
  ·
    refine ⟨20000546572241891377235243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53334790859311710339293981 20000546572241891377235243)
    ·
      refine ⟨30000819858362837065852865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20000546572241891377235243 30000819858362837065852865)
      ·
        refine ⟨22500614893772127799389649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30000819858362837065852865 22500614893772127799389649)
        ·
          refine ⟨16875461170329095849542237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22500614893772127799389649 16875461170329095849542237)
          ·
            refine ⟨6328297938873410943578339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16875461170329095849542237 6328297938873410943578339)
            ·
              refine ⟨9492446908310116415367509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6328297938873410943578339 9492446908310116415367509)
              ·
                refine ⟨27809903051689794185647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9492446908310116415367509 27809903051689794185647)
                ·
                  rfl

theorem cell23_1462309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 10].length) (baseStart_1462309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462309 prefixEnd_1462309 := by exact prefixLift 1462309
  have htrace : WordTrace (prefixWord ++ tailWord_1462309) baseStart_1462309 baseEnd_1462309 := by
    simpa [prefixWord, tailWord_1462309, baseEnd_1462309] using wordTrace_append hprefix tailTrace_1462309
  have hstable : (prefixWord ++ tailWord_1462309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462309).length < 2 ^ (prefixWord ++ tailWord_1462309).sum := by decide
  have hdescent : baseEnd_1462309 < baseStart_1462309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462323 : List Nat := [1, 1, 1, 2, 4, 1, 5, 2, 1, 2, 3]
def baseStart_1462323 : Nat := 118140960795 + 1462323 * 2 ^ 59
def prefixEnd_1462323 : Nat := 4983230072969 + 3 ^ 40 * 1462323 * 2
def baseEnd_1462323 : Nat := 750874571124787388237405

theorem tailTrace_1462323 : CollatzResearch.WordTrace tailWord_1462323 prefixEnd_1462323 750874571124787388237405 := by
  unfold tailWord_1462323
  simp only [CollatzResearch.WordTrace]
  refine ⟨53335301481260990730303623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35556867654173993820202415 53335301481260990730303623)
  ·
    refine ⟨80002952221891486095455435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53335301481260990730303623 80002952221891486095455435)
    ·
      refine ⟨120004428332837229143183153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80002952221891486095455435 120004428332837229143183153)
      ·
        refine ⟨90003321249627921857387365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120004428332837229143183153 90003321249627921857387365)
        ·
          refine ⟨16875622734305235348260131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90003321249627921857387365 16875622734305235348260131)
          ·
            refine ⟨25313434101457853022390197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16875622734305235348260131 25313434101457853022390197)
            ·
              refine ⟨2373134447011673720849081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25313434101457853022390197 2373134447011673720849081)
              ·
                refine ⟨1779850835258755290636811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2373134447011673720849081 1779850835258755290636811)
                ·
                  refine ⟨2669776252888132935955217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1779850835258755290636811 2669776252888132935955217)
                  ·
                    refine ⟨2002332189666099701966413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2669776252888132935955217 2002332189666099701966413)
                    ·
                      refine ⟨750874571124787388237405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2002332189666099701966413 750874571124787388237405)
                      ·
                        rfl

theorem cell23_1462323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 2, 3].length) (baseStart_1462323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462323 prefixEnd_1462323 := by exact prefixLift 1462323
  have htrace : WordTrace (prefixWord ++ tailWord_1462323) baseStart_1462323 baseEnd_1462323 := by
    simpa [prefixWord, tailWord_1462323, baseEnd_1462323] using wordTrace_append hprefix tailTrace_1462323
  have hstable : (prefixWord ++ tailWord_1462323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462323).length < 2 ^ (prefixWord ++ tailWord_1462323).sum := by decide
  have hdescent : baseEnd_1462323 < baseStart_1462323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462326 : List Nat := [5, 1, 2, 1, 1, 1, 1, 11]
def baseStart_1462326 : Nat := 118140960795 + 1462326 * 2 ^ 59
def prefixEnd_1462326 : Nat := 4983230072969 + 3 ^ 40 * 1462326 * 2
def baseEnd_1462326 : Nat := 27810226354324106537033

theorem tailTrace_1462326 : CollatzResearch.WordTrace tailWord_1462326 prefixEnd_1462326 27810226354324106537033 := by
  unfold tailWord_1462326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3333463181265632640166427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35556940600166748161775221 3333463181265632640166427)
  ·
    refine ⟨5000194771898448960249641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3333463181265632640166427 5000194771898448960249641)
    ·
      refine ⟨3750146078923836720187231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5000194771898448960249641 3750146078923836720187231)
      ·
        refine ⟨5625219118385755080280847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3750146078923836720187231 5625219118385755080280847)
        ·
          refine ⟨8437828677578632620421271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5625219118385755080280847 8437828677578632620421271)
          ·
            refine ⟨12656743016367948930631907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8437828677578632620421271 12656743016367948930631907)
            ·
              refine ⟨18985114524551923395947861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12656743016367948930631907 18985114524551923395947861)
              ·
                refine ⟨27810226354324106537033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 18985114524551923395947861 27810226354324106537033)
                ·
                  rfl

theorem cell23_1462326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_1462326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462326 prefixEnd_1462326 := by exact prefixLift 1462326
  have htrace : WordTrace (prefixWord ++ tailWord_1462326) baseStart_1462326 baseEnd_1462326 := by
    simpa [prefixWord, tailWord_1462326, baseEnd_1462326] using wordTrace_append hprefix tailTrace_1462326
  have hstable : (prefixWord ++ tailWord_1462326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462326).length < 2 ^ (prefixWord ++ tailWord_1462326).sum := by decide
  have hdescent : baseEnd_1462326 < baseStart_1462326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462336 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 3]
def baseStart_1462336 : Nat := 118140960795 + 1462336 * 2 ^ 59
def prefixEnd_1462336 : Nat := 4983230072969 + 3 ^ 40 * 1462336 * 2
def baseEnd_1462336 : Nat := 750881246373295837374845

theorem tailTrace_1462336 : CollatzResearch.WordTrace tailWord_1462336 prefixEnd_1462336 750881246373295837374845 := by
  unfold tailWord_1462336
  simp only [CollatzResearch.WordTrace]
  refine ⟨26667887815106946975263431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35557183753475929300351241 26667887815106946975263431)
  ·
    refine ⟨40001831722660420462895147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26667887815106946975263431 40001831722660420462895147)
    ·
      refine ⟨60002747583990630694342721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40001831722660420462895147 60002747583990630694342721)
      ·
        refine ⟨45002060687992973020757041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60002747583990630694342721 45002060687992973020757041)
        ·
          refine ⟨33751545515994729765567781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45002060687992973020757041 33751545515994729765567781)
          ·
            refine ⟨6328414784249011831043959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33751545515994729765567781 6328414784249011831043959)
            ·
              refine ⟨9492622176373517746565939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6328414784249011831043959 9492622176373517746565939)
              ·
                refine ⟨14238933264560276619848909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9492622176373517746565939 14238933264560276619848909)
                ·
                  refine ⟨5339599974210103732443341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14238933264560276619848909 5339599974210103732443341)
                  ·
                    refine ⟨2002349990328788899666253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5339599974210103732443341 2002349990328788899666253)
                    ·
                      refine ⟨750881246373295837374845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2002349990328788899666253 750881246373295837374845)
                      ·
                        rfl

theorem cell23_1462336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_1462336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462336 prefixEnd_1462336 := by exact prefixLift 1462336
  have htrace : WordTrace (prefixWord ++ tailWord_1462336) baseStart_1462336 baseEnd_1462336 := by
    simpa [prefixWord, tailWord_1462336, baseEnd_1462336] using wordTrace_append hprefix tailTrace_1462336
  have hstable : (prefixWord ++ tailWord_1462336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462336).length < 2 ^ (prefixWord ++ tailWord_1462336).sum := by decide
  have hdescent : baseEnd_1462336 < baseStart_1462336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462354 : List Nat := [3, 2, 2, 1, 4, 1, 1, 4, 1, 2, 2]
def baseStart_1462354 : Nat := 118140960795 + 1462354 * 2 ^ 59
def prefixEnd_1462354 : Nat := 4983230072969 + 3 ^ 40 * 1462354 * 2
def baseEnd_1462354 : Nat := 750890489025076766949763

theorem tailTrace_1462354 : CollatzResearch.WordTrace tailWord_1462354 prefixEnd_1462354 750890489025076766949763 := by
  unfold tailWord_1462354
  simp only [CollatzResearch.WordTrace]
  refine ⟨13334108036037170756170529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35557621429432455349788077 13334108036037170756170529)
  ·
    refine ⟨10000581027027878067127897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13334108036037170756170529 10000581027027878067127897)
    ·
      refine ⟨7500435770270908550345923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10000581027027878067127897 7500435770270908550345923)
      ·
        refine ⟨11250653655406362825518885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7500435770270908550345923 11250653655406362825518885)
        ·
          refine ⟨2109497560388693029784791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11250653655406362825518885 2109497560388693029784791)
          ·
            refine ⟨3164246340583039544677187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109497560388693029784791 3164246340583039544677187)
            ·
              refine ⟨4746369510874559317015781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3164246340583039544677187 4746369510874559317015781)
              ·
                refine ⟨889944283288979871940459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4746369510874559317015781 889944283288979871940459)
                ·
                  refine ⟨1334916424933469807910689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889944283288979871940459 1334916424933469807910689)
                  ·
                    refine ⟨1001187318700102355933017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1334916424933469807910689 1001187318700102355933017)
                    ·
                      refine ⟨750890489025076766949763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1001187318700102355933017 750890489025076766949763)
                      ·
                        rfl

theorem cell23_1462354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_1462354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462354 prefixEnd_1462354 := by exact prefixLift 1462354
  have htrace : WordTrace (prefixWord ++ tailWord_1462354) baseStart_1462354 baseEnd_1462354 := by
    simpa [prefixWord, tailWord_1462354, baseEnd_1462354] using wordTrace_append hprefix tailTrace_1462354
  have hstable : (prefixWord ++ tailWord_1462354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462354).length < 2 ^ (prefixWord ++ tailWord_1462354).sum := by decide
  have hdescent : baseEnd_1462354 < baseStart_1462354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462397 : List Nat := [1, 4, 1, 1, 3, 2, 4, 1, 1, 3, 2]
def baseStart_1462397 : Nat := 118140960795 + 1462397 * 2 ^ 59
def prefixEnd_1462397 : Nat := 4983230072969 + 3 ^ 40 * 1462397 * 2
def baseEnd_1462397 : Nat := 750912568693220098712065

theorem tailTrace_1462397 : CollatzResearch.WordTrace tailWord_1462397 prefixEnd_1462397 750912568693220098712065 := by
  unfold tailWord_1462397
  simp only [CollatzResearch.WordTrace]
  refine ⟨53338000482992901368497445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35558666988661934245664963 53338000482992901368497445)
  ·
    refine ⟨10000875090561169006593271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53338000482992901368497445 10000875090561169006593271)
    ·
      refine ⟨15001312635841753509889907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10000875090561169006593271 15001312635841753509889907)
      ·
        refine ⟨22501968953762630264834861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15001312635841753509889907 22501968953762630264834861)
        ·
          refine ⟨8438238357660986349313073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22501968953762630264834861 8438238357660986349313073)
          ·
            refine ⟨6328678768245739761984805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8438238357660986349313073 6328678768245739761984805)
            ·
              refine ⟨1186627269046076205372151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6328678768245739761984805 1186627269046076205372151)
              ·
                refine ⟨1779940903569114308058227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186627269046076205372151 1779940903569114308058227)
                ·
                  refine ⟨2669911355353671462087341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1779940903569114308058227 2669911355353671462087341)
                  ·
                    refine ⟨1001216758257626798282753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2669911355353671462087341 1001216758257626798282753)
                    ·
                      refine ⟨750912568693220098712065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1001216758257626798282753 750912568693220098712065)
                      ·
                        rfl

theorem cell23_1462397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_1462397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462397 prefixEnd_1462397 := by exact prefixLift 1462397
  have htrace : WordTrace (prefixWord ++ tailWord_1462397) baseStart_1462397 baseEnd_1462397 := by
    simpa [prefixWord, tailWord_1462397, baseEnd_1462397] using wordTrace_append hprefix tailTrace_1462397
  have hstable : (prefixWord ++ tailWord_1462397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462397).length < 2 ^ (prefixWord ++ tailWord_1462397).sum := by decide
  have hdescent : baseEnd_1462397 < baseStart_1462397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462416 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 7]
def baseStart_1462416 : Nat := 118140960795 + 1462416 * 2 ^ 59
def prefixEnd_1462416 : Nat := 4983230072969 + 3 ^ 40 * 1462416 * 2
def baseEnd_1462416 : Nat := 83435813869517280486053

theorem tailTrace_1462416 : CollatzResearch.WordTrace tailWord_1462416 prefixEnd_1462416 83435813869517280486053 := by
  unfold tailWord_1462416
  simp only [CollatzResearch.WordTrace]
  refine ⟨26669346734962033806719551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35559128979949378408959401 26669346734962033806719551)
  ·
    refine ⟨40004020102443050710079327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26669346734962033806719551 40004020102443050710079327)
    ·
      refine ⟨60006030153664576065118991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40004020102443050710079327 60006030153664576065118991)
      ·
        refine ⟨90009045230496864097678487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60006030153664576065118991 90009045230496864097678487)
        ·
          refine ⟨135013567845745296146517731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90009045230496864097678487 135013567845745296146517731)
          ·
            refine ⟨202520351768617944219776597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135013567845745296146517731 202520351768617944219776597)
            ·
              refine ⟨2373285372288491533825507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 202520351768617944219776597 2373285372288491533825507)
              ·
                refine ⟨3559928058432737300738261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373285372288491533825507 3559928058432737300738261)
                ·
                  refine ⟨83435813869517280486053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3559928058432737300738261 83435813869517280486053)
                  ·
                    rfl

theorem cell23_1462416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 7].length) (baseStart_1462416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462416 prefixEnd_1462416 := by exact prefixLift 1462416
  have htrace : WordTrace (prefixWord ++ tailWord_1462416) baseStart_1462416 baseEnd_1462416 := by
    simpa [prefixWord, tailWord_1462416, baseEnd_1462416] using wordTrace_append hprefix tailTrace_1462416
  have hstable : (prefixWord ++ tailWord_1462416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462416).length < 2 ^ (prefixWord ++ tailWord_1462416).sum := by decide
  have hdescent : baseEnd_1462416 < baseStart_1462416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462456 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 1, 2, 5]
def baseStart_1462456 : Nat := 118140960795 + 1462456 * 2 ^ 59
def prefixEnd_1462456 : Nat := 4983230072969 + 3 ^ 40 * 1462456 * 2
def baseEnd_1462456 : Nat := 750942864051835367874293

theorem tailTrace_1462456 : CollatzResearch.WordTrace tailWord_1462456 prefixEnd_1462456 750942864051835367874293 := by
  unfold tailWord_1462456
  simp only [CollatzResearch.WordTrace]
  refine ⟨26670076194889577222447611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35560101593186102963263481 26670076194889577222447611)
  ·
    refine ⟨40005114292334365833671417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26670076194889577222447611 40005114292334365833671417)
    ·
      refine ⟨30003835719250774375253563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40005114292334365833671417 30003835719250774375253563)
      ·
        refine ⟨45005753578876161562880345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30003835719250774375253563 45005753578876161562880345)
        ·
          refine ⟨33754315184157121172160259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45005753578876161562880345 33754315184157121172160259)
          ·
            refine ⟨50631472776235681758240389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33754315184157121172160259 50631472776235681758240389)
            ·
              refine ⟨9493401145544190329670073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50631472776235681758240389 9493401145544190329670073)
              ·
                refine ⟨7120050859158142747252555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9493401145544190329670073 7120050859158142747252555)
                ·
                  refine ⟨10680076288737214120878833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7120050859158142747252555 10680076288737214120878833)
                  ·
                    refine ⟨8010057216552910590659125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10680076288737214120878833 8010057216552910590659125)
                    ·
                      refine ⟨750942864051835367874293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8010057216552910590659125 750942864051835367874293)
                      ·
                        rfl

theorem cell23_1462456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_1462456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462456 prefixEnd_1462456 := by exact prefixLift 1462456
  have htrace : WordTrace (prefixWord ++ tailWord_1462456) baseStart_1462456 baseEnd_1462456 := by
    simpa [prefixWord, tailWord_1462456, baseEnd_1462456] using wordTrace_append hprefix tailTrace_1462456
  have hstable : (prefixWord ++ tailWord_1462456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462456).length < 2 ^ (prefixWord ++ tailWord_1462456).sum := by decide
  have hdescent : baseEnd_1462456 < baseStart_1462456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462554 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3]
def baseStart_1462554 : Nat := 118140960795 + 1462554 * 2 ^ 59
def prefixEnd_1462554 : Nat := 4983230072969 + 3 ^ 40 * 1462554 * 2
def baseEnd_1462554 : Nat := 750993185155975984448843

theorem tailTrace_1462554 : CollatzResearch.WordTrace tailWord_1462554 prefixEnd_1462554 750993185155975984448843 := by
  unfold tailWord_1462554
  simp only [CollatzResearch.WordTrace]
  refine ⟨13335931685856029295490679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35562484495616078121308477 13335931685856029295490679)
  ·
    refine ⟨20003897528784043943236019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13335931685856029295490679 20003897528784043943236019)
    ·
      refine ⟨30005846293176065914854029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20003897528784043943236019 30005846293176065914854029)
      ·
        refine ⟨11252192359941024718070261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30005846293176065914854029 11252192359941024718070261)
        ·
          refine ⟨1054893033744471067319087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11252192359941024718070261 1054893033744471067319087)
          ·
            refine ⟨1582339550616706600978631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054893033744471067319087 1582339550616706600978631)
            ·
              refine ⟨2373509325925059901467947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582339550616706600978631 2373509325925059901467947)
              ·
                refine ⟨3560263988887589852201921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373509325925059901467947 3560263988887589852201921)
                ·
                  refine ⟨2670197991665692389151441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3560263988887589852201921 2670197991665692389151441)
                  ·
                    refine ⟨2002648493749269291863581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2670197991665692389151441 2002648493749269291863581)
                    ·
                      refine ⟨750993185155975984448843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2002648493749269291863581 750993185155975984448843)
                      ·
                        rfl

theorem cell23_1462554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_1462554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462554 prefixEnd_1462554 := by exact prefixLift 1462554
  have htrace : WordTrace (prefixWord ++ tailWord_1462554) baseStart_1462554 baseEnd_1462554 := by
    simpa [prefixWord, tailWord_1462554, baseEnd_1462554] using wordTrace_append hprefix tailTrace_1462554
  have hstable : (prefixWord ++ tailWord_1462554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462554).length < 2 ^ (prefixWord ++ tailWord_1462554).sum := by decide
  have hdescent : baseEnd_1462554 < baseStart_1462554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462574 : List Nat := [4, 1, 3, 3, 1, 2, 1, 2, 6]
def baseStart_1462574 : Nat := 118140960795 + 1462574 * 2 ^ 59
def prefixEnd_1462574 : Nat := 4983230072969 + 3 ^ 40 * 1462574 * 2
def baseEnd_1462574 : Nat := 83444828307673989577639

theorem tailTrace_1462574 : CollatzResearch.WordTrace tailWord_1462574 prefixEnd_1462574 83444828307673989577639 := by
  unfold tailWord_1462574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6668057025418957574711347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35562970802234440398460517 6668057025418957574711347)
  ·
    refine ⟨10002085538128436362067021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6668057025418957574711347 10002085538128436362067021)
    ·
      refine ⟨3750782076798163635775133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10002085538128436362067021 3750782076798163635775133)
      ·
        refine ⟨1406543278799311363415675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3750782076798163635775133 1406543278799311363415675)
        ·
          refine ⟨2109814918198967045123513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406543278799311363415675 2109814918198967045123513)
          ·
            refine ⟨1582361188649225283842635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2109814918198967045123513 1582361188649225283842635)
            ·
              refine ⟨2373541782973837925763953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582361188649225283842635 2373541782973837925763953)
              ·
                refine ⟨1780156337230378444322965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2373541782973837925763953 1780156337230378444322965)
                ·
                  refine ⟨83444828307673989577639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1780156337230378444322965 83444828307673989577639)
                  ·
                    rfl

theorem cell23_1462574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_1462574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462574 prefixEnd_1462574 := by exact prefixLift 1462574
  have htrace : WordTrace (prefixWord ++ tailWord_1462574) baseStart_1462574 baseEnd_1462574 := by
    simpa [prefixWord, tailWord_1462574, baseEnd_1462574] using wordTrace_append hprefix tailTrace_1462574
  have hstable : (prefixWord ++ tailWord_1462574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462574).length < 2 ^ (prefixWord ++ tailWord_1462574).sum := by decide
  have hdescent : baseEnd_1462574 < baseStart_1462574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462600 : List Nat := [2, 1, 3, 1, 1, 2, 2, 5, 2, 4]
def baseStart_1462600 : Nat := 118140960795 + 1462600 * 2 ^ 59
def prefixEnd_1462600 : Nat := 4983230072969 + 3 ^ 40 * 1462600 * 2
def baseEnd_1462600 : Nat := 250338935088694268157877

theorem tailTrace_1462600 : CollatzResearch.WordTrace tailWord_1462600 prefixEnd_1462600 250338935088694268157877 := by
  unfold tailWord_1462600
  simp only [CollatzResearch.WordTrace]
  refine ⟨26672702250628733519068627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35563603000838311358758169 26672702250628733519068627)
  ·
    refine ⟨40009053375943100278602941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26672702250628733519068627 40009053375943100278602941)
    ·
      refine ⟨15003395015978662604476103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40009053375943100278602941 15003395015978662604476103)
      ·
        refine ⟨22505092523967993906714155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15003395015978662604476103 22505092523967993906714155)
        ·
          refine ⟨33757638785951990860071233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22505092523967993906714155 33757638785951990860071233)
          ·
            refine ⟨25318229089463993145053425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33757638785951990860071233 25318229089463993145053425)
            ·
              refine ⟨18988671817097994858790069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25318229089463993145053425 18988671817097994858790069)
              ·
                refine ⟨1780187982852937018011569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18988671817097994858790069 1780187982852937018011569)
                ·
                  refine ⟨1335140987139702763508677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1780187982852937018011569 1335140987139702763508677)
                  ·
                    refine ⟨250338935088694268157877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1335140987139702763508677 250338935088694268157877)
                    ·
                      rfl

theorem cell23_1462600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_1462600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462600 prefixEnd_1462600 := by exact prefixLift 1462600
  have htrace : WordTrace (prefixWord ++ tailWord_1462600) baseStart_1462600 baseEnd_1462600 := by
    simpa [prefixWord, tailWord_1462600, baseEnd_1462600] using wordTrace_append hprefix tailTrace_1462600
  have hstable : (prefixWord ++ tailWord_1462600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462600).length < 2 ^ (prefixWord ++ tailWord_1462600).sum := by decide
  have hdescent : baseEnd_1462600 < baseStart_1462600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462603 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 4]
def baseStart_1462603 : Nat := 118140960795 + 1462603 * 2 ^ 59
def prefixEnd_1462603 : Nat := 4983230072969 + 3 ^ 40 * 1462603 * 2
def baseEnd_1462603 : Nat := 751018345708046292736117

theorem tailTrace_1462603 : CollatzResearch.WordTrace tailWord_1462603 prefixEnd_1462603 751018345708046292736117 := by
  unfold tailWord_1462603
  simp only [CollatzResearch.WordTrace]
  refine ⟨53345513920246598550496463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35563675946831065700330975 53345513920246598550496463)
  ·
    refine ⟨80018270880369897825744695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53345513920246598550496463 80018270880369897825744695)
    ·
      refine ⟨120027406320554846738617043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80018270880369897825744695 120027406320554846738617043)
      ·
        refine ⟨180041109480832270107925565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120027406320554846738617043 180041109480832270107925565)
        ·
          refine ⟨67515416055312101290472087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180041109480832270107925565 67515416055312101290472087)
          ·
            refine ⟨101273124082968151935708131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67515416055312101290472087 101273124082968151935708131)
            ·
              refine ⟨151909686124452227903562197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101273124082968151935708131 151909686124452227903562197)
              ·
                refine ⟨3560383268541849091489739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 151909686124452227903562197 3560383268541849091489739)
                ·
                  refine ⟨5340574902812773637234609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3560383268541849091489739 5340574902812773637234609)
                  ·
                    refine ⟨4005431177109580227925957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5340574902812773637234609 4005431177109580227925957)
                    ·
                      refine ⟨751018345708046292736117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4005431177109580227925957 751018345708046292736117)
                      ·
                        rfl

theorem cell23_1462603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 4].length) (baseStart_1462603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462603 prefixEnd_1462603 := by exact prefixLift 1462603
  have htrace : WordTrace (prefixWord ++ tailWord_1462603) baseStart_1462603 baseEnd_1462603 := by
    simpa [prefixWord, tailWord_1462603, baseEnd_1462603] using wordTrace_append hprefix tailTrace_1462603
  have hstable : (prefixWord ++ tailWord_1462603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462603).length < 2 ^ (prefixWord ++ tailWord_1462603).sum := by decide
  have hdescent : baseEnd_1462603 < baseStart_1462603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462610 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_1462610 : Nat := 118140960795 + 1462610 * 2 ^ 59
def prefixEnd_1462610 : Nat := 4983230072969 + 3 ^ 40 * 1462610 * 2
def baseEnd_1462610 : Nat := 751021940072627765348585

theorem tailTrace_1462610 : CollatzResearch.WordTrace tailWord_1462610 prefixEnd_1462610 751021940072627765348585 := by
  unfold tailWord_1462610
  simp only [CollatzResearch.WordTrace]
  refine ⟨13336442307805309686500321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35563846154147492497334189 13336442307805309686500321)
  ·
    refine ⟨10002331730853982264875241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13336442307805309686500321 10002331730853982264875241)
    ·
      refine ⟨7501748798140486698656431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10002331730853982264875241 7501748798140486698656431)
      ·
        refine ⟨11252623197210730047984647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7501748798140486698656431 11252623197210730047984647)
        ·
          refine ⟨16878934795816095071976971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11252623197210730047984647 16878934795816095071976971)
          ·
            refine ⟨25318402193724142607965457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16878934795816095071976971 25318402193724142607965457)
            ·
              refine ⟨18988801645293106955974093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25318402193724142607965457 18988801645293106955974093)
              ·
                refine ⟨7120800616984915108490285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18988801645293106955974093 7120800616984915108490285)
                ·
                  refine ⟨2670300231369343165683857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7120800616984915108490285 2670300231369343165683857)
                  ·
                    refine ⟨2002725173527007374262893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2670300231369343165683857 2002725173527007374262893)
                    ·
                      refine ⟨751021940072627765348585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2002725173527007374262893 751021940072627765348585)
                      ·
                        rfl

theorem cell23_1462610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_1462610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462610 prefixEnd_1462610 := by exact prefixLift 1462610
  have htrace : WordTrace (prefixWord ++ tailWord_1462610) baseStart_1462610 baseEnd_1462610 := by
    simpa [prefixWord, tailWord_1462610, baseEnd_1462610] using wordTrace_append hprefix tailTrace_1462610
  have hstable : (prefixWord ++ tailWord_1462610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462610).length < 2 ^ (prefixWord ++ tailWord_1462610).sum := by decide
  have hdescent : baseEnd_1462610 < baseStart_1462610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462658 : List Nat := [3, 4, 2, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_1462658 : Nat := 118140960795 + 1462658 * 2 ^ 59
def prefixEnd_1462658 : Nat := 4983230072969 + 3 ^ 40 * 1462658 * 2
def baseEnd_1462658 : Nat := 751046587144043577548365

theorem tailTrace_1462658 : CollatzResearch.WordTrace tailWord_1462658 prefixEnd_1462658 751046587144043577548365 := by
  unfold tailWord_1462658
  simp only [CollatzResearch.WordTrace]
  refine ⟨13336879983761835735937157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35565013290031561962499085 13336879983761835735937157)
  ·
    refine ⟨2500664996955344200488217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13336879983761835735937157 2500664996955344200488217)
    ·
      refine ⟨1875498747716508150366163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2500664996955344200488217 1875498747716508150366163)
      ·
        refine ⟨2813248121574762225549245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875498747716508150366163 2813248121574762225549245)
        ·
          refine ⟨1054968045590535834580967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2813248121574762225549245 1054968045590535834580967)
          ·
            refine ⟨1582452068385803751871451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054968045590535834580967 1582452068385803751871451)
            ·
              refine ⟨2373678102578705627807177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582452068385803751871451 2373678102578705627807177)
              ·
                refine ⟨1780258576934029220855383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2373678102578705627807177 1780258576934029220855383)
                ·
                  refine ⟨2670387865401043831283075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780258576934029220855383 2670387865401043831283075)
                  ·
                    refine ⟨4005581798101565746924613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2670387865401043831283075 4005581798101565746924613)
                    ·
                      refine ⟨751046587144043577548365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4005581798101565746924613 751046587144043577548365)
                      ·
                        rfl

theorem cell23_1462658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_1462658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462658 prefixEnd_1462658 := by exact prefixLift 1462658
  have htrace : WordTrace (prefixWord ++ tailWord_1462658) baseStart_1462658 baseEnd_1462658 := by
    simpa [prefixWord, tailWord_1462658, baseEnd_1462658] using wordTrace_append hprefix tailTrace_1462658
  have hstable : (prefixWord ++ tailWord_1462658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462658).length < 2 ^ (prefixWord ++ tailWord_1462658).sum := by decide
  have hdescent : baseEnd_1462658 < baseStart_1462658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462667 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 3, 3, 2]
def baseStart_1462667 : Nat := 118140960795 + 1462667 * 2 ^ 59
def prefixEnd_1462667 : Nat := 4983230072969 + 3 ^ 40 * 1462667 * 2
def baseEnd_1462667 : Nat := 751051208469934042335823

theorem tailTrace_1462667 : CollatzResearch.WordTrace tailWord_1462667 prefixEnd_1462667 751051208469934042335823 := by
  unfold tailWord_1462667
  simp only [CollatzResearch.WordTrace]
  refine ⟨53347848192014737480826255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35565232128009824987217503 53347848192014737480826255)
  ·
    refine ⟨80021772288022106221239383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53347848192014737480826255 80021772288022106221239383)
    ·
      refine ⟨120032658432033159331859075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80021772288022106221239383 120032658432033159331859075)
      ·
        refine ⟨180048987648049738997788613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120032658432033159331859075 180048987648049738997788613)
        ·
          refine ⟨33759185184009326062085365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180048987648049738997788613 33759185184009326062085365)
          ·
            refine ⟨3164923611000874318320503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33759185184009326062085365 3164923611000874318320503)
            ·
              refine ⟨4747385416501311477480755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3164923611000874318320503 4747385416501311477480755)
              ·
                refine ⟨7121078124751967216221133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4747385416501311477480755 7121078124751967216221133)
                ·
                  refine ⟨2670404296781987706082925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7121078124751967216221133 2670404296781987706082925)
                  ·
                    refine ⟨1001401611293245389781097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2670404296781987706082925 1001401611293245389781097)
                    ·
                      refine ⟨751051208469934042335823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1001401611293245389781097 751051208469934042335823)
                      ·
                        rfl

theorem cell23_1462667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 3, 2].length) (baseStart_1462667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462667 prefixEnd_1462667 := by exact prefixLift 1462667
  have htrace : WordTrace (prefixWord ++ tailWord_1462667) baseStart_1462667 baseEnd_1462667 := by
    simpa [prefixWord, tailWord_1462667, baseEnd_1462667] using wordTrace_append hprefix tailTrace_1462667
  have hstable : (prefixWord ++ tailWord_1462667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462667).length < 2 ^ (prefixWord ++ tailWord_1462667).sum := by decide
  have hdescent : baseEnd_1462667 < baseStart_1462667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462678 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1462678 : Nat := 118140960795 + 1462678 * 2 ^ 59
def prefixEnd_1462678 : Nat := 4983230072969 + 3 ^ 40 * 1462678 * 2
def baseEnd_1462678 : Nat := 751056856757133499298273

theorem tailTrace_1462678 : CollatzResearch.WordTrace tailWord_1462678 prefixEnd_1462678 751056856757133499298273 := by
  unfold tailWord_1462678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3334265587185930397467293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35565499596649924239651125 3334265587185930397467293)
  ·
    refine ⟨1250349595194723899050235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3334265587185930397467293 1250349595194723899050235)
    ·
      refine ⟨1875524392792085848575353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250349595194723899050235 1875524392792085848575353)
      ·
        refine ⟨1406643294594064386431515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1875524392792085848575353 1406643294594064386431515)
        ·
          refine ⟨2109964941891096579647273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406643294594064386431515 2109964941891096579647273)
          ·
            refine ⟨1582473706418322434735455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2109964941891096579647273 1582473706418322434735455)
            ·
              refine ⟨2373710559627483652103183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582473706418322434735455 2373710559627483652103183)
              ·
                refine ⟨3560565839441225478154775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373710559627483652103183 3560565839441225478154775)
                ·
                  refine ⟨5340848759161838217232163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3560565839441225478154775 5340848759161838217232163)
                  ·
                    refine ⟨8011273138742757325848245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5340848759161838217232163 8011273138742757325848245)
                    ·
                      refine ⟨751056856757133499298273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8011273138742757325848245 751056856757133499298273)
                      ·
                        rfl

theorem cell23_1462678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1462678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462678 prefixEnd_1462678 := by exact prefixLift 1462678
  have htrace : WordTrace (prefixWord ++ tailWord_1462678) baseStart_1462678 baseEnd_1462678 := by
    simpa [prefixWord, tailWord_1462678, baseEnd_1462678] using wordTrace_append hprefix tailTrace_1462678
  have hstable : (prefixWord ++ tailWord_1462678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462678).length < 2 ^ (prefixWord ++ tailWord_1462678).sum := by decide
  have hdescent : baseEnd_1462678 < baseStart_1462678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462690 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_1462690 : Nat := 118140960795 + 1462690 * 2 ^ 59
def prefixEnd_1462690 : Nat := 4983230072969 + 3 ^ 40 * 1462690 * 2
def baseEnd_1462690 : Nat := 250354339508329150782739

theorem tailTrace_1462690 : CollatzResearch.WordTrace tailWord_1462690 prefixEnd_1462690 250354339508329150782739 := by
  unfold tailWord_1462690
  simp only [CollatzResearch.WordTrace]
  refine ⟨13337171767732853102228381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35565791380620941605942349 13337171767732853102228381)
  ·
    refine ⟨5001439412899819913335643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13337171767732853102228381 5001439412899819913335643)
    ·
      refine ⟨7502159119349729870003465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5001439412899819913335643 7502159119349729870003465)
      ·
        refine ⟨5626619339512297402502599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7502159119349729870003465 5626619339512297402502599)
        ·
          refine ⟨8439929009268446103753899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5626619339512297402502599 8439929009268446103753899)
          ·
            refine ⟨12659893513902669155630849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8439929009268446103753899 12659893513902669155630849)
            ·
              refine ⟨9494920135427001866723137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12659893513902669155630849 9494920135427001866723137)
              ·
                refine ⟨7121190101570251400042353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9494920135427001866723137 7121190101570251400042353)
                ·
                  refine ⟨5340892576177688550031765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7121190101570251400042353 5340892576177688550031765)
                  ·
                    refine ⟨250354339508329150782739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5340892576177688550031765 250354339508329150782739)
                    ·
                      rfl

theorem cell23_1462690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_1462690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462690 prefixEnd_1462690 := by exact prefixLift 1462690
  have htrace : WordTrace (prefixWord ++ tailWord_1462690) baseStart_1462690 baseEnd_1462690 := by
    simpa [prefixWord, tailWord_1462690, baseEnd_1462690] using wordTrace_append hprefix tailTrace_1462690
  have hstable : (prefixWord ++ tailWord_1462690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462690).length < 2 ^ (prefixWord ++ tailWord_1462690).sum := by decide
  have hdescent : baseEnd_1462690 < baseStart_1462690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462697 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 4, 2, 2]
def baseStart_1462697 : Nat := 118140960795 + 1462697 * 2 ^ 59
def prefixEnd_1462697 : Nat := 4983230072969 + 3 ^ 40 * 1462697 * 2
def baseEnd_1462697 : Nat := 751066612889568924960685

theorem tailTrace_1462697 : CollatzResearch.WordTrace tailWord_1462697 prefixEnd_1462697 751066612889568924960685 := by
  unfold tailWord_1462697
  simp only [CollatzResearch.WordTrace]
  refine ⟨53348942381906052604418345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35565961587937368402945563 53348942381906052604418345)
  ·
    refine ⟨40011706786429539453313759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53348942381906052604418345 40011706786429539453313759)
    ·
      refine ⟨60017560179644309179970639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40011706786429539453313759 60017560179644309179970639)
      ·
        refine ⟨90026340269466463769955959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60017560179644309179970639 90026340269466463769955959)
        ·
          refine ⟨135039510404199695654933939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90026340269466463769955959 135039510404199695654933939)
          ·
            refine ⟨202559265606299543482400909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135039510404199695654933939 202559265606299543482400909)
            ·
              refine ⟨75959724602362328805900341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202559265606299543482400909 75959724602362328805900341)
              ·
                refine ⟨7121224181471468325553157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75959724602362328805900341 7121224181471468325553157)
                ·
                  refine ⟨1335229534025900311041217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7121224181471468325553157 1335229534025900311041217)
                  ·
                    refine ⟨1001422150519425233280913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1335229534025900311041217 1001422150519425233280913)
                    ·
                      refine ⟨751066612889568924960685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1001422150519425233280913 751066612889568924960685)
                      ·
                        rfl

theorem cell23_1462697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 2, 2].length) (baseStart_1462697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462697 prefixEnd_1462697 := by exact prefixLift 1462697
  have htrace : WordTrace (prefixWord ++ tailWord_1462697) baseStart_1462697 baseEnd_1462697 := by
    simpa [prefixWord, tailWord_1462697, baseEnd_1462697] using wordTrace_append hprefix tailTrace_1462697
  have hstable : (prefixWord ++ tailWord_1462697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462697).length < 2 ^ (prefixWord ++ tailWord_1462697).sum := by decide
  have hdescent : baseEnd_1462697 < baseStart_1462697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462730 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 1, 5, 3]
def baseStart_1462730 : Nat := 118140960795 + 1462730 * 2 ^ 59
def prefixEnd_1462730 : Nat := 4983230072969 + 3 ^ 40 * 1462730 * 2
def baseEnd_1462730 : Nat := 751083557751167295848033

theorem tailTrace_1462730 : CollatzResearch.WordTrace tailWord_1462730 prefixEnd_1462730 751083557751167295848033 := by
  unfold tailWord_1462730
  simp only [CollatzResearch.WordTrace]
  refine ⟨13337536497696624810092411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35566763993857666160246429 13337536497696624810092411)
  ·
    refine ⟨20006304746544937215138617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13337536497696624810092411 20006304746544937215138617)
    ·
      refine ⟨15004728559908702911353963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20006304746544937215138617 15004728559908702911353963)
      ·
        refine ⟨22507092839863054367030945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15004728559908702911353963 22507092839863054367030945)
        ·
          refine ⟨16880319629897290775273209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22507092839863054367030945 16880319629897290775273209)
          ·
            refine ⟨12660239722422968081454907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16880319629897290775273209 12660239722422968081454907)
            ·
              refine ⟨18990359583634452122182361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12660239722422968081454907 18990359583634452122182361)
              ·
                refine ⟨14242769687725839091636771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18990359583634452122182361 14242769687725839091636771)
                ·
                  refine ⟨21364154531588758637455157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14242769687725839091636771 21364154531588758637455157)
                  ·
                    refine ⟨2002889487336446122261421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21364154531588758637455157 2002889487336446122261421)
                    ·
                      refine ⟨751083557751167295848033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2002889487336446122261421 751083557751167295848033)
                      ·
                        rfl

theorem cell23_1462730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_1462730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462730 prefixEnd_1462730 := by exact prefixLift 1462730
  have htrace : WordTrace (prefixWord ++ tailWord_1462730) baseStart_1462730 baseEnd_1462730 := by
    simpa [prefixWord, tailWord_1462730, baseEnd_1462730] using wordTrace_append hprefix tailTrace_1462730
  have hstable : (prefixWord ++ tailWord_1462730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462730).length < 2 ^ (prefixWord ++ tailWord_1462730).sum := by decide
  have hdescent : baseEnd_1462730 < baseStart_1462730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462804 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1462804 : Nat := 118140960795 + 1462804 * 2 ^ 59
def prefixEnd_1462804 : Nat := 4983230072969 + 3 ^ 40 * 1462804 * 2
def baseEnd_1462804 : Nat := 751121555319600006322693

theorem tailTrace_1462804 : CollatzResearch.WordTrace tailWord_1462804 prefixEnd_1462804 751121555319600006322693 := by
  unfold tailWord_1462804
  simp only [CollatzResearch.WordTrace]
  refine ⟨26676422496259204939281733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35568563328345606585708977 26676422496259204939281733)
  ·
    refine ⟨5001829218048600926115325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26676422496259204939281733 5001829218048600926115325)
    ·
      refine ⟨1875685956768225347293247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5001829218048600926115325 1875685956768225347293247)
      ·
        refine ⟨2813528935152338020939871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875685956768225347293247 2813528935152338020939871)
        ·
          refine ⟨4220293402728507031409807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2813528935152338020939871 4220293402728507031409807)
          ·
            refine ⟨6330440104092760547114711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4220293402728507031409807 6330440104092760547114711)
            ·
              refine ⟨9495660156139140820672067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6330440104092760547114711 9495660156139140820672067)
              ·
                refine ⟨14243490234208711231008101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9495660156139140820672067 14243490234208711231008101)
                ·
                  refine ⟨2670654418914133355814019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14243490234208711231008101 2670654418914133355814019)
                  ·
                    refine ⟨4005981628371200033721029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2670654418914133355814019 4005981628371200033721029)
                    ·
                      refine ⟨751121555319600006322693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4005981628371200033721029 751121555319600006322693)
                      ·
                        rfl

theorem cell23_1462804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1462804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462804 prefixEnd_1462804 := by exact prefixLift 1462804
  have htrace : WordTrace (prefixWord ++ tailWord_1462804) baseStart_1462804 baseEnd_1462804 := by
    simpa [prefixWord, tailWord_1462804, baseEnd_1462804] using wordTrace_append hprefix tailTrace_1462804
  have hstable : (prefixWord ++ tailWord_1462804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462804).length < 2 ^ (prefixWord ++ tailWord_1462804).sum := by decide
  have hdescent : baseEnd_1462804 < baseStart_1462804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462810 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 8]
def baseStart_1462810 : Nat := 118140960795 + 1462810 * 2 ^ 59
def prefixEnd_1462810 : Nat := 4983230072969 + 3 ^ 40 * 1462810 * 2
def baseEnd_1462810 : Nat := 83458292911502998094185

theorem tailTrace_1462810 : CollatzResearch.WordTrace tailWord_1462810 prefixEnd_1462810 83458292911502998094185 := by
  unfold tailWord_1462810
  simp only [CollatzResearch.WordTrace]
  refine ⟨13338265957624168225820471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35568709220331115268854589 13338265957624168225820471)
  ·
    refine ⟨20007398936436252338730707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13338265957624168225820471 20007398936436252338730707)
    ·
      refine ⟨30011098404654378508096061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20007398936436252338730707 30011098404654378508096061)
      ·
        refine ⟨11254161901745391940536023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30011098404654378508096061 11254161901745391940536023)
        ·
          refine ⟨16881242852618087910804035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11254161901745391940536023 16881242852618087910804035)
          ·
            refine ⟨25321864278927131866206053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16881242852618087910804035 25321864278927131866206053)
            ·
              refine ⟨4747849552298837224913635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25321864278927131866206053 4747849552298837224913635)
              ·
                refine ⟨7121774328448255837370453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4747849552298837224913635 7121774328448255837370453)
                ·
                  refine ⟨83458292911502998094185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7121774328448255837370453 83458292911502998094185)
                  ·
                    rfl

theorem cell23_1462810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 8].length) (baseStart_1462810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462810 prefixEnd_1462810 := by exact prefixLift 1462810
  have htrace : WordTrace (prefixWord ++ tailWord_1462810) baseStart_1462810 baseEnd_1462810 := by
    simpa [prefixWord, tailWord_1462810, baseEnd_1462810] using wordTrace_append hprefix tailTrace_1462810
  have hstable : (prefixWord ++ tailWord_1462810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462810).length < 2 ^ (prefixWord ++ tailWord_1462810).sum := by decide
  have hdescent : baseEnd_1462810 < baseStart_1462810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462871 : List Nat := [1, 1, 3, 2, 2, 2, 3, 4, 1, 1, 3]
def baseStart_1462871 : Nat := 118140960795 + 1462871 * 2 ^ 59
def prefixEnd_1462871 : Nat := 4983230072969 + 3 ^ 40 * 1462871 * 2
def baseEnd_1462871 : Nat := 751155958523451244184885

theorem tailTrace_1462871 : CollatzResearch.WordTrace tailWord_1462871 prefixEnd_1462871 751155958523451244184885 := by
  unfold tailWord_1462871
  simp only [CollatzResearch.WordTrace]
  refine ⟨53355288683275680321252467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35570192455517120214168311 53355288683275680321252467)
  ·
    refine ⟨80032933024913520481878701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53355288683275680321252467 80032933024913520481878701)
    ·
      refine ⟨30012349884342570180704513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80032933024913520481878701 30012349884342570180704513)
      ·
        refine ⟨22509262413256927635528385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30012349884342570180704513 22509262413256927635528385)
        ·
          refine ⟨16881946809942695726646289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22509262413256927635528385 16881946809942695726646289)
          ·
            refine ⟨12661460107457021794984717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16881946809942695726646289 12661460107457021794984717)
            ·
              refine ⟨4748047540296383173119269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12661460107457021794984717 4748047540296383173119269)
              ·
                refine ⟨890258913805571844959863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4748047540296383173119269 890258913805571844959863)
                ·
                  refine ⟨1335388370708357767439795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 890258913805571844959863 1335388370708357767439795)
                  ·
                    refine ⟨2003082556062536651159693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1335388370708357767439795 2003082556062536651159693)
                    ·
                      refine ⟨751155958523451244184885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2003082556062536651159693 751155958523451244184885)
                      ·
                        rfl

theorem cell23_1462871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_1462871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462871 prefixEnd_1462871 := by exact prefixLift 1462871
  have htrace : WordTrace (prefixWord ++ tailWord_1462871) baseStart_1462871 baseEnd_1462871 := by
    simpa [prefixWord, tailWord_1462871, baseEnd_1462871] using wordTrace_append hprefix tailTrace_1462871
  have hstable : (prefixWord ++ tailWord_1462871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462871).length < 2 ^ (prefixWord ++ tailWord_1462871).sum := by decide
  have hdescent : baseEnd_1462871 < baseStart_1462871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462887 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 6, 4]
def baseStart_1462887 : Nat := 118140960795 + 1462887 * 2 ^ 59
def prefixEnd_1462887 : Nat := 4983230072969 + 3 ^ 40 * 1462887 * 2
def baseEnd_1462887 : Nat := 250388058071307727194937

theorem tailTrace_1462887 : CollatzResearch.WordTrace tailWord_1462887 prefixEnd_1462887 250388058071307727194937 := by
  unfold tailWord_1462887
  simp only [CollatzResearch.WordTrace]
  refine ⟨53355872251217715053834915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35570581500811810035889943 53355872251217715053834915)
  ·
    refine ⟨80033808376826572580752373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53355872251217715053834915 80033808376826572580752373)
    ·
      refine ⟨7503169535327491179445535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80033808376826572580752373 7503169535327491179445535)
      ·
        refine ⟨11254754302991236769168303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7503169535327491179445535 11254754302991236769168303)
        ·
          refine ⟨16882131454486855153752455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11254754302991236769168303 16882131454486855153752455)
          ·
            refine ⟨25323197181730282730628683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16882131454486855153752455 25323197181730282730628683)
            ·
              refine ⟨37984795772595424095943025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25323197181730282730628683 37984795772595424095943025)
              ·
                refine ⟨28488596829446568071957269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37984795772595424095943025 28488596829446568071957269)
                ·
                  refine ⟨1335402976380307878372997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28488596829446568071957269 1335402976380307878372997)
                  ·
                    refine ⟨250388058071307727194937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1335402976380307878372997 250388058071307727194937)
                    ·
                      rfl

theorem cell23_1462887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_1462887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462887 prefixEnd_1462887 := by exact prefixLift 1462887
  have htrace : WordTrace (prefixWord ++ tailWord_1462887) baseStart_1462887 baseEnd_1462887 := by
    simpa [prefixWord, tailWord_1462887, baseEnd_1462887] using wordTrace_append hprefix tailTrace_1462887
  have hstable : (prefixWord ++ tailWord_1462887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462887).length < 2 ^ (prefixWord ++ tailWord_1462887).sum := by decide
  have hdescent : baseEnd_1462887 < baseStart_1462887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462894 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1462894 : Nat := 118140960795 + 1462894 * 2 ^ 59
def prefixEnd_1462894 : Nat := 4983230072969 + 3 ^ 40 * 1462894 * 2
def baseEnd_1462894 : Nat := 751167768578504654197279

theorem tailTrace_1462894 : CollatzResearch.WordTrace tailWord_1462894 prefixEnd_1462894 751167768578504654197279 := by
  unfold tailWord_1462894
  simp only [CollatzResearch.WordTrace]
  refine ⟨6669515945274044406167467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35570751708128236832893157 6669515945274044406167467)
  ·
    refine ⟨10004273917911066609251201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6669515945274044406167467 10004273917911066609251201)
    ·
      refine ⟨7503205438433299956938401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10004273917911066609251201 7503205438433299956938401)
      ·
        refine ⟨5627404078824974967703801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7503205438433299956938401 5627404078824974967703801)
        ·
          refine ⟨4220553059118731225777851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5627404078824974967703801 4220553059118731225777851)
          ·
            refine ⟨6330829588678096838666777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4220553059118731225777851 6330829588678096838666777)
            ·
              refine ⟨4748122191508572629000083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6330829588678096838666777 4748122191508572629000083)
              ·
                refine ⟨7122183287262858943500125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4748122191508572629000083 7122183287262858943500125)
                ·
                  refine ⟨2670818732723572103812547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7122183287262858943500125 2670818732723572103812547)
                  ·
                    refine ⟨4006228099085358155718821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2670818732723572103812547 4006228099085358155718821)
                    ·
                      refine ⟨751167768578504654197279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4006228099085358155718821 751167768578504654197279)
                      ·
                        rfl

theorem cell23_1462894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1462894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462894 prefixEnd_1462894 := by exact prefixLift 1462894
  have htrace : WordTrace (prefixWord ++ tailWord_1462894) baseStart_1462894 baseEnd_1462894 := by
    simpa [prefixWord, tailWord_1462894, baseEnd_1462894] using wordTrace_append hprefix tailTrace_1462894
  have hstable : (prefixWord ++ tailWord_1462894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462894).length < 2 ^ (prefixWord ++ tailWord_1462894).sum := by decide
  have hdescent : baseEnd_1462894 < baseStart_1462894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462898 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 2, 3, 2]
def baseStart_1462898 : Nat := 118140960795 + 1462898 * 2 ^ 59
def prefixEnd_1462898 : Nat := 4983230072969 + 3 ^ 40 * 1462898 * 2
def baseEnd_1462898 : Nat := 751169822501122638547261

theorem tailTrace_1462898 : CollatzResearch.WordTrace tailWord_1462898 prefixEnd_1462898 751169822501122638547261 := by
  unfold tailWord_1462898
  simp only [CollatzResearch.WordTrace]
  refine ⟨13339068363544465983121337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35570848969451909288323565 13339068363544465983121337)
  ·
    refine ⟨10004301272658349487341003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13339068363544465983121337 10004301272658349487341003)
    ·
      refine ⟨15006451908987524231011505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10004301272658349487341003 15006451908987524231011505)
      ·
        refine ⟨11254838931740643173258629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15006451908987524231011505 11254838931740643173258629)
        ·
          refine ⟨2110282299701370594985993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11254838931740643173258629 2110282299701370594985993)
          ·
            refine ⟨1582711724776027946239495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2110282299701370594985993 1582711724776027946239495)
            ·
              refine ⟨2374067587164041919359243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582711724776027946239495 2374067587164041919359243)
              ·
                refine ⟨3561101380746062879038865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374067587164041919359243 3561101380746062879038865)
                ·
                  refine ⟨2670826035559547159279149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3561101380746062879038865 2670826035559547159279149)
                  ·
                    refine ⟨1001559763334830184729681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2670826035559547159279149 1001559763334830184729681)
                    ·
                      refine ⟨751169822501122638547261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1001559763334830184729681 751169822501122638547261)
                      ·
                        rfl

theorem cell23_1462898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_1462898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462898 prefixEnd_1462898 := by exact prefixLift 1462898
  have htrace : WordTrace (prefixWord ++ tailWord_1462898) baseStart_1462898 baseEnd_1462898 := by
    simpa [prefixWord, tailWord_1462898, baseEnd_1462898] using wordTrace_append hprefix tailTrace_1462898
  have hstable : (prefixWord ++ tailWord_1462898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462898).length < 2 ^ (prefixWord ++ tailWord_1462898).sum := by decide
  have hdescent : baseEnd_1462898 < baseStart_1462898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462938 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 1, 6]
def baseStart_1462938 : Nat := 118140960795 + 1462938 * 2 ^ 59
def prefixEnd_1462938 : Nat := 4983230072969 + 3 ^ 40 * 1462938 * 2
def baseEnd_1462938 : Nat := 250396787242434160682359

theorem tailTrace_1462938 : CollatzResearch.WordTrace tailWord_1462938 prefixEnd_1462938 250396787242434160682359 := by
  unfold tailWord_1462938
  simp only [CollatzResearch.WordTrace]
  refine ⟨13339433093508237690985367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35571821582688633842627645 13339433093508237690985367)
  ·
    refine ⟨20009149640262356536478051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13339433093508237690985367 20009149640262356536478051)
    ·
      refine ⟨30013724460393534804717077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20009149640262356536478051 30013724460393534804717077)
      ·
        refine ⟨1406893334080946943971113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30013724460393534804717077 1406893334080946943971113)
        ·
          refine ⟨1055170000560710207978335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1406893334080946943971113 1055170000560710207978335)
          ·
            refine ⟨1582755000841065311967503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055170000560710207978335 1582755000841065311967503)
            ·
              refine ⟨2374132501261597967951255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582755000841065311967503 2374132501261597967951255)
              ·
                refine ⟨3561198751892396951926883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374132501261597967951255 3561198751892396951926883)
                ·
                  refine ⟨5341798127838595427890325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3561198751892396951926883 5341798127838595427890325)
                  ·
                    refine ⟨250396787242434160682359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5341798127838595427890325 250396787242434160682359)
                    ·
                      rfl

theorem cell23_1462938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_1462938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1462938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1462938 prefixEnd_1462938 := by exact prefixLift 1462938
  have htrace : WordTrace (prefixWord ++ tailWord_1462938) baseStart_1462938 baseEnd_1462938 := by
    simpa [prefixWord, tailWord_1462938, baseEnd_1462938] using wordTrace_append hprefix tailTrace_1462938
  have hstable : (prefixWord ++ tailWord_1462938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462938).length < 2 ^ (prefixWord ++ tailWord_1462938).sum := by decide
  have hdescent : baseEnd_1462938 < baseStart_1462938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463024 : List Nat := [2, 1, 1, 1, 3, 1, 4, 5, 5]
def baseStart_1463024 : Nat := 118140960795 + 1463024 * 2 ^ 59
def prefixEnd_1463024 : Nat := 4983230072969 + 3 ^ 40 * 1463024 * 2
def baseEnd_1463024 : Nat := 83470502340398793952409

theorem tailTrace_1463024 : CollatzResearch.WordTrace tailWord_1463024 prefixEnd_1463024 83470502340398793952409 := by
  unfold tailWord_1463024
  simp only [CollatzResearch.WordTrace]
  refine ⟨26680434525860693725786063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35573912701147591634381417 26680434525860693725786063)
  ·
    refine ⟨40020651788791040588679095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26680434525860693725786063 40020651788791040588679095)
    ·
      refine ⟨60030977683186560883018643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40020651788791040588679095 60030977683186560883018643)
      ·
        refine ⟨90046466524779841324527965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60030977683186560883018643 90046466524779841324527965)
        ·
          refine ⟨33767424946792440496697987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90046466524779841324527965 33767424946792440496697987)
          ·
            refine ⟨50651137420188660745046981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33767424946792440496697987 50651137420188660745046981)
            ·
              refine ⟨9497088266285373889696309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50651137420188660745046981 9497088266285373889696309)
              ·
                refine ⟨890352024964253802159029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9497088266285373889696309 890352024964253802159029)
                ·
                  refine ⟨83470502340398793952409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 890352024964253802159029 83470502340398793952409)
                  ·
                    rfl

theorem cell23_1463024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 5].length) (baseStart_1463024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463024 prefixEnd_1463024 := by exact prefixLift 1463024
  have htrace : WordTrace (prefixWord ++ tailWord_1463024) baseStart_1463024 baseEnd_1463024 := by
    simpa [prefixWord, tailWord_1463024, baseEnd_1463024] using wordTrace_append hprefix tailTrace_1463024
  have hstable : (prefixWord ++ tailWord_1463024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463024).length < 2 ^ (prefixWord ++ tailWord_1463024).sum := by decide
  have hdescent : baseEnd_1463024 < baseStart_1463024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463071 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 2, 5]
def baseStart_1463071 : Nat := 118140960795 + 1463071 * 2 ^ 59
def prefixEnd_1463071 : Nat := 4983230072969 + 3 ^ 40 * 1463071 * 2
def baseEnd_1463071 : Nat := 250419551551450153894655

theorem tailTrace_1463071 : CollatzResearch.WordTrace tailWord_1463071 prefixEnd_1463071 250419551551450153894655 := by
  unfold tailWord_1463071
  simp only [CollatzResearch.WordTrace]
  refine ⟨53362583282551114478533067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35575055521700742985688711 53362583282551114478533067)
  ·
    refine ⟨80043874923826671717799601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53362583282551114478533067 80043874923826671717799601)
    ·
      refine ⟨60032906192870003788349701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80043874923826671717799601 60032906192870003788349701)
      ·
        refine ⟨11256169911163125710315569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60032906192870003788349701 11256169911163125710315569)
        ·
          refine ⟨8442127433372344282736677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11256169911163125710315569 8442127433372344282736677)
          ·
            refine ⟨1582898893757314553013127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8442127433372344282736677 1582898893757314553013127)
            ·
              refine ⟨2374348340635971829519691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582898893757314553013127 2374348340635971829519691)
              ·
                refine ⟨3561522510953957744279537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374348340635971829519691 3561522510953957744279537)
                ·
                  refine ⟨2671141883215468308209653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3561522510953957744279537 2671141883215468308209653)
                  ·
                    refine ⟨250419551551450153894655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2671141883215468308209653 250419551551450153894655)
                    ·
                      rfl

theorem cell23_1463071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 5].length) (baseStart_1463071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463071 prefixEnd_1463071 := by exact prefixLift 1463071
  have htrace : WordTrace (prefixWord ++ tailWord_1463071) baseStart_1463071 baseEnd_1463071 := by
    simpa [prefixWord, tailWord_1463071, baseEnd_1463071] using wordTrace_append hprefix tailTrace_1463071
  have hstable : (prefixWord ++ tailWord_1463071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463071).length < 2 ^ (prefixWord ++ tailWord_1463071).sum := by decide
  have hdescent : baseEnd_1463071 < baseStart_1463071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463084 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 5, 4]
def baseStart_1463084 : Nat := 118140960795 + 1463084 * 2 ^ 59
def prefixEnd_1463084 : Nat := 4983230072969 + 3 ^ 40 * 1463084 * 2
def baseEnd_1463084 : Nat := 250421776634286303607135

theorem tailTrace_1463084 : CollatzResearch.WordTrace tailWord_1463084 prefixEnd_1463084 250421776634286303607135 := by
  unfold tailWord_1463084
  simp only [CollatzResearch.WordTrace]
  refine ⟨26681528715752008849378153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35575371621002678465837537 26681528715752008849378153)
  ·
    refine ⟨20011146536814006637033615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26681528715752008849378153 20011146536814006637033615)
    ·
      refine ⟨30016719805221009955550423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20011146536814006637033615 30016719805221009955550423)
      ·
        refine ⟨45025079707831514933325635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30016719805221009955550423 45025079707831514933325635)
        ·
          refine ⟨67537619561747272399988453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45025079707831514933325635 67537619561747272399988453)
          ·
            refine ⟨12663303667827613574997835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67537619561747272399988453 12663303667827613574997835)
            ·
              refine ⟨18994955501741420362496753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12663303667827613574997835 18994955501741420362496753)
              ·
                refine ⟨14246216626306065271872565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18994955501741420362496753 14246216626306065271872565)
                ·
                  refine ⟨1335582808716193619238053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14246216626306065271872565 1335582808716193619238053)
                  ·
                    refine ⟨250421776634286303607135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1335582808716193619238053 250421776634286303607135)
                    ·
                      rfl

theorem cell23_1463084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_1463084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463084 prefixEnd_1463084 := by exact prefixLift 1463084
  have htrace : WordTrace (prefixWord ++ tailWord_1463084) baseStart_1463084 baseEnd_1463084 := by
    simpa [prefixWord, tailWord_1463084, baseEnd_1463084] using wordTrace_append hprefix tailTrace_1463084
  have hstable : (prefixWord ++ tailWord_1463084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463084).length < 2 ^ (prefixWord ++ tailWord_1463084).sum := by decide
  have hdescent : baseEnd_1463084 < baseStart_1463084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463091 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 2, 4, 2]
def baseStart_1463091 : Nat := 118140960795 + 1463091 * 2 ^ 59
def prefixEnd_1463091 : Nat := 4983230072969 + 3 ^ 40 * 1463091 * 2
def baseEnd_1463091 : Nat := 751268924267440383433873

theorem tailTrace_1463091 : CollatzResearch.WordTrace tailWord_1463091 prefixEnd_1463091 751268924267440383433873 := by
  unfold tailWord_1463091
  simp only [CollatzResearch.WordTrace]
  refine ⟨53363312742478657894261127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35575541828319105262840751 53363312742478657894261127)
  ·
    refine ⟨80044969113717986841391691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53363312742478657894261127 80044969113717986841391691)
    ·
      refine ⟨120067453670576980262087537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80044969113717986841391691 120067453670576980262087537)
      ·
        refine ⟨90050590252932735196565653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120067453670576980262087537 90050590252932735196565653)
        ·
          refine ⟨4221121418106221962339015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90050590252932735196565653 4221121418106221962339015)
          ·
            refine ⟨6331682127159332943508523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221121418106221962339015 6331682127159332943508523)
            ·
              refine ⟨9497523190738999415262785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6331682127159332943508523 9497523190738999415262785)
              ·
                refine ⟨7123142393054249561447089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9497523190738999415262785 7123142393054249561447089)
                ·
                  refine ⟨5342356794790687171085317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7123142393054249561447089 5342356794790687171085317)
                  ·
                    refine ⟨1001691899023253844578497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5342356794790687171085317 1001691899023253844578497)
                    ·
                      refine ⟨751268924267440383433873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1001691899023253844578497 751268924267440383433873)
                      ·
                        rfl

theorem cell23_1463091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 4, 2].length) (baseStart_1463091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463091 prefixEnd_1463091 := by exact prefixLift 1463091
  have htrace : WordTrace (prefixWord ++ tailWord_1463091) baseStart_1463091 baseEnd_1463091 := by
    simpa [prefixWord, tailWord_1463091, baseEnd_1463091] using wordTrace_append hprefix tailTrace_1463091
  have hstable : (prefixWord ++ tailWord_1463091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463091).length < 2 ^ (prefixWord ++ tailWord_1463091).sum := by decide
  have hdescent : baseEnd_1463091 < baseStart_1463091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463141 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 5, 1, 3]
def baseStart_1463141 : Nat := 118140960795 + 1463141 * 2 ^ 59
def prefixEnd_1463141 : Nat := 4983230072969 + 3 ^ 40 * 1463141 * 2
def baseEnd_1463141 : Nat := 751294598300165187808643

theorem tailTrace_1463141 : CollatzResearch.WordTrace tailWord_1463141 prefixEnd_1463141 751294598300165187808643 := by
  unfold tailWord_1463141
  simp only [CollatzResearch.WordTrace]
  refine ⟨53365136392297516433581277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35576757594865010955720851 53365136392297516433581277)
  ·
    refine ⟨20011926147111568662592979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53365136392297516433581277 20011926147111568662592979)
    ·
      refine ⟨30017889220667352993889469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20011926147111568662592979 30017889220667352993889469)
      ·
        refine ⟨11256708457750257372708551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30017889220667352993889469 11256708457750257372708551)
        ·
          refine ⟨16885062686625386059062827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11256708457750257372708551 16885062686625386059062827)
          ·
            refine ⟨25327594029938079088594241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16885062686625386059062827 25327594029938079088594241)
            ·
              refine ⟨18995695522453559316445681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25327594029938079088594241 18995695522453559316445681)
              ·
                refine ⟨14246771641840169487334261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18995695522453559316445681 14246771641840169487334261)
                ·
                  refine ⟨1335634841422515889437587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14246771641840169487334261 1335634841422515889437587)
                  ·
                    refine ⟨2003452262133773834156381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1335634841422515889437587 2003452262133773834156381)
                    ·
                      refine ⟨751294598300165187808643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2003452262133773834156381 751294598300165187808643)
                      ·
                        rfl

theorem cell23_1463141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_1463141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463141 prefixEnd_1463141 := by exact prefixLift 1463141
  have htrace : WordTrace (prefixWord ++ tailWord_1463141) baseStart_1463141 baseEnd_1463141 := by
    simpa [prefixWord, tailWord_1463141, baseEnd_1463141] using wordTrace_append hprefix tailTrace_1463141
  have hstable : (prefixWord ++ tailWord_1463141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463141).length < 2 ^ (prefixWord ++ tailWord_1463141).sum := by decide
  have hdescent : baseEnd_1463141 < baseStart_1463141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463178 : List Nat := [3, 1, 2, 4, 1, 1, 3, 2, 1, 5]
def baseStart_1463178 : Nat := 118140960795 + 1463178 * 2 ^ 59
def prefixEnd_1463178 : Nat := 4983230072969 + 3 ^ 40 * 1463178 * 2
def baseEnd_1463178 : Nat := 250437865694793847681991

theorem tailTrace_1463178 : CollatzResearch.WordTrace tailWord_1463178 prefixEnd_1463178 250437865694793847681991 := by
  unfold tailWord_1463178
  simp only [CollatzResearch.WordTrace]
  refine ⟨13341621473290867938169547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35577657262108981168452125 13341621473290867938169547)
  ·
    refine ⟨20012432209936301907254321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13341621473290867938169547 20012432209936301907254321)
    ·
      refine ⟨15009324157452226430440741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20012432209936301907254321 15009324157452226430440741)
      ·
        refine ⟨2814248279522292455707639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15009324157452226430440741 2814248279522292455707639)
        ·
          refine ⟨4221372419283438683561459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2814248279522292455707639 4221372419283438683561459)
          ·
            refine ⟨6332058628925158025342189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221372419283438683561459 6332058628925158025342189)
            ·
              refine ⟨2374521985846934259503321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6332058628925158025342189 2374521985846934259503321)
              ·
                refine ⟨1780891489385200694627491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2374521985846934259503321 1780891489385200694627491)
                ·
                  refine ⟨2671337234077801041941237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780891489385200694627491 2671337234077801041941237)
                  ·
                    refine ⟨250437865694793847681991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2671337234077801041941237 250437865694793847681991)
                    ·
                      rfl

theorem cell23_1463178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_1463178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463178 prefixEnd_1463178 := by exact prefixLift 1463178
  have htrace : WordTrace (prefixWord ++ tailWord_1463178) baseStart_1463178 baseEnd_1463178 := by
    simpa [prefixWord, tailWord_1463178, baseEnd_1463178] using wordTrace_append hprefix tailTrace_1463178
  have hstable : (prefixWord ++ tailWord_1463178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463178).length < 2 ^ (prefixWord ++ tailWord_1463178).sum := by decide
  have hdescent : baseEnd_1463178 < baseStart_1463178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463252 : List Nat := [2, 4, 1, 2, 1, 4, 2, 1, 1, 2, 3]
def baseStart_1463252 : Nat := 118140960795 + 1463252 * 2 ^ 59
def prefixEnd_1463252 : Nat := 4983230072969 + 3 ^ 40 * 1463252 * 2
def baseEnd_1463252 : Nat := 751351594652814253520633

theorem tailTrace_1463252 : CollatzResearch.WordTrace tailWord_1463252 prefixEnd_1463252 751351594652814253520633 := by
  unfold tailWord_1463252
  simp only [CollatzResearch.WordTrace]
  refine ⟨26684592447447691195436005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35579456596596921593914673 26684592447447691195436005)
  ·
    refine ⟨5003361083896442099144251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26684592447447691195436005 5003361083896442099144251)
    ·
      refine ⟨7505041625844663148716377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5003361083896442099144251 7505041625844663148716377)
      ·
        refine ⟨5628781219383497361537283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7505041625844663148716377 5628781219383497361537283)
        ·
          refine ⟨8443171829075246042305925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5628781219383497361537283 8443171829075246042305925)
          ·
            refine ⟨1583094717951608632932361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8443171829075246042305925 1583094717951608632932361)
            ·
              refine ⟨1187321038463706474699271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1583094717951608632932361 1187321038463706474699271)
              ·
                refine ⟨1780981557695559712048907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187321038463706474699271 1780981557695559712048907)
                ·
                  refine ⟨2671472336543339568073361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780981557695559712048907 2671472336543339568073361)
                  ·
                    refine ⟨2003604252407504676055021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2671472336543339568073361 2003604252407504676055021)
                    ·
                      refine ⟨751351594652814253520633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2003604252407504676055021 751351594652814253520633)
                      ·
                        rfl

theorem cell23_1463252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_1463252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463252 prefixEnd_1463252 := by exact prefixLift 1463252
  have htrace : WordTrace (prefixWord ++ tailWord_1463252) baseStart_1463252 baseEnd_1463252 := by
    simpa [prefixWord, tailWord_1463252, baseEnd_1463252] using wordTrace_append hprefix tailTrace_1463252
  have hstable : (prefixWord ++ tailWord_1463252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463252).length < 2 ^ (prefixWord ++ tailWord_1463252).sum := by decide
  have hdescent : baseEnd_1463252 < baseStart_1463252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463281 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 2, 6]
def baseStart_1463281 : Nat := 118140960795 + 1463281 * 2 ^ 59
def prefixEnd_1463281 : Nat := 4983230072969 + 3 ^ 40 * 1463281 * 2
def baseEnd_1463281 : Nat := 250455495197264880019333

theorem tailTrace_1463281 : CollatzResearch.WordTrace tailWord_1463281 prefixEnd_1463281 250455495197264880019333 := by
  unfold tailWord_1463281
  simp only [CollatzResearch.WordTrace]
  refine ⟨53370242611790320343677697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35580161741193546895785131 53370242611790320343677697)
  ·
    refine ⟨40027681958842740257758273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53370242611790320343677697 40027681958842740257758273)
    ·
      refine ⟨30020761469132055193318705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40027681958842740257758273 30020761469132055193318705)
      ·
        refine ⟨22515571101849041394989029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30020761469132055193318705 22515571101849041394989029)
        ·
          refine ⟨4221669581596695261560443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22515571101849041394989029 4221669581596695261560443)
          ·
            refine ⟨6332504372395042892340665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221669581596695261560443 6332504372395042892340665)
            ·
              refine ⟨4749378279296282169255499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6332504372395042892340665 4749378279296282169255499)
              ·
                refine ⟨7124067418944423253883249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4749378279296282169255499 7124067418944423253883249)
                ·
                  refine ⟨5343050564208317440412437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7124067418944423253883249 5343050564208317440412437)
                  ·
                    refine ⟨250455495197264880019333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5343050564208317440412437 250455495197264880019333)
                    ·
                      rfl

theorem cell23_1463281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_1463281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463281 prefixEnd_1463281 := by exact prefixLift 1463281
  have htrace : WordTrace (prefixWord ++ tailWord_1463281) baseStart_1463281 baseEnd_1463281 := by
    simpa [prefixWord, tailWord_1463281, baseEnd_1463281] using wordTrace_append hprefix tailTrace_1463281
  have hstable : (prefixWord ++ tailWord_1463281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463281).length < 2 ^ (prefixWord ++ tailWord_1463281).sum := by decide
  have hdescent : baseEnd_1463281 < baseStart_1463281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463282 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1463282 : Nat := 118140960795 + 1463282 * 2 ^ 59
def prefixEnd_1463282 : Nat := 4983230072969 + 3 ^ 40 * 1463282 * 2
def baseEnd_1463282 : Nat := 751366999072449136145495

theorem tailTrace_1463282 : CollatzResearch.WordTrace tailWord_1463282 prefixEnd_1463282 751366999072449136145495 := by
  unfold tailWord_1463282
  simp only [CollatzResearch.WordTrace]
  refine ⟨13342569771196674378616025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35580186056524465009642733 13342569771196674378616025)
  ·
    refine ⟨10006927328397505783962019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13342569771196674378616025 10006927328397505783962019)
    ·
      refine ⟨15010390992596258675943029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10006927328397505783962019 15010390992596258675943029)
      ·
        refine ⟨1407224155555899250869659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15010390992596258675943029 1407224155555899250869659)
        ·
          refine ⟨2110836233333848876304489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1407224155555899250869659 2110836233333848876304489)
          ·
            refine ⟨1583127175000386657228367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2110836233333848876304489 1583127175000386657228367)
            ·
              refine ⟨2374690762500579985842551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1583127175000386657228367 2374690762500579985842551)
              ·
                refine ⟨3562036143750869978763827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374690762500579985842551 3562036143750869978763827)
                ·
                  refine ⟨5343054215626304968145741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3562036143750869978763827 5343054215626304968145741)
                  ·
                    refine ⟨2003645330859864363054653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5343054215626304968145741 2003645330859864363054653)
                    ·
                      refine ⟨751366999072449136145495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2003645330859864363054653 751366999072449136145495)
                      ·
                        rfl

theorem cell23_1463282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1463282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463282 prefixEnd_1463282 := by exact prefixLift 1463282
  have htrace : WordTrace (prefixWord ++ tailWord_1463282) baseStart_1463282 baseEnd_1463282 := by
    simpa [prefixWord, tailWord_1463282, baseEnd_1463282] using wordTrace_append hprefix tailTrace_1463282
  have hstable : (prefixWord ++ tailWord_1463282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463282).length < 2 ^ (prefixWord ++ tailWord_1463282).sum := by decide
  have hdescent : baseEnd_1463282 < baseStart_1463282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463321 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 4, 3, 3]
def baseStart_1463321 : Nat := 118140960795 + 1463321 * 2 ^ 59
def prefixEnd_1463321 : Nat := 4983230072969 + 3 ^ 40 * 1463321 * 2
def baseEnd_1463321 : Nat := 751387024817974483557815

theorem tailTrace_1463321 : CollatzResearch.WordTrace tailWord_1463321 prefixEnd_1463321 751387024817974483557815 := by
  unfold tailWord_1463321
  simp only [CollatzResearch.WordTrace]
  refine ⟨53371701531645407175133817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35581134354430271450089211 53371701531645407175133817)
  ·
    refine ⟨40028776148734055381350363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53371701531645407175133817 40028776148734055381350363)
    ·
      refine ⟨60043164223101083072025545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40028776148734055381350363 60043164223101083072025545)
      ·
        refine ⟨45032373167325812304019159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60043164223101083072025545 45032373167325812304019159)
        ·
          refine ⟨67548559750988718456028739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45032373167325812304019159 67548559750988718456028739)
          ·
            refine ⟨101322839626483077684043109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67548559750988718456028739 101322839626483077684043109)
            ·
              refine ⟨18998032429965577065758083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101322839626483077684043109 18998032429965577065758083)
              ·
                refine ⟨28497048644948365598637125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18998032429965577065758083 28497048644948365598637125)
                ·
                  refine ⟨5343196620927818549744461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28497048644948365598637125 5343196620927818549744461)
                  ·
                    refine ⟨2003698732847931956154173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5343196620927818549744461 2003698732847931956154173)
                    ·
                      refine ⟨751387024817974483557815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2003698732847931956154173 751387024817974483557815)
                      ·
                        rfl

theorem cell23_1463321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_1463321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463321 prefixEnd_1463321 := by exact prefixLift 1463321
  have htrace : WordTrace (prefixWord ++ tailWord_1463321) baseStart_1463321 baseEnd_1463321 := by
    simpa [prefixWord, tailWord_1463321, baseEnd_1463321] using wordTrace_append hprefix tailTrace_1463321
  have hstable : (prefixWord ++ tailWord_1463321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463321).length < 2 ^ (prefixWord ++ tailWord_1463321).sum := by decide
  have hdescent : baseEnd_1463321 < baseStart_1463321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463381 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_1463381 : Nat := 118140960795 + 1463381 * 2 ^ 59
def prefixEnd_1463381 : Nat := 4983230072969 + 3 ^ 40 * 1463381 * 2
def baseEnd_1463381 : Nat := 751417833657244248807539

theorem tailTrace_1463381 : CollatzResearch.WordTrace tailWord_1463381 prefixEnd_1463381 751417833657244248807539 := by
  unfold tailWord_1463381
  simp only [CollatzResearch.WordTrace]
  refine ⟨53373889911428037422317997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35582593274285358281545331 53373889911428037422317997)
  ·
    refine ⟨20015208716785514033369249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53373889911428037422317997 20015208716785514033369249)
    ·
      refine ⟨15011406537589135525026937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20015208716785514033369249 15011406537589135525026937)
      ·
        refine ⟨11258554903191851643770203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15011406537589135525026937 11258554903191851643770203)
        ·
          refine ⟨16887832354787777465655305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11258554903191851643770203 16887832354787777465655305)
          ·
            refine ⟨12665874266090833099241479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16887832354787777465655305 12665874266090833099241479)
            ·
              refine ⟨18998811399136249648862219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12665874266090833099241479 18998811399136249648862219)
              ·
                refine ⟨28498217098704374473293329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18998811399136249648862219 28498217098704374473293329)
                ·
                  refine ⟨21373662824028280854969997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28498217098704374473293329 21373662824028280854969997)
                  ·
                    refine ⟨8015123559010605320613749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21373662824028280854969997 8015123559010605320613749)
                    ·
                      refine ⟨751417833657244248807539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8015123559010605320613749 751417833657244248807539)
                      ·
                        rfl

theorem cell23_1463381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_1463381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463381 prefixEnd_1463381 := by exact prefixLift 1463381
  have htrace : WordTrace (prefixWord ++ tailWord_1463381) baseStart_1463381 baseEnd_1463381 := by
    simpa [prefixWord, tailWord_1463381, baseEnd_1463381] using wordTrace_append hprefix tailTrace_1463381
  have hstable : (prefixWord ++ tailWord_1463381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463381).length < 2 ^ (prefixWord ++ tailWord_1463381).sum := by decide
  have hdescent : baseEnd_1463381 < baseStart_1463381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463405 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_1463405 : Nat := 118140960795 + 1463405 * 2 ^ 59
def prefixEnd_1463405 : Nat := 4983230072969 + 3 ^ 40 * 1463405 * 2
def baseEnd_1463405 : Nat := 250476719064317384969143

theorem tailTrace_1463405 : CollatzResearch.WordTrace tailWord_1463405 prefixEnd_1463405 250476719064317384969143 := by
  unfold tailWord_1463405
  simp only [CollatzResearch.WordTrace]
  refine ⟨53374765263341089521191669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35583176842227393014127779 53374765263341089521191669)
  ·
    refine ⟨5003884243438227142611719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53374765263341089521191669 5003884243438227142611719)
    ·
      refine ⟨7505826365157340713917579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5003884243438227142611719 7505826365157340713917579)
      ·
        refine ⟨11258739547736011070876369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7505826365157340713917579 11258739547736011070876369)
        ·
          refine ⟨8444054660802008303157277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11258739547736011070876369 8444054660802008303157277)
          ·
            refine ⟨3166520497800753113683979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8444054660802008303157277 3166520497800753113683979)
            ·
              refine ⟨4749780746701129670525969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3166520497800753113683979 4749780746701129670525969)
              ·
                refine ⟨3562335560025847252894477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4749780746701129670525969 3562335560025847252894477)
                ·
                  refine ⟨1335875835009692719835429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3562335560025847252894477 1335875835009692719835429)
                  ·
                    refine ⟨250476719064317384969143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1335875835009692719835429 250476719064317384969143)
                    ·
                      rfl

theorem cell23_1463405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_1463405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463405 prefixEnd_1463405 := by exact prefixLift 1463405
  have htrace : WordTrace (prefixWord ++ tailWord_1463405) baseStart_1463405 baseEnd_1463405 := by
    simpa [prefixWord, tailWord_1463405, baseEnd_1463405] using wordTrace_append hprefix tailTrace_1463405
  have hstable : (prefixWord ++ tailWord_1463405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463405).length < 2 ^ (prefixWord ++ tailWord_1463405).sum := by decide
  have hdescent : baseEnd_1463405 < baseStart_1463405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463438 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1463438 : Nat := 118140960795 + 1463438 * 2 ^ 59
def prefixEnd_1463438 : Nat := 4983230072969 + 3 ^ 40 * 1463438 * 2
def baseEnd_1463438 : Nat := 751447102054550525794777

theorem tailTrace_1463438 : CollatzResearch.WordTrace tailWord_1463438 prefixEnd_1463438 751447102054550525794777 := by
  unfold tailWord_1463438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6671996109027692019642871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35583979248147690771428645 6671996109027692019642871)
  ·
    refine ⟨10007994163541538029464307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6671996109027692019642871 10007994163541538029464307)
    ·
      refine ⟨15011991245312307044196461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10007994163541538029464307 15011991245312307044196461)
      ·
        refine ⟨5629496716992115141573673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15011991245312307044196461 5629496716992115141573673)
        ·
          refine ⟨4222122537744086356180255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5629496716992115141573673 4222122537744086356180255)
          ·
            refine ⟨6333183806616129534270383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4222122537744086356180255 6333183806616129534270383)
            ·
              refine ⟨9499775709924194301405575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6333183806616129534270383 9499775709924194301405575)
              ·
                refine ⟨14249663564886291452108363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9499775709924194301405575 14249663564886291452108363)
                ·
                  refine ⟨21374495347329437178162545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14249663564886291452108363 21374495347329437178162545)
                  ·
                    refine ⟨16030871510497077883621909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21374495347329437178162545 16030871510497077883621909)
                    ·
                      refine ⟨751447102054550525794777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16030871510497077883621909 751447102054550525794777)
                      ·
                        rfl

theorem cell23_1463438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1463438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463438 prefixEnd_1463438 := by exact prefixLift 1463438
  have htrace : WordTrace (prefixWord ++ tailWord_1463438) baseStart_1463438 baseEnd_1463438 := by
    simpa [prefixWord, tailWord_1463438, baseEnd_1463438] using wordTrace_append hprefix tailTrace_1463438
  have hstable : (prefixWord ++ tailWord_1463438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463438).length < 2 ^ (prefixWord ++ tailWord_1463438).sum := by decide
  have hdescent : baseEnd_1463438 < baseStart_1463438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463451 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 4]
def baseStart_1463451 : Nat := 118140960795 + 1463451 * 2 ^ 59
def prefixEnd_1463451 : Nat := 4983230072969 + 3 ^ 40 * 1463451 * 2
def baseEnd_1463451 : Nat := 751453777303058974932217

theorem tailTrace_1463451 : CollatzResearch.WordTrace tailWord_1463451 prefixEnd_1463451 751453777303058974932217 := by
  unfold tailWord_1463451
  simp only [CollatzResearch.WordTrace]
  refine ⟨53376443021174439377366207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35584295347449626251577471 53376443021174439377366207)
  ·
    refine ⟨80064664531761659066049311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53376443021174439377366207 80064664531761659066049311)
    ·
      refine ⟨120096996797642488599073967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80064664531761659066049311 120096996797642488599073967)
      ·
        refine ⟨180145495196463732898610951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120096996797642488599073967 180145495196463732898610951)
        ·
          refine ⟨270218242794695599347916427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180145495196463732898610951 270218242794695599347916427)
          ·
            refine ⟨405327364192043399021874641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270218242794695599347916427 405327364192043399021874641)
            ·
              refine ⟨303995523144032549266405981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405327364192043399021874641 303995523144032549266405981)
              ·
                refine ⟨113998321179012205974902243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303995523144032549266405981 113998321179012205974902243)
                ·
                  refine ⟨170997481768518308962353365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113998321179012205974902243 170997481768518308962353365)
                  ·
                    refine ⟨4007753478949647866305157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 170997481768518308962353365 4007753478949647866305157)
                    ·
                      refine ⟨751453777303058974932217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4007753478949647866305157 751453777303058974932217)
                      ·
                        rfl

theorem cell23_1463451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 4].length) (baseStart_1463451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463451 prefixEnd_1463451 := by exact prefixLift 1463451
  have htrace : WordTrace (prefixWord ++ tailWord_1463451) baseStart_1463451 baseEnd_1463451 := by
    simpa [prefixWord, tailWord_1463451, baseEnd_1463451] using wordTrace_append hprefix tailTrace_1463451
  have hstable : (prefixWord ++ tailWord_1463451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463451).length < 2 ^ (prefixWord ++ tailWord_1463451).sum := by decide
  have hdescent : baseEnd_1463451 < baseStart_1463451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463485 : List Nat := [1, 4, 1, 2, 1, 1, 4, 3, 1, 1, 4]
def baseStart_1463485 : Nat := 118140960795 + 1463485 * 2 ^ 59
def prefixEnd_1463485 : Nat := 4983230072969 + 3 ^ 40 * 1463485 * 2
def baseEnd_1463485 : Nat := 751471235645311841907061

theorem tailTrace_1463485 : CollatzResearch.WordTrace tailWord_1463485 prefixEnd_1463485 751471235645311841907061 := by
  unfold tailWord_1463485
  simp only [CollatzResearch.WordTrace]
  refine ⟨53377683103051263184103909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35585122068700842122735939 53377683103051263184103909)
  ·
    refine ⟨10008315581822111847019483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53377683103051263184103909 10008315581822111847019483)
    ·
      refine ⟨15012473372733167770529225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10008315581822111847019483 15012473372733167770529225)
      ·
        refine ⟨11259355029549875827896919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15012473372733167770529225 11259355029549875827896919)
        ·
          refine ⟨16889032544324813741845379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11259355029549875827896919 16889032544324813741845379)
          ·
            refine ⟨25333548816487220612768069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16889032544324813741845379 25333548816487220612768069)
            ·
              refine ⟨4750040403091353864894013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25333548816487220612768069 4750040403091353864894013)
              ·
                refine ⟨1781265151159257699335255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4750040403091353864894013 1781265151159257699335255)
                ·
                  refine ⟨2671897726738886549002883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781265151159257699335255 2671897726738886549002883)
                  ·
                    refine ⟨4007846590108329823504325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2671897726738886549002883 4007846590108329823504325)
                    ·
                      refine ⟨751471235645311841907061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4007846590108329823504325 751471235645311841907061)
                      ·
                        rfl

theorem cell23_1463485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_1463485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463485 prefixEnd_1463485 := by exact prefixLift 1463485
  have htrace : WordTrace (prefixWord ++ tailWord_1463485) baseStart_1463485 baseEnd_1463485 := by
    simpa [prefixWord, tailWord_1463485, baseEnd_1463485] using wordTrace_append hprefix tailTrace_1463485
  have hstable : (prefixWord ++ tailWord_1463485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463485).length < 2 ^ (prefixWord ++ tailWord_1463485).sum := by decide
  have hdescent : baseEnd_1463485 < baseStart_1463485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463489 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_1463489 : Nat := 118140960795 + 1463489 * 2 ^ 59
def prefixEnd_1463489 : Nat := 4983230072969 + 3 ^ 40 * 1463489 * 2
def baseEnd_1463489 : Nat := 751473289567929826257043

theorem tailTrace_1463489 : CollatzResearch.WordTrace tailWord_1463489 prefixEnd_1463489 751473289567929826257043 := by
  unfold tailWord_1463489
  simp only [CollatzResearch.WordTrace]
  refine ⟨53377828995036771867249521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35585219330024514578166347 53377828995036771867249521)
  ·
    refine ⟨40033371746277578900437141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53377828995036771867249521 40033371746277578900437141)
    ·
      refine ⟨1876564300606761510957991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40033371746277578900437141 1876564300606761510957991)
      ·
        refine ⟨2814846450910142266436987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876564300606761510957991 2814846450910142266436987)
        ·
          refine ⟨4222269676365213399655481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2814846450910142266436987 4222269676365213399655481)
          ·
            refine ⟨3166702257273910049741611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4222269676365213399655481 3166702257273910049741611)
            ·
              refine ⟨4750053385910865074612417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3166702257273910049741611 4750053385910865074612417)
              ·
                refine ⟨3562540039433148805959313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4750053385910865074612417 3562540039433148805959313)
                ·
                  refine ⟨2671905029574861604469485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3562540039433148805959313 2671905029574861604469485)
                  ·
                    refine ⟨1001964386090573101676057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2671905029574861604469485 1001964386090573101676057)
                    ·
                      refine ⟨751473289567929826257043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1001964386090573101676057 751473289567929826257043)
                      ·
                        rfl

theorem cell23_1463489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_1463489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463489 prefixEnd_1463489 := by exact prefixLift 1463489
  have htrace : WordTrace (prefixWord ++ tailWord_1463489) baseStart_1463489 baseEnd_1463489 := by
    simpa [prefixWord, tailWord_1463489, baseEnd_1463489] using wordTrace_append hprefix tailTrace_1463489
  have hstable : (prefixWord ++ tailWord_1463489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463489).length < 2 ^ (prefixWord ++ tailWord_1463489).sum := by decide
  have hdescent : baseEnd_1463489 < baseStart_1463489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463498 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_1463498 : Nat := 118140960795 + 1463498 * 2 ^ 59
def prefixEnd_1463498 : Nat := 4983230072969 + 3 ^ 40 * 1463498 * 2
def baseEnd_1463498 : Nat := 751477910893820291044501

theorem tailTrace_1463498 : CollatzResearch.WordTrace tailWord_1463498 prefixEnd_1463498 751477910893820291044501 := by
  unfold tailWord_1463498
  simp only [CollatzResearch.WordTrace]
  refine ⟨13344539313001041601081787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35585438168002777602884765 13344539313001041601081787)
  ·
    refine ⟨20016808969501562401622681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13344539313001041601081787 20016808969501562401622681)
    ·
      refine ⟨15012606727126171801217011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20016808969501562401622681 15012606727126171801217011)
      ·
        refine ⟨22518910090689257701825517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15012606727126171801217011 22518910090689257701825517)
        ·
          refine ⟨8444591284008471638184569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22518910090689257701825517 8444591284008471638184569)
          ·
            refine ⟨6333443463006353728638427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8444591284008471638184569 6333443463006353728638427)
            ·
              refine ⟨9500165194509530592957641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6333443463006353728638427 9500165194509530592957641)
              ·
                refine ⟨7125123895882147944718231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9500165194509530592957641 7125123895882147944718231)
                ·
                  refine ⟨10687685843823221917077347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7125123895882147944718231 10687685843823221917077347)
                  ·
                    refine ⟨16031528765734832875616021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10687685843823221917077347 16031528765734832875616021)
                    ·
                      refine ⟨751477910893820291044501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16031528765734832875616021 751477910893820291044501)
                      ·
                        rfl

theorem cell23_1463498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_1463498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463498 prefixEnd_1463498 := by exact prefixLift 1463498
  have htrace : WordTrace (prefixWord ++ tailWord_1463498) baseStart_1463498 baseEnd_1463498 := by
    simpa [prefixWord, tailWord_1463498, baseEnd_1463498] using wordTrace_append hprefix tailTrace_1463498
  have hstable : (prefixWord ++ tailWord_1463498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463498).length < 2 ^ (prefixWord ++ tailWord_1463498).sum := by decide
  have hdescent : baseEnd_1463498 < baseStart_1463498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463512 : List Nat := [2, 1, 2, 2, 5, 1, 1, 3, 2, 4]
def baseStart_1463512 : Nat := 118140960795 + 1463512 * 2 ^ 59
def prefixEnd_1463512 : Nat := 4983230072969 + 3 ^ 40 * 1463512 * 2
def baseEnd_1463512 : Nat := 250495033207661078756479

theorem tailTrace_1463512 : CollatzResearch.WordTrace tailWord_1463512 prefixEnd_1463512 250495033207661078756479 := by
  unfold tailWord_1463512
  simp only [CollatzResearch.WordTrace]
  refine ⟨26689333936976723397668395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35585778582635631196891193 26689333936976723397668395)
  ·
    refine ⟨40034000905465085096502593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26689333936976723397668395 40034000905465085096502593)
    ·
      refine ⟨30025500679098813822376945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40034000905465085096502593 30025500679098813822376945)
      ·
        refine ⟨22519125509324110366782709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30025500679098813822376945 22519125509324110366782709)
        ·
          refine ⟨2111168016499135346885879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22519125509324110366782709 2111168016499135346885879)
          ·
            refine ⟨3166752024748703020328819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2111168016499135346885879 3166752024748703020328819)
            ·
              refine ⟨4750128037123054530493229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3166752024748703020328819 4750128037123054530493229)
              ·
                refine ⟨1781298013921145448934961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4750128037123054530493229 1781298013921145448934961)
                ·
                  refine ⟨1335973510440859086701221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1781298013921145448934961 1335973510440859086701221)
                  ·
                    refine ⟨250495033207661078756479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1335973510440859086701221 250495033207661078756479)
                    ·
                      rfl

theorem cell23_1463512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_1463512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463512 prefixEnd_1463512 := by exact prefixLift 1463512
  have htrace : WordTrace (prefixWord ++ tailWord_1463512) baseStart_1463512 baseEnd_1463512 := by
    simpa [prefixWord, tailWord_1463512, baseEnd_1463512] using wordTrace_append hprefix tailTrace_1463512
  have hstable : (prefixWord ++ tailWord_1463512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463512).length < 2 ^ (prefixWord ++ tailWord_1463512).sum := by decide
  have hdescent : baseEnd_1463512 < baseStart_1463512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463553 : List Nat := [1, 2, 4, 1, 1, 5, 2, 2, 1, 2, 2]
def baseStart_1463553 : Nat := 118140960795 + 1463553 * 2 ^ 59
def prefixEnd_1463553 : Nat := 4983230072969 + 3 ^ 40 * 1463553 * 2
def baseEnd_1463553 : Nat := 751506152329817575856749

theorem tailTrace_1463553 : CollatzResearch.WordTrace tailWord_1463553 prefixEnd_1463553 751506152329817575856749 := by
  unfold tailWord_1463553
  simp only [CollatzResearch.WordTrace]
  refine ⟨53380163266804910797579313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35586775511203273865052875 53380163266804910797579313)
  ·
    refine ⟨40035122450103683098184485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53380163266804910797579313 40035122450103683098184485)
    ·
      refine ⟨7506585459394440580909591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40035122450103683098184485 7506585459394440580909591)
      ·
        refine ⟨11259878189091660871364387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7506585459394440580909591 11259878189091660871364387)
        ·
          refine ⟨16889817283637491307046581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11259878189091660871364387 16889817283637491307046581)
          ·
            refine ⟨1583420370341014810035617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16889817283637491307046581 1583420370341014810035617)
            ·
              refine ⟨1187565277755761107526713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1583420370341014810035617 1187565277755761107526713)
              ·
                refine ⟨890673958316820830645035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1187565277755761107526713 890673958316820830645035)
                ·
                  refine ⟨1336010937475231245967553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 890673958316820830645035 1336010937475231245967553)
                  ·
                    refine ⟨1002008203106423434475665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1336010937475231245967553 1002008203106423434475665)
                    ·
                      refine ⟨751506152329817575856749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1002008203106423434475665 751506152329817575856749)
                      ·
                        rfl

theorem cell23_1463553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_1463553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463553 prefixEnd_1463553 := by exact prefixLift 1463553
  have htrace : WordTrace (prefixWord ++ tailWord_1463553) baseStart_1463553 baseEnd_1463553 := by
    simpa [prefixWord, tailWord_1463553, baseEnd_1463553] using wordTrace_append hprefix tailTrace_1463553
  have hstable : (prefixWord ++ tailWord_1463553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463553).length < 2 ^ (prefixWord ++ tailWord_1463553).sum := by decide
  have hdescent : baseEnd_1463553 < baseStart_1463553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463605 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_1463605 : Nat := 118140960795 + 1463605 * 2 ^ 59
def prefixEnd_1463605 : Nat := 4983230072969 + 3 ^ 40 * 1463605 * 2
def baseEnd_1463605 : Nat := 751532853323851372406509

theorem tailTrace_1463605 : CollatzResearch.WordTrace tailWord_1463605 prefixEnd_1463605 751532853323851372406509 := by
  unfold tailWord_1463605
  simp only [CollatzResearch.WordTrace]
  refine ⟨53382059862616523678472269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35588039908411015785648179 53382059862616523678472269)
  ·
    refine ⟨20018272448481196379427101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53382059862616523678472269 20018272448481196379427101)
    ·
      refine ⟨7506852168180448642285163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20018272448481196379427101 7506852168180448642285163)
      ·
        refine ⟨11260278252270672963427745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7506852168180448642285163 11260278252270672963427745)
        ·
          refine ⟨8445208689203004722570809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11260278252270672963427745 8445208689203004722570809)
          ·
            refine ⟨6333906516902253541928107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8445208689203004722570809 6333906516902253541928107)
            ·
              refine ⟨9500859775353380312892161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6333906516902253541928107 9500859775353380312892161)
              ·
                refine ⟨7125644831515035234669121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9500859775353380312892161 7125644831515035234669121)
                ·
                  refine ⟨5344233623636276426001841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7125644831515035234669121 5344233623636276426001841)
                  ·
                    refine ⟨4008175217727207319501381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5344233623636276426001841 4008175217727207319501381)
                    ·
                      refine ⟨751532853323851372406509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4008175217727207319501381 751532853323851372406509)
                      ·
                        rfl

theorem cell23_1463605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_1463605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463605 prefixEnd_1463605 := by exact prefixLift 1463605
  have htrace : WordTrace (prefixWord ++ tailWord_1463605) baseStart_1463605 baseEnd_1463605 := by
    simpa [prefixWord, tailWord_1463605, baseEnd_1463605] using wordTrace_append hprefix tailTrace_1463605
  have hstable : (prefixWord ++ tailWord_1463605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463605).length < 2 ^ (prefixWord ++ tailWord_1463605).sum := by decide
  have hdescent : baseEnd_1463605 < baseStart_1463605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463615 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 7]
def baseStart_1463615 : Nat := 118140960795 + 1463615 * 2 ^ 59
def prefixEnd_1463615 : Nat := 4983230072969 + 3 ^ 40 * 1463615 * 2
def baseEnd_1463615 : Nat := 83504220903377370364607

theorem tailTrace_1463615 : CollatzResearch.WordTrace tailWord_1463615 prefixEnd_1463615 83504220903377370364607 := by
  unfold tailWord_1463615
  simp only [CollatzResearch.WordTrace]
  refine ⟨53382424592580295386336299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35588283061720196924224199 53382424592580295386336299)
  ·
    refine ⟨80073636888870443079504449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53382424592580295386336299 80073636888870443079504449)
    ·
      refine ⟨60055227666652832309628337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80073636888870443079504449 60055227666652832309628337)
      ·
        refine ⟨45041420749989624232221253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60055227666652832309628337 45041420749989624232221253)
        ·
          refine ⟨8445266390623054543541485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45041420749989624232221253 8445266390623054543541485)
          ·
            refine ⟨3166974896483645453828057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8445266390623054543541485 3166974896483645453828057)
            ·
              refine ⟨2375231172362734090371043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3166974896483645453828057 2375231172362734090371043)
              ·
                refine ⟨3562846758544101135556565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2375231172362734090371043 3562846758544101135556565)
                ·
                  refine ⟨83504220903377370364607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3562846758544101135556565 83504220903377370364607)
                  ·
                    rfl

theorem cell23_1463615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 7].length) (baseStart_1463615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463615 prefixEnd_1463615 := by exact prefixLift 1463615
  have htrace : WordTrace (prefixWord ++ tailWord_1463615) baseStart_1463615 baseEnd_1463615 := by
    simpa [prefixWord, tailWord_1463615, baseEnd_1463615] using wordTrace_append hprefix tailTrace_1463615
  have hstable : (prefixWord ++ tailWord_1463615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463615).length < 2 ^ (prefixWord ++ tailWord_1463615).sum := by decide
  have hdescent : baseEnd_1463615 < baseStart_1463615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463625 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 2, 3, 3]
def baseStart_1463625 : Nat := 118140960795 + 1463625 * 2 ^ 59
def prefixEnd_1463625 : Nat := 4983230072969 + 3 ^ 40 * 1463625 * 2
def baseEnd_1463625 : Nat := 751543122936941294156417

theorem tailTrace_1463625 : CollatzResearch.WordTrace tailWord_1463625 prefixEnd_1463625 751543122936941294156417 := by
  unfold tailWord_1463625
  simp only [CollatzResearch.WordTrace]
  refine ⟨53382789322544067094200329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35588526215029378062800219 53382789322544067094200329)
  ·
    refine ⟨40037091991908050320650247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53382789322544067094200329 40037091991908050320650247)
    ·
      refine ⟨60055637987862075480975371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40037091991908050320650247 60055637987862075480975371)
      ·
        refine ⟨90083456981793113221463057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60055637987862075480975371 90083456981793113221463057)
        ·
          refine ⟨67562592736344834916097293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90083456981793113221463057 67562592736344834916097293)
          ·
            refine ⟨25335972276129313093536485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67562592736344834916097293 25335972276129313093536485)
            ·
              refine ⟨4750494801774246205038091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25335972276129313093536485 4750494801774246205038091)
              ·
                refine ⟨7125742202661369307557137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4750494801774246205038091 7125742202661369307557137)
                ·
                  refine ⟨5344306651996026980667853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7125742202661369307557137 5344306651996026980667853)
                  ·
                    refine ⟨2004114994498510117750445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5344306651996026980667853 2004114994498510117750445)
                    ·
                      refine ⟨751543122936941294156417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2004114994498510117750445 751543122936941294156417)
                      ·
                        rfl

theorem cell23_1463625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 3, 3].length) (baseStart_1463625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463625 prefixEnd_1463625 := by exact prefixLift 1463625
  have htrace : WordTrace (prefixWord ++ tailWord_1463625) baseStart_1463625 baseEnd_1463625 := by
    simpa [prefixWord, tailWord_1463625, baseEnd_1463625] using wordTrace_append hprefix tailTrace_1463625
  have hstable : (prefixWord ++ tailWord_1463625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463625).length < 2 ^ (prefixWord ++ tailWord_1463625).sum := by decide
  have hdescent : baseEnd_1463625 < baseStart_1463625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463665 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 4, 1, 4]
def baseStart_1463665 : Nat := 118140960795 + 1463665 * 2 ^ 59
def prefixEnd_1463665 : Nat := 4983230072969 + 3 ^ 40 * 1463665 * 2
def baseEnd_1463665 : Nat := 751563662163121137656233

theorem tailTrace_1463665 : CollatzResearch.WordTrace tailWord_1463665 prefixEnd_1463665 751563662163121137656233 := by
  unfold tailWord_1463665
  simp only [CollatzResearch.WordTrace]
  refine ⟨53384248242399153925656449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35589498828266102617104299 53384248242399153925656449)
  ·
    refine ⟨40038186181799365444242337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53384248242399153925656449 40038186181799365444242337)
    ·
      refine ⟨30028639636349524083181753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40038186181799365444242337 30028639636349524083181753)
      ·
        refine ⟨22521479727262143062386315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30028639636349524083181753 22521479727262143062386315)
        ·
          refine ⟨33782219590893214593579473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22521479727262143062386315 33782219590893214593579473)
          ·
            refine ⟨25336664693169910945184605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33782219590893214593579473 25336664693169910945184605)
            ·
              refine ⟨9501249259938716604444227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25336664693169910945184605 9501249259938716604444227)
              ·
                refine ⟨14251873889908074906666341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9501249259938716604444227 14251873889908074906666341)
                ·
                  refine ⟨2672226354357764044999939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14251873889908074906666341 2672226354357764044999939)
                  ·
                    refine ⟨4008339531536646067499909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2672226354357764044999939 4008339531536646067499909)
                    ·
                      refine ⟨751563662163121137656233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4008339531536646067499909 751563662163121137656233)
                      ·
                        rfl

theorem cell23_1463665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_1463665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463665 prefixEnd_1463665 := by exact prefixLift 1463665
  have htrace : WordTrace (prefixWord ++ tailWord_1463665) baseStart_1463665 baseEnd_1463665 := by
    simpa [prefixWord, tailWord_1463665, baseEnd_1463665] using wordTrace_append hprefix tailTrace_1463665
  have hstable : (prefixWord ++ tailWord_1463665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463665).length < 2 ^ (prefixWord ++ tailWord_1463665).sum := by decide
  have hdescent : baseEnd_1463665 < baseStart_1463665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463685 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 3, 4, 3]
def baseStart_1463685 : Nat := 118140960795 + 1463685 * 2 ^ 59
def prefixEnd_1463685 : Nat := 4983230072969 + 3 ^ 40 * 1463685 * 2
def baseEnd_1463685 : Nat := 751573931776211059406141

theorem tailTrace_1463685 : CollatzResearch.WordTrace tailWord_1463685 prefixEnd_1463685 751573931776211059406141 := by
  unfold tailWord_1463685
  simp only [CollatzResearch.WordTrace]
  refine ⟨53384977702326697341384509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35589985134884464894256339 53384977702326697341384509)
  ·
    refine ⟨20019366638372511503019191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53384977702326697341384509 20019366638372511503019191)
    ·
      refine ⟨30029049957558767254528787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20019366638372511503019191 30029049957558767254528787)
      ·
        refine ⟨45043574936338150881793181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30029049957558767254528787 45043574936338150881793181)
        ·
          refine ⟨16891340601126806580672443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45043574936338150881793181 16891340601126806580672443)
          ·
            refine ⟨25337010901690209871008665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16891340601126806580672443 25337010901690209871008665)
            ·
              refine ⟨19002758176267657403256499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25337010901690209871008665 19002758176267657403256499)
              ·
                refine ⟨28504137264401486104884749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19002758176267657403256499 28504137264401486104884749)
                ·
                  refine ⟨10689051474150557289331781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28504137264401486104884749 10689051474150557289331781)
                  ·
                    refine ⟨2004197151403229491749709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10689051474150557289331781 2004197151403229491749709)
                    ·
                      refine ⟨751573931776211059406141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2004197151403229491749709 751573931776211059406141)
                      ·
                        rfl

theorem cell23_1463685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_1463685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463685 prefixEnd_1463685 := by exact prefixLift 1463685
  have htrace : WordTrace (prefixWord ++ tailWord_1463685) baseStart_1463685 baseEnd_1463685 := by
    simpa [prefixWord, tailWord_1463685, baseEnd_1463685] using wordTrace_append hprefix tailTrace_1463685
  have hstable : (prefixWord ++ tailWord_1463685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463685).length < 2 ^ (prefixWord ++ tailWord_1463685).sum := by decide
  have hdescent : baseEnd_1463685 < baseStart_1463685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463735 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 5, 5]
def baseStart_1463735 : Nat := 118140960795 + 1463735 * 2 ^ 59
def prefixEnd_1463735 : Nat := 4983230072969 + 3 ^ 40 * 1463735 * 2
def baseEnd_1463735 : Nat := 250533201936311954593637

theorem tailTrace_1463735 : CollatzResearch.WordTrace tailWord_1463735 prefixEnd_1463735 250533201936311954593637 := by
  unfold tailWord_1463735
  simp only [CollatzResearch.WordTrace]
  refine ⟨53386801352145555880704659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35591200901430370587136439 53386801352145555880704659)
  ·
    refine ⟨80080202028218333821056989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53386801352145555880704659 80080202028218333821056989)
    ·
      refine ⟨30030075760581875182896371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80080202028218333821056989 30030075760581875182896371)
      ·
        refine ⟨45045113640872812774344557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30030075760581875182896371 45045113640872812774344557)
        ·
          refine ⟨16891917615327304790379209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45045113640872812774344557 16891917615327304790379209)
          ·
            refine ⟨12668938211495478592784407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16891917615327304790379209 12668938211495478592784407)
            ·
              refine ⟨19003407317243217889176611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12668938211495478592784407 19003407317243217889176611)
              ·
                refine ⟨28505110975864826833764917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19003407317243217889176611 28505110975864826833764917)
                ·
                  refine ⟨2672354153987327515665461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28505110975864826833764917 2672354153987327515665461)
                  ·
                    refine ⟨250533201936311954593637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2672354153987327515665461 250533201936311954593637)
                    ·
                      rfl

theorem cell23_1463735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_1463735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463735 prefixEnd_1463735 := by exact prefixLift 1463735
  have htrace : WordTrace (prefixWord ++ tailWord_1463735) baseStart_1463735 baseEnd_1463735 := by
    simpa [prefixWord, tailWord_1463735, baseEnd_1463735] using wordTrace_append hprefix tailTrace_1463735
  have hstable : (prefixWord ++ tailWord_1463735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463735).length < 2 ^ (prefixWord ++ tailWord_1463735).sum := by decide
  have hdescent : baseEnd_1463735 < baseStart_1463735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463752 : List Nat := [2, 1, 3, 1, 3, 1, 2, 4, 1, 5]
def baseStart_1463752 : Nat := 118140960795 + 1463752 * 2 ^ 59
def prefixEnd_1463752 : Nat := 4983230072969 + 3 ^ 40 * 1463752 * 2
def baseEnd_1463752 : Nat := 250536111660020765756111

theorem tailTrace_1463752 : CollatzResearch.WordTrace tailWord_1463752 prefixEnd_1463752 250536111660020765756111 := by
  unfold tailWord_1463752
  simp only [CollatzResearch.WordTrace]
  refine ⟨26693710696541983892036755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35591614262055978522715673 26693710696541983892036755)
  ·
    refine ⟨40040566044812975838055133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26693710696541983892036755 40040566044812975838055133)
    ·
      refine ⟨15015212266804865939270675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40040566044812975838055133 15015212266804865939270675)
      ·
        refine ⟨22522818400207298908906013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15015212266804865939270675 22522818400207298908906013)
        ·
          refine ⟨8446056900077737090839755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22522818400207298908906013 8446056900077737090839755)
          ·
            refine ⟨12669085350116605636259633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8446056900077737090839755 12669085350116605636259633)
            ·
              refine ⟨9501814012587454227194725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12669085350116605636259633 9501814012587454227194725)
              ·
                refine ⟨1781590127360147667599011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9501814012587454227194725 1781590127360147667599011)
                ·
                  refine ⟨2672385191040221501398517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781590127360147667599011 2672385191040221501398517)
                  ·
                    refine ⟨250536111660020765756111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2672385191040221501398517 250536111660020765756111)
                    ·
                      rfl

theorem cell23_1463752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_1463752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463752 prefixEnd_1463752 := by exact prefixLift 1463752
  have htrace : WordTrace (prefixWord ++ tailWord_1463752) baseStart_1463752 baseEnd_1463752 := by
    simpa [prefixWord, tailWord_1463752, baseEnd_1463752] using wordTrace_append hprefix tailTrace_1463752
  have hstable : (prefixWord ++ tailWord_1463752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463752).length < 2 ^ (prefixWord ++ tailWord_1463752).sum := by decide
  have hdescent : baseEnd_1463752 < baseStart_1463752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463759 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 2, 3, 2]
def baseStart_1463759 : Nat := 118140960795 + 1463759 * 2 ^ 59
def prefixEnd_1463759 : Nat := 4983230072969 + 3 ^ 40 * 1463759 * 2
def baseEnd_1463759 : Nat := 751611929344643769880801

theorem tailTrace_1463759 : CollatzResearch.WordTrace tailWord_1463759 prefixEnd_1463759 751611929344643769880801 := by
  unfold tailWord_1463759
  simp only [CollatzResearch.WordTrace]
  refine ⟨53387676704058607979578331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35591784469372405319718887 53387676704058607979578331)
  ·
    refine ⟨80081515056087911969367497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53387676704058607979578331 80081515056087911969367497)
    ·
      refine ⟨60061136292065933977025623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80081515056087911969367497 60061136292065933977025623)
      ·
        refine ⟨90091704438098900965538435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60061136292065933977025623 90091704438098900965538435)
        ·
          refine ⟨135137556657148351448307653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90091704438098900965538435 135137556657148351448307653)
          ·
            refine ⟨25338291873215315896557685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135137556657148351448307653 25338291873215315896557685)
            ·
              refine ⟨2375464863113935865302283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25338291873215315896557685 2375464863113935865302283)
              ·
                refine ⟨3563197294670903797953425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2375464863113935865302283 3563197294670903797953425)
                ·
                  refine ⟨2672397971003177848465069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3563197294670903797953425 2672397971003177848465069)
                  ·
                    refine ⟨1002149239126191693174401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2672397971003177848465069 1002149239126191693174401)
                    ·
                      refine ⟨751611929344643769880801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1002149239126191693174401 751611929344643769880801)
                      ·
                        rfl

theorem cell23_1463759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 3, 2].length) (baseStart_1463759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463759 prefixEnd_1463759 := by exact prefixLift 1463759
  have htrace : WordTrace (prefixWord ++ tailWord_1463759) baseStart_1463759 baseEnd_1463759 := by
    simpa [prefixWord, tailWord_1463759, baseEnd_1463759] using wordTrace_append hprefix tailTrace_1463759
  have hstable : (prefixWord ++ tailWord_1463759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463759).length < 2 ^ (prefixWord ++ tailWord_1463759).sum := by decide
  have hdescent : baseEnd_1463759 < baseStart_1463759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463769 : List Nat := [1, 2, 1, 2, 4, 2, 4, 1, 1, 5]
def baseStart_1463769 : Nat := 118140960795 + 1463769 * 2 ^ 59
def prefixEnd_1463769 : Nat := 4983230072969 + 3 ^ 40 * 1463769 * 2
def baseEnd_1463769 : Nat := 250539021383729576918585

theorem tailTrace_1463769 : CollatzResearch.WordTrace tailWord_1463769 prefixEnd_1463769 250539021383729576918585 := by
  unfold tailWord_1463769
  simp only [CollatzResearch.WordTrace]
  refine ⟨53388041434022379687442361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35592027622681586458294907 53388041434022379687442361)
  ·
    refine ⟨40041031075516784765581771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53388041434022379687442361 40041031075516784765581771)
    ·
      refine ⟨60061546613275177148372657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40041031075516784765581771 60061546613275177148372657)
      ·
        refine ⟨45046159959956382861279493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60061546613275177148372657 45046159959956382861279493)
        ·
          refine ⟨8446154992491821786489905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45046159959956382861279493 8446154992491821786489905)
          ·
            refine ⟨6334616244368866339867429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8446154992491821786489905 6334616244368866339867429)
            ·
              refine ⟨1187740545819162438725143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6334616244368866339867429 1187740545819162438725143)
              ·
                refine ⟨1781610818728743658087715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187740545819162438725143 1781610818728743658087715)
                ·
                  refine ⟨2672416228093115487131573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781610818728743658087715 2672416228093115487131573)
                  ·
                    refine ⟨250539021383729576918585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2672416228093115487131573 250539021383729576918585)
                    ·
                      rfl

theorem cell23_1463769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 1, 5].length) (baseStart_1463769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463769 prefixEnd_1463769 := by exact prefixLift 1463769
  have htrace : WordTrace (prefixWord ++ tailWord_1463769) baseStart_1463769 baseEnd_1463769 := by
    simpa [prefixWord, tailWord_1463769, baseEnd_1463769] using wordTrace_append hprefix tailTrace_1463769
  have hstable : (prefixWord ++ tailWord_1463769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463769).length < 2 ^ (prefixWord ++ tailWord_1463769).sum := by decide
  have hdescent : baseEnd_1463769 < baseStart_1463769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463792 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 5]
def baseStart_1463792 : Nat := 118140960795 + 1463792 * 2 ^ 59
def prefixEnd_1463792 : Nat := 4983230072969 + 3 ^ 40 * 1463792 * 2
def baseEnd_1463792 : Nat := 751628874206242140768149

theorem tailTrace_1463792 : CollatzResearch.WordTrace tailWord_1463792 prefixEnd_1463792 751628874206242140768149 := by
  unfold tailWord_1463792
  simp only [CollatzResearch.WordTrace]
  refine ⟨26694440156469527307764815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35592586875292703077019753 26694440156469527307764815)
  ·
    refine ⟨40041660234704290961647223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26694440156469527307764815 40041660234704290961647223)
    ·
      refine ⟨60062490352056436442470835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40041660234704290961647223 60062490352056436442470835)
      ·
        refine ⟨90093735528084654663706253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60062490352056436442470835 90093735528084654663706253)
        ·
          refine ⟨33785150823031745498889845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90093735528084654663706253 33785150823031745498889845)
          ·
            refine ⟨3167357889659226140520923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33785150823031745498889845 3167357889659226140520923)
            ·
              refine ⟨4751036834488839210781385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167357889659226140520923 4751036834488839210781385)
              ·
                refine ⟨3563277625866629408086039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4751036834488839210781385 3563277625866629408086039)
                ·
                  refine ⟨5344916438799944112129059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3563277625866629408086039 5344916438799944112129059)
                  ·
                    refine ⟨8017374658199916168193589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5344916438799944112129059 8017374658199916168193589)
                    ·
                      refine ⟨751628874206242140768149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8017374658199916168193589 751628874206242140768149)
                      ·
                        rfl

theorem cell23_1463792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_1463792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463792 prefixEnd_1463792 := by exact prefixLift 1463792
  have htrace : WordTrace (prefixWord ++ tailWord_1463792) baseStart_1463792 baseEnd_1463792 := by
    simpa [prefixWord, tailWord_1463792, baseEnd_1463792] using wordTrace_append hprefix tailTrace_1463792
  have hstable : (prefixWord ++ tailWord_1463792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463792).length < 2 ^ (prefixWord ++ tailWord_1463792).sum := by decide
  have hdescent : baseEnd_1463792 < baseStart_1463792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463839 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 4, 1, 3]
def baseStart_1463839 : Nat := 118140960795 + 1463839 * 2 ^ 59
def prefixEnd_1463839 : Nat := 4983230072969 + 3 ^ 40 * 1463839 * 2
def baseEnd_1463839 : Nat := 751653007797003456880433

theorem tailTrace_1463839 : CollatzResearch.WordTrace tailWord_1463839 prefixEnd_1463839 751653007797003456880433 := by
  unfold tailWord_1463839
  simp only [CollatzResearch.WordTrace]
  refine ⟨53390594543768781642490571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35593729695845854428327047 53390594543768781642490571)
  ·
    refine ⟨80085891815653172463735857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53390594543768781642490571 80085891815653172463735857)
    ·
      refine ⟨60064418861739879347801893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80085891815653172463735857 60064418861739879347801893)
      ·
        refine ⟨11262078536576227377712855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60064418861739879347801893 11262078536576227377712855)
        ·
          refine ⟨16893117804864341066569283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11262078536576227377712855 16893117804864341066569283)
          ·
            refine ⟨25339676707296511599853925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16893117804864341066569283 25339676707296511599853925)
            ·
              refine ⟨4751189382618095924972611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25339676707296511599853925 4751189382618095924972611)
              ·
                refine ⟨7126784073927143887458917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751189382618095924972611 7126784073927143887458917)
                ·
                  refine ⟨1336272013861339478898547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7126784073927143887458917 1336272013861339478898547)
                  ·
                    refine ⟨2004408020792009218347821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1336272013861339478898547 2004408020792009218347821)
                    ·
                      refine ⟨751653007797003456880433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2004408020792009218347821 751653007797003456880433)
                      ·
                        rfl

theorem cell23_1463839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_1463839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463839 prefixEnd_1463839 := by exact prefixLift 1463839
  have htrace : WordTrace (prefixWord ++ tailWord_1463839) baseStart_1463839 baseEnd_1463839 := by
    simpa [prefixWord, tailWord_1463839, baseEnd_1463839] using wordTrace_append hprefix tailTrace_1463839
  have hstable : (prefixWord ++ tailWord_1463839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463839).length < 2 ^ (prefixWord ++ tailWord_1463839).sum := by decide
  have hdescent : baseEnd_1463839 < baseStart_1463839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463882 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_1463882 : Nat := 118140960795 + 1463882 * 2 ^ 59
def prefixEnd_1463882 : Nat := 4983230072969 + 3 ^ 40 * 1463882 * 2
def baseEnd_1463882 : Nat := 751675087465146788642735

theorem tailTrace_1463882 : CollatzResearch.WordTrace tailWord_1463882 prefixEnd_1463882 751675087465146788642735 := by
  unfold tailWord_1463882
  simp only [CollatzResearch.WordTrace]
  refine ⟨13348040720653249996576475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35594775255075333324203933 13348040720653249996576475)
  ·
    refine ⟨20022061080979874994864713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13348040720653249996576475 20022061080979874994864713)
    ·
      refine ⟨15016545810734906246148535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20022061080979874994864713 15016545810734906246148535)
      ·
        refine ⟨22524818716102359369222803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15016545810734906246148535 22524818716102359369222803)
        ·
          refine ⟨33787228074153539053834205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22524818716102359369222803 33787228074153539053834205)
          ·
            refine ⟨12670210527807577145187827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33787228074153539053834205 12670210527807577145187827)
            ·
              refine ⟨19005315791711365717781741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12670210527807577145187827 19005315791711365717781741)
              ·
                refine ⟨7126993421891762144168153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19005315791711365717781741 7126993421891762144168153)
                ·
                  refine ⟨5345245066418821608126115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7126993421891762144168153 5345245066418821608126115)
                  ·
                    refine ⟨8017867599628232412189173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5345245066418821608126115 8017867599628232412189173)
                    ·
                      refine ⟨751675087465146788642735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8017867599628232412189173 751675087465146788642735)
                      ·
                        rfl

theorem cell23_1463882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_1463882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463882 prefixEnd_1463882 := by exact prefixLift 1463882
  have htrace : WordTrace (prefixWord ++ tailWord_1463882) baseStart_1463882 baseEnd_1463882 := by
    simpa [prefixWord, tailWord_1463882, baseEnd_1463882] using wordTrace_append hprefix tailTrace_1463882
  have hstable : (prefixWord ++ tailWord_1463882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463882).length < 2 ^ (prefixWord ++ tailWord_1463882).sum := by decide
  have hdescent : baseEnd_1463882 < baseStart_1463882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463909 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 2, 2, 4]
def baseStart_1463909 : Nat := 118140960795 + 1463909 * 2 ^ 59
def prefixEnd_1463909 : Nat := 4983230072969 + 3 ^ 40 * 1463909 * 2
def baseEnd_1463909 : Nat := 751688951442818183005111

theorem tailTrace_1463909 : CollatzResearch.WordTrace tailWord_1463909 prefixEnd_1463909 751688951442818183005111 := by
  unfold tailWord_1463909
  simp only [CollatzResearch.WordTrace]
  refine ⟨53393147653515183597538781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35595431769010122398359187 53393147653515183597538781)
  ·
    refine ⟨20022430370068193849077043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53393147653515183597538781 20022430370068193849077043)
    ·
      refine ⟨30033645555102290773615565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20022430370068193849077043 30033645555102290773615565)
      ·
        refine ⟨11262617083163359040105837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30033645555102290773615565 11262617083163359040105837)
        ·
          refine ⟨4223481406186259640039689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11262617083163359040105837 4223481406186259640039689)
          ·
            refine ⟨3167611054639694730029767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4223481406186259640039689 3167611054639694730029767)
            ·
              refine ⟨4751416581959542095044651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167611054639694730029767 4751416581959542095044651)
              ·
                refine ⟨7127124872939313142566977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751416581959542095044651 7127124872939313142566977)
                ·
                  refine ⟨5345343654704484856925233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7127124872939313142566977 5345343654704484856925233)
                  ·
                    refine ⟨4009007741028363642693925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5345343654704484856925233 4009007741028363642693925)
                    ·
                      refine ⟨751688951442818183005111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4009007741028363642693925 751688951442818183005111)
                      ·
                        rfl

theorem cell23_1463909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_1463909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463909 prefixEnd_1463909 := by exact prefixLift 1463909
  have htrace : WordTrace (prefixWord ++ tailWord_1463909) baseStart_1463909 baseEnd_1463909 := by
    simpa [prefixWord, tailWord_1463909, baseEnd_1463909] using wordTrace_append hprefix tailTrace_1463909
  have hstable : (prefixWord ++ tailWord_1463909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463909).length < 2 ^ (prefixWord ++ tailWord_1463909).sum := by decide
  have hdescent : baseEnd_1463909 < baseStart_1463909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463969 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1463969 : Nat := 118140960795 + 1463969 * 2 ^ 59
def prefixEnd_1463969 : Nat := 4983230072969 + 3 ^ 40 * 1463969 * 2
def baseEnd_1463969 : Nat := 751719760282087948254835

theorem tailTrace_1463969 : CollatzResearch.WordTrace tailWord_1463969 prefixEnd_1463969 751719760282087948254835 := by
  unfold tailWord_1463969
  simp only [CollatzResearch.WordTrace]
  refine ⟨53395336033297813844722961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35596890688865209229815307 53395336033297813844722961)
  ·
    refine ⟨40046502024973360383542221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53395336033297813844722961 40046502024973360383542221)
    ·
      refine ⟨15017438259365010143828333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40046502024973360383542221 15017438259365010143828333)
      ·
        refine ⟨5631539347261878803935625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15017438259365010143828333 5631539347261878803935625)
        ·
          refine ⟨4223654510446409102951719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5631539347261878803935625 4223654510446409102951719)
          ·
            refine ⟨6335481765669613654427579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223654510446409102951719 6335481765669613654427579)
            ·
              refine ⟨9503222648504420481641369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6335481765669613654427579 9503222648504420481641369)
              ·
                refine ⟨7127416986378315361231027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9503222648504420481641369 7127416986378315361231027)
                ·
                  refine ⟨10691125479567473041846541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7127416986378315361231027 10691125479567473041846541)
                  ·
                    refine ⟨4009172054837802390692453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10691125479567473041846541 4009172054837802390692453)
                    ·
                      refine ⟨751719760282087948254835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4009172054837802390692453 751719760282087948254835)
                      ·
                        rfl

theorem cell23_1463969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1463969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1463969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1463969 prefixEnd_1463969 := by exact prefixLift 1463969
  have htrace : WordTrace (prefixWord ++ tailWord_1463969) baseStart_1463969 baseEnd_1463969 := by
    simpa [prefixWord, tailWord_1463969, baseEnd_1463969] using wordTrace_append hprefix tailTrace_1463969
  have hstable : (prefixWord ++ tailWord_1463969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463969).length < 2 ^ (prefixWord ++ tailWord_1463969).sum := by decide
  have hdescent : baseEnd_1463969 < baseStart_1463969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464026 : List Nat := [3, 1, 1, 2, 2, 3, 4, 1, 6]
def baseStart_1464026 : Nat := 118140960795 + 1464026 * 2 ^ 59
def prefixEnd_1464026 : Nat := 4983230072969 + 3 ^ 40 * 1464026 * 2
def baseEnd_1464026 : Nat := 83527669853266025026897

theorem tailTrace_1464026 : CollatzResearch.WordTrace tailWord_1464026 prefixEnd_1464026 83527669853266025026897 := by
  unfold tailWord_1464026
  simp only [CollatzResearch.WordTrace]
  refine ⟨13349353748522828144886983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35598276662727541719698621 13349353748522828144886983)
  ·
    refine ⟨20024030622784242217330475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13349353748522828144886983 20024030622784242217330475)
    ·
      refine ⟨30036045934176363325995713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20024030622784242217330475 30036045934176363325995713)
      ·
        refine ⟨22527034450632272494496785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30036045934176363325995713 22527034450632272494496785)
        ·
          refine ⟨16895275837974204370872589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22527034450632272494496785 16895275837974204370872589)
          ·
            refine ⟨6335728439240326639077221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16895275837974204370872589 6335728439240326639077221)
            ·
              refine ⟨1187949082357561244826979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6335728439240326639077221 1187949082357561244826979)
              ·
                refine ⟨1781923623536341867240469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187949082357561244826979 1781923623536341867240469)
                ·
                  refine ⟨83527669853266025026897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1781923623536341867240469 83527669853266025026897)
                  ·
                    rfl

theorem cell23_1464026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 6].length) (baseStart_1464026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464026 prefixEnd_1464026 := by exact prefixLift 1464026
  have htrace : WordTrace (prefixWord ++ tailWord_1464026) baseStart_1464026 baseEnd_1464026 := by
    simpa [prefixWord, tailWord_1464026, baseEnd_1464026] using wordTrace_append hprefix tailTrace_1464026
  have hstable : (prefixWord ++ tailWord_1464026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464026).length < 2 ^ (prefixWord ++ tailWord_1464026).sum := by decide
  have hdescent : baseEnd_1464026 < baseStart_1464026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464036 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 5, 1, 3]
def baseStart_1464036 : Nat := 118140960795 + 1464036 * 2 ^ 59
def prefixEnd_1464036 : Nat := 4983230072969 + 3 ^ 40 * 1464036 * 2
def baseEnd_1464036 : Nat := 751754163485939186117027

theorem tailTrace_1464036 : CollatzResearch.WordTrace tailWord_1464036 prefixEnd_1464036 751754163485939186117027 := by
  unfold tailWord_1464036
  simp only [CollatzResearch.WordTrace]
  refine ⟨26698889862027542143705981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35598519816036722858274641 26698889862027542143705981)
  ·
    refine ⟨10012083698260328303889743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26698889862027542143705981 10012083698260328303889743)
    ·
      refine ⟨15018125547390492455834615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10012083698260328303889743 15018125547390492455834615)
      ·
        refine ⟨22527188321085738683751923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15018125547390492455834615 22527188321085738683751923)
        ·
          refine ⟨33790782481628608025627885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22527188321085738683751923 33790782481628608025627885)
          ·
            refine ⟨12671543430610728009610457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33790782481628608025627885 12671543430610728009610457)
            ·
              refine ⟨9503657572958046007207843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12671543430610728009610457 9503657572958046007207843)
              ·
                refine ⟨14255486359437069010811765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9503657572958046007207843 14255486359437069010811765)
                ·
                  refine ⟨1336451846197225219763603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14255486359437069010811765 1336451846197225219763603)
                  ·
                    refine ⟨2004677769295837829645405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1336451846197225219763603 2004677769295837829645405)
                    ·
                      refine ⟨751754163485939186117027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2004677769295837829645405 751754163485939186117027)
                      ·
                        rfl

theorem cell23_1464036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_1464036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464036 prefixEnd_1464036 := by exact prefixLift 1464036
  have htrace : WordTrace (prefixWord ++ tailWord_1464036) baseStart_1464036 baseEnd_1464036 := by
    simpa [prefixWord, tailWord_1464036, baseEnd_1464036] using wordTrace_append hprefix tailTrace_1464036
  have hstable : (prefixWord ++ tailWord_1464036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464036).length < 2 ^ (prefixWord ++ tailWord_1464036).sum := by decide
  have hdescent : baseEnd_1464036 < baseStart_1464036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464096 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 3]
def baseStart_1464096 : Nat := 118140960795 + 1464096 * 2 ^ 59
def prefixEnd_1464096 : Nat := 4983230072969 + 3 ^ 40 * 1464096 * 2
def baseEnd_1464096 : Nat := 751784972325208951366751

theorem tailTrace_1464096 : CollatzResearch.WordTrace tailWord_1464096 prefixEnd_1464096 751784972325208951366751 := by
  unfold tailWord_1464096
  simp only [CollatzResearch.WordTrace]
  refine ⟨26699984051918857267298071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35599978735891809689730761 26699984051918857267298071)
  ·
    refine ⟨40049976077878285900947107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26699984051918857267298071 40049976077878285900947107)
    ·
      refine ⟨60074964116817428851420661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40049976077878285900947107 60074964116817428851420661)
      ·
        refine ⟨5632027885951633954820687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60074964116817428851420661 5632027885951633954820687)
        ·
          refine ⟨8448041828927450932231031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5632027885951633954820687 8448041828927450932231031)
          ·
            refine ⟨12672062743391176398346547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8448041828927450932231031 12672062743391176398346547)
            ·
              refine ⟨19008094115086764597519821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12672062743391176398346547 19008094115086764597519821)
              ·
                refine ⟨7128035293157536724069933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19008094115086764597519821 7128035293157536724069933)
                ·
                  refine ⟨2673013234934076271526225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7128035293157536724069933 2673013234934076271526225)
                  ·
                    refine ⟨2004759926200557203644669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2673013234934076271526225 2004759926200557203644669)
                    ·
                      refine ⟨751784972325208951366751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2004759926200557203644669 751784972325208951366751)
                      ·
                        rfl

theorem cell23_1464096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_1464096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464096 prefixEnd_1464096 := by exact prefixLift 1464096
  have htrace : WordTrace (prefixWord ++ tailWord_1464096) baseStart_1464096 baseEnd_1464096 := by
    simpa [prefixWord, tailWord_1464096, baseEnd_1464096] using wordTrace_append hprefix tailTrace_1464096
  have hstable : (prefixWord ++ tailWord_1464096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464096).length < 2 ^ (prefixWord ++ tailWord_1464096).sum := by decide
  have hdescent : baseEnd_1464096 < baseStart_1464096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464110 : List Nat := [4, 1, 3, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1464110 : Nat := 118140960795 + 1464110 * 2 ^ 59
def prefixEnd_1464110 : Nat := 4983230072969 + 3 ^ 40 * 1464110 * 2
def baseEnd_1464110 : Nat := 751792161054371896591687

theorem tailTrace_1464110 : CollatzResearch.WordTrace tailWord_1464110 prefixEnd_1464110 751792161054371896591687 := by
  unfold tailWord_1464110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6675059840723374365700723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35600319150524663283737189 6675059840723374365700723)
  ·
    refine ⟨10012589761085061548551085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6675059840723374365700723 10012589761085061548551085)
    ·
      refine ⟨3754721160406898080706657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10012589761085061548551085 3754721160406898080706657)
      ·
        refine ⟨2816040870305173560529993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3754721160406898080706657 2816040870305173560529993)
        ·
          refine ⟨2112030652728880170397495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2816040870305173560529993 2112030652728880170397495)
          ·
            refine ⟨3168045979093320255596243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2112030652728880170397495 3168045979093320255596243)
            ·
              refine ⟨4752068968639980383394365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3168045979093320255596243 4752068968639980383394365)
              ·
                refine ⟨1782025863239992643772887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4752068968639980383394365 1782025863239992643772887)
                ·
                  refine ⟨2673038794859988965659331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782025863239992643772887 2673038794859988965659331)
                  ·
                    refine ⟨4009558192289983448488997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2673038794859988965659331 4009558192289983448488997)
                    ·
                      refine ⟨751792161054371896591687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4009558192289983448488997 751792161054371896591687)
                      ·
                        rfl

theorem cell23_1464110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1464110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464110 prefixEnd_1464110 := by exact prefixLift 1464110
  have htrace : WordTrace (prefixWord ++ tailWord_1464110) baseStart_1464110 baseEnd_1464110 := by
    simpa [prefixWord, tailWord_1464110, baseEnd_1464110] using wordTrace_append hprefix tailTrace_1464110
  have hstable : (prefixWord ++ tailWord_1464110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464110).length < 2 ^ (prefixWord ++ tailWord_1464110).sum := by decide
  have hdescent : baseEnd_1464110 < baseStart_1464110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464113 : List Nat := [1, 2, 2, 3, 2, 3, 1, 3, 1, 2, 3]
def baseStart_1464113 : Nat := 118140960795 + 1464113 * 2 ^ 59
def prefixEnd_1464113 : Nat := 4983230072969 + 3 ^ 40 * 1464113 * 2
def baseEnd_1464113 : Nat := 751793701496335384854173

theorem tailTrace_1464113 : CollatzResearch.WordTrace tailWord_1464113 prefixEnd_1464113 751793701496335384854173 := by
  unfold tailWord_1464113
  simp only [CollatzResearch.WordTrace]
  refine ⟨53400588144776126437964993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35600392096517417625309995 53400588144776126437964993)
  ·
    refine ⟨40050441108582094828473745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53400588144776126437964993 40050441108582094828473745)
    ·
      refine ⟨30037830831436571121355309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40050441108582094828473745 30037830831436571121355309)
      ·
        refine ⟨11264186561788714170508241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30037830831436571121355309 11264186561788714170508241)
        ·
          refine ⟨8448139921341535627881181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11264186561788714170508241 8448139921341535627881181)
          ·
            refine ⟨3168052470503075860455443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8448139921341535627881181 3168052470503075860455443)
            ·
              refine ⟨4752078705754613790683165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3168052470503075860455443 4752078705754613790683165)
              ·
                refine ⟨1782029514657980171506187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4752078705754613790683165 1782029514657980171506187)
                ·
                  refine ⟨2673044271986970257259281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782029514657980171506187 2673044271986970257259281)
                  ·
                    refine ⟨2004783203990227692944461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2673044271986970257259281 2004783203990227692944461)
                    ·
                      refine ⟨751793701496335384854173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2004783203990227692944461 751793701496335384854173)
                      ·
                        rfl

theorem cell23_1464113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_1464113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464113 prefixEnd_1464113 := by exact prefixLift 1464113
  have htrace : WordTrace (prefixWord ++ tailWord_1464113) baseStart_1464113 baseEnd_1464113 := by
    simpa [prefixWord, tailWord_1464113, baseEnd_1464113] using wordTrace_append hprefix tailTrace_1464113
  have hstable : (prefixWord ++ tailWord_1464113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464113).length < 2 ^ (prefixWord ++ tailWord_1464113).sum := by decide
  have hdescent : baseEnd_1464113 < baseStart_1464113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464116 : List Nat := [2, 5, 1, 1, 2, 2, 10]
def baseStart_1464116 : Nat := 118140960795 + 1464116 * 2 ^ 59
def prefixEnd_1464116 : Nat := 4983230072969 + 3 ^ 40 * 1464116 * 2
def baseEnd_1464116 : Nat := 9281422739978998433539

theorem tailTrace_1464116 : CollatzResearch.WordTrace tailWord_1464116 prefixEnd_1464116 9281422739978998433539 := by
  unfold tailWord_1464116
  simp only [CollatzResearch.WordTrace]
  refine ⟨26700348781882628975162101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35600465042510171966882801 26700348781882628975162101)
  ·
    refine ⟨2503157698301496466421447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26700348781882628975162101 2503157698301496466421447)
    ·
      refine ⟨3754736547452244699632171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2503157698301496466421447 3754736547452244699632171)
      ·
        refine ⟨5632104821178367049448257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3754736547452244699632171 5632104821178367049448257)
        ·
          refine ⟨4224078615883775287086193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5632104821178367049448257 4224078615883775287086193)
          ·
            refine ⟨3168058961912831465314645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4224078615883775287086193 3168058961912831465314645)
            ·
              refine ⟨9281422739978998433539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3168058961912831465314645 9281422739978998433539)
              ·
                rfl

theorem cell23_1464116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 10].length) (baseStart_1464116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464116 prefixEnd_1464116 := by exact prefixLift 1464116
  have htrace : WordTrace (prefixWord ++ tailWord_1464116) baseStart_1464116 baseEnd_1464116 := by
    simpa [prefixWord, tailWord_1464116, baseEnd_1464116] using wordTrace_append hprefix tailTrace_1464116
  have hstable : (prefixWord ++ tailWord_1464116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464116).length < 2 ^ (prefixWord ++ tailWord_1464116).sum := by decide
  have hdescent : baseEnd_1464116 < baseStart_1464116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464140 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 1, 2, 4]
def baseStart_1464140 : Nat := 118140960795 + 1464140 * 2 ^ 59
def prefixEnd_1464140 : Nat := 4983230072969 + 3 ^ 40 * 1464140 * 2
def baseEnd_1464140 : Nat := 751807565474006779216549

theorem tailTrace_1464140 : CollatzResearch.WordTrace tailWord_1464140 prefixEnd_1464140 751807565474006779216549 := by
  unfold tailWord_1464140
  simp only [CollatzResearch.WordTrace]
  refine ⟨26700786457839155024598937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35601048610452206699465249 26700786457839155024598937)
  ·
    refine ⟨20025589843379366268449203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26700786457839155024598937 20025589843379366268449203)
    ·
      refine ⟨30038384765069049402673805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20025589843379366268449203 30038384765069049402673805)
      ·
        refine ⟨11264394286900893526002677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30038384765069049402673805 11264394286900893526002677)
        ·
          refine ⟨1056036964396958768062751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11264394286900893526002677 1056036964396958768062751)
          ·
            refine ⟨1584055446595438152094127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056036964396958768062751 1584055446595438152094127)
            ·
              refine ⟨2376083169893157228141191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584055446595438152094127 2376083169893157228141191)
              ·
                refine ⟨3564124754839735842211787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2376083169893157228141191 3564124754839735842211787)
                ·
                  refine ⟨5346187132259603763317681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3564124754839735842211787 5346187132259603763317681)
                  ·
                    refine ⟨4009640349194702822488261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5346187132259603763317681 4009640349194702822488261)
                    ·
                      refine ⟨751807565474006779216549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4009640349194702822488261 751807565474006779216549)
                      ·
                        rfl

theorem cell23_1464140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_1464140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464140 prefixEnd_1464140 := by exact prefixLift 1464140
  have htrace : WordTrace (prefixWord ++ tailWord_1464140) baseStart_1464140 baseEnd_1464140 := by
    simpa [prefixWord, tailWord_1464140, baseEnd_1464140] using wordTrace_append hprefix tailTrace_1464140
  have hstable : (prefixWord ++ tailWord_1464140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464140).length < 2 ^ (prefixWord ++ tailWord_1464140).sum := by decide
  have hdescent : baseEnd_1464140 < baseStart_1464140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464196 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_1464196 : Nat := 118140960795 + 1464196 * 2 ^ 59
def prefixEnd_1464196 : Nat := 4983230072969 + 3 ^ 40 * 1464196 * 2
def baseEnd_1464196 : Nat := 751836320390658560116291

theorem tailTrace_1464196 : CollatzResearch.WordTrace tailWord_1464196 prefixEnd_1464196 751836320390658560116291 := by
  unfold tailWord_1464196
  simp only [CollatzResearch.WordTrace]
  refine ⟨26701807701737715806618221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35602410268983621075490961 26701807701737715806618221)
  ·
    refine ⟨10013177888151643427481833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26701807701737715806618221 10013177888151643427481833)
    ·
      refine ⟨7509883416113732570611375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10013177888151643427481833 7509883416113732570611375)
      ·
        refine ⟨11264825124170598855917063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7509883416113732570611375 11264825124170598855917063)
        ·
          refine ⟨16897237686255898283875595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11264825124170598855917063 16897237686255898283875595)
          ·
            refine ⟨25345856529383847425813393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16897237686255898283875595 25345856529383847425813393)
            ·
              refine ⟨19009392397037885569360045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25345856529383847425813393 19009392397037885569360045)
              ·
                refine ⟨7128522148889207088510017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19009392397037885569360045 7128522148889207088510017)
                ·
                  refine ⟨5346391611666905316382513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7128522148889207088510017 5346391611666905316382513)
                  ·
                    refine ⟨4009793708750178987286885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5346391611666905316382513 4009793708750178987286885)
                    ·
                      refine ⟨751836320390658560116291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4009793708750178987286885 751836320390658560116291)
                      ·
                        rfl

theorem cell23_1464196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_1464196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464196 prefixEnd_1464196 := by exact prefixLift 1464196
  have htrace : WordTrace (prefixWord ++ tailWord_1464196) baseStart_1464196 baseEnd_1464196 := by
    simpa [prefixWord, tailWord_1464196, baseEnd_1464196] using wordTrace_append hprefix tailTrace_1464196
  have hstable : (prefixWord ++ tailWord_1464196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464196).length < 2 ^ (prefixWord ++ tailWord_1464196).sum := by decide
  have hdescent : baseEnd_1464196 < baseStart_1464196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464256 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 4]
def baseStart_1464256 : Nat := 118140960795 + 1464256 * 2 ^ 59
def prefixEnd_1464256 : Nat := 4983230072969 + 3 ^ 40 * 1464256 * 2
def baseEnd_1464256 : Nat := 751867129229928325366015

theorem tailTrace_1464256 : CollatzResearch.WordTrace tailWord_1464256 prefixEnd_1464256 751867129229928325366015 := by
  unfold tailWord_1464256
  simp only [CollatzResearch.WordTrace]
  refine ⟨26702901891629030930210311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35603869188838707906947081 26702901891629030930210311)
  ·
    refine ⟨40054352837443546395315467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26702901891629030930210311 40054352837443546395315467)
    ·
      refine ⟨60081529256165319592973201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40054352837443546395315467 60081529256165319592973201)
      ·
        refine ⟨45061146942123989694729901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60081529256165319592973201 45061146942123989694729901)
        ·
          refine ⟨16897930103296496135523713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45061146942123989694729901 16897930103296496135523713)
          ·
            refine ⟨12673447577472372101642785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16897930103296496135523713 12673447577472372101642785)
            ·
              refine ⟨9505085683104279076232089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12673447577472372101642785 9505085683104279076232089)
              ·
                refine ⟨7128814262328209307174067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9505085683104279076232089 7128814262328209307174067)
                ·
                  refine ⟨10693221393492313960761101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7128814262328209307174067 10693221393492313960761101)
                  ·
                    refine ⟨4009958022559617735285413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10693221393492313960761101 4009958022559617735285413)
                    ·
                      refine ⟨751867129229928325366015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4009958022559617735285413 751867129229928325366015)
                      ·
                        rfl

theorem cell23_1464256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_1464256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464256 prefixEnd_1464256 := by exact prefixLift 1464256
  have htrace : WordTrace (prefixWord ++ tailWord_1464256) baseStart_1464256 baseEnd_1464256 := by
    simpa [prefixWord, tailWord_1464256, baseEnd_1464256] using wordTrace_append hprefix tailTrace_1464256
  have hstable : (prefixWord ++ tailWord_1464256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464256).length < 2 ^ (prefixWord ++ tailWord_1464256).sum := by decide
  have hdescent : baseEnd_1464256 < baseStart_1464256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464316 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_1464316 : Nat := 118140960795 + 1464316 * 2 ^ 59
def prefixEnd_1464316 : Nat := 4983230072969 + 3 ^ 40 * 1464316 * 2
def baseEnd_1464316 : Nat := 751897938069198090615739

theorem tailTrace_1464316 : CollatzResearch.WordTrace tailWord_1464316 prefixEnd_1464316 751897938069198090615739 := by
  unfold tailWord_1464316
  simp only [CollatzResearch.WordTrace]
  refine ⟨26703996081520346053802401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35605328108693794738403201 26703996081520346053802401)
  ·
    refine ⟨20027997061140259540351801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26703996081520346053802401 20027997061140259540351801)
    ·
      refine ⟨15020997795855194655263851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20027997061140259540351801 15020997795855194655263851)
      ·
        refine ⟨22531496693782791982895777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15020997795855194655263851 22531496693782791982895777)
        ·
          refine ⟨16898622520337093987171833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22531496693782791982895777 16898622520337093987171833)
          ·
            refine ⟨12673966890252820490378875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16898622520337093987171833 12673966890252820490378875)
            ·
              refine ⟨19010950335379230735568313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12673966890252820490378875 19010950335379230735568313)
              ·
                refine ⟨14258212751534423051676235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19010950335379230735568313 14258212751534423051676235)
                ·
                  refine ⟨21387319127301634577514353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14258212751534423051676235 21387319127301634577514353)
                  ·
                    refine ⟨16040489345476225933135765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21387319127301634577514353 16040489345476225933135765)
                    ·
                      refine ⟨751897938069198090615739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16040489345476225933135765 751897938069198090615739)
                      ·
                        rfl

theorem cell23_1464316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_1464316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464316 prefixEnd_1464316 := by exact prefixLift 1464316
  have htrace : WordTrace (prefixWord ++ tailWord_1464316) baseStart_1464316 baseEnd_1464316 := by
    simpa [prefixWord, tailWord_1464316, baseEnd_1464316] using wordTrace_append hprefix tailTrace_1464316
  have hstable : (prefixWord ++ tailWord_1464316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464316).length < 2 ^ (prefixWord ++ tailWord_1464316).sum := by decide
  have hdescent : baseEnd_1464316 < baseStart_1464316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464357 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 3, 1, 3]
def baseStart_1464357 : Nat := 118140960795 + 1464357 * 2 ^ 59
def prefixEnd_1464357 : Nat := 4983230072969 + 3 ^ 40 * 1464357 * 2
def baseEnd_1464357 : Nat := 751918990776032430203051

theorem tailTrace_1464357 : CollatzResearch.WordTrace tailWord_1464357 prefixEnd_1464357 751918990776032430203051 := by
  unfold tailWord_1464357
  simp only [CollatzResearch.WordTrace]
  refine ⟨53409487555892156109847325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35606325037261437406564883 53409487555892156109847325)
  ·
    refine ⟨20028557833459558541192747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53409487555892156109847325 20028557833459558541192747)
    ·
      refine ⟨30042836750189337811789121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20028557833459558541192747 30042836750189337811789121)
      ·
        refine ⟨22532127562642003358841841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30042836750189337811789121 22532127562642003358841841)
        ·
          refine ⟨16899095671981502519131381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22532127562642003358841841 16899095671981502519131381)
          ·
            refine ⟨1584290219248265861168567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16899095671981502519131381 1584290219248265861168567)
            ·
              refine ⟨2376435328872398791752851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584290219248265861168567 2376435328872398791752851)
              ·
                refine ⟨3564652993308598187629277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2376435328872398791752851 3564652993308598187629277)
                ·
                  refine ⟨1336744872490724320360979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3564652993308598187629277 1336744872490724320360979)
                  ·
                    refine ⟨2005117308736086480541469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1336744872490724320360979 2005117308736086480541469)
                    ·
                      refine ⟨751918990776032430203051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2005117308736086480541469 751918990776032430203051)
                      ·
                        rfl

theorem cell23_1464357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_1464357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464357 prefixEnd_1464357 := by exact prefixLift 1464357
  have htrace : WordTrace (prefixWord ++ tailWord_1464357) baseStart_1464357 baseEnd_1464357 := by
    simpa [prefixWord, tailWord_1464357, baseEnd_1464357] using wordTrace_append hprefix tailTrace_1464357
  have hstable : (prefixWord ++ tailWord_1464357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464357).length < 2 ^ (prefixWord ++ tailWord_1464357).sum := by decide
  have hdescent : baseEnd_1464357 < baseStart_1464357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464363 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 2, 6, 2]
def baseStart_1464363 : Nat := 118140960795 + 1464363 * 2 ^ 59
def prefixEnd_1464363 : Nat := 4983230072969 + 3 ^ 40 * 1464363 * 2
def baseEnd_1464363 : Nat := 751922071659959406728023

theorem tailTrace_1464363 : CollatzResearch.WordTrace tailWord_1464363 prefixEnd_1464363 751922071659959406728023 := by
  unfold tailWord_1464363
  simp only [CollatzResearch.WordTrace]
  refine ⟨53409706393870419134565743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35606470929246946089710495 53409706393870419134565743)
  ·
    refine ⟨80114559590805628701848615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53409706393870419134565743 80114559590805628701848615)
    ·
      refine ⟨120171839386208443052772923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80114559590805628701848615 120171839386208443052772923)
      ·
        refine ⟨180257759079312664579159385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120171839386208443052772923 180257759079312664579159385)
        ·
          refine ⟨135193319309484498434369539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180257759079312664579159385 135193319309484498434369539)
          ·
            refine ⟨202789978964226747651554309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135193319309484498434369539 202789978964226747651554309)
            ·
              refine ⟨38023121055792515184666433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202789978964226747651554309 38023121055792515184666433)
              ·
                refine ⟨28517340791844386388499825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38023121055792515184666433 28517340791844386388499825)
                ·
                  refine ⟨21388005593883289791374869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28517340791844386388499825 21388005593883289791374869)
                  ·
                    refine ⟨1002562762213279208970697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21388005593883289791374869 1002562762213279208970697)
                    ·
                      refine ⟨751922071659959406728023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1002562762213279208970697 751922071659959406728023)
                      ·
                        rfl

theorem cell23_1464363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 6, 2].length) (baseStart_1464363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464363 prefixEnd_1464363 := by exact prefixLift 1464363
  have htrace : WordTrace (prefixWord ++ tailWord_1464363) baseStart_1464363 baseEnd_1464363 := by
    simpa [prefixWord, tailWord_1464363, baseEnd_1464363] using wordTrace_append hprefix tailTrace_1464363
  have hstable : (prefixWord ++ tailWord_1464363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464363).length < 2 ^ (prefixWord ++ tailWord_1464363).sum := by decide
  have hdescent : baseEnd_1464363 < baseStart_1464363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464377 : List Nat := [1, 2, 1, 5, 3, 2, 1, 2, 1, 5]
def baseStart_1464377 : Nat := 118140960795 + 1464377 * 2 ^ 59
def prefixEnd_1464377 : Nat := 4983230072969 + 3 ^ 40 * 1464377 * 2
def baseEnd_1464377 : Nat := 250643086796374117317653

theorem tailTrace_1464377 : CollatzResearch.WordTrace tailWord_1464377 prefixEnd_1464377 250643086796374117317653 := by
  unfold tailWord_1464377
  simp only [CollatzResearch.WordTrace]
  refine ⟨53410217015819699525575385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35606811343879799683716923 53410217015819699525575385)
  ·
    refine ⟨40057662761864774644181539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53410217015819699525575385 40057662761864774644181539)
    ·
      refine ⟨60086494142797161966272309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40057662761864774644181539 60086494142797161966272309)
      ·
        refine ⟨5633108825887233934338029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60086494142797161966272309 5633108825887233934338029)
        ·
          refine ⟨2112415809707712725376761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5633108825887233934338029 2112415809707712725376761)
          ·
            refine ⟨1584311857280784544032571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2112415809707712725376761 1584311857280784544032571)
            ·
              refine ⟨2376467785921176816048857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584311857280784544032571 2376467785921176816048857)
              ·
                refine ⟨1782350839440882612036643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2376467785921176816048857 1782350839440882612036643)
                ·
                  refine ⟨2673526259161323918054965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782350839440882612036643 2673526259161323918054965)
                  ·
                    refine ⟨250643086796374117317653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2673526259161323918054965 250643086796374117317653)
                    ·
                      rfl

theorem cell23_1464377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 5].length) (baseStart_1464377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464377 prefixEnd_1464377 := by exact prefixLift 1464377
  have htrace : WordTrace (prefixWord ++ tailWord_1464377) baseStart_1464377 baseEnd_1464377 := by
    simpa [prefixWord, tailWord_1464377, baseEnd_1464377] using wordTrace_append hprefix tailTrace_1464377
  have hstable : (prefixWord ++ tailWord_1464377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464377).length < 2 ^ (prefixWord ++ tailWord_1464377).sum := by decide
  have hdescent : baseEnd_1464377 < baseStart_1464377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464393 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 1, 2, 4]
def baseStart_1464393 : Nat := 118140960795 + 1464393 * 2 ^ 59
def prefixEnd_1464393 : Nat := 4983230072969 + 3 ^ 40 * 1464393 * 2
def baseEnd_1464393 : Nat := 751937476079594289352885

theorem tailTrace_1464393 : CollatzResearch.WordTrace tailWord_1464393 prefixEnd_1464393 751937476079594289352885 := by
  unfold tailWord_1464393
  simp only [CollatzResearch.WordTrace]
  refine ⟨53410800583761734258157833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35607200389174489505438555 53410800583761734258157833)
  ·
    refine ⟨40058100437821300693618375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53410800583761734258157833 40058100437821300693618375)
    ·
      refine ⟨60087150656731951040427563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40058100437821300693618375 60087150656731951040427563)
      ·
        refine ⟨90130725985097926560641345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60087150656731951040427563 90130725985097926560641345)
        ·
          refine ⟨67598044488823444920481009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90130725985097926560641345 67598044488823444920481009)
          ·
            refine ⟨50698533366617583690360757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67598044488823444920481009 50698533366617583690360757)
            ·
              refine ⟨4752987503120398470971321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50698533366617583690360757 4752987503120398470971321)
              ·
                refine ⟨3564740627340298853228491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4752987503120398470971321 3564740627340298853228491)
                ·
                  refine ⟨5347110941010448279842737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3564740627340298853228491 5347110941010448279842737)
                  ·
                    refine ⟨4010333205757836209882053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5347110941010448279842737 4010333205757836209882053)
                    ·
                      refine ⟨751937476079594289352885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4010333205757836209882053 751937476079594289352885)
                      ·
                        rfl

theorem cell23_1464393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_1464393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464393 prefixEnd_1464393 := by exact prefixLift 1464393
  have htrace : WordTrace (prefixWord ++ tailWord_1464393) baseStart_1464393 baseEnd_1464393 := by
    simpa [prefixWord, tailWord_1464393, baseEnd_1464393] using wordTrace_append hprefix tailTrace_1464393
  have hstable : (prefixWord ++ tailWord_1464393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464393).length < 2 ^ (prefixWord ++ tailWord_1464393).sum := by decide
  have hdescent : baseEnd_1464393 < baseStart_1464393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464457 : List Nat := [1, 2, 1, 1, 4, 2, 3, 3, 1, 3, 2]
def baseStart_1464457 : Nat := 118140960795 + 1464457 * 2 ^ 59
def prefixEnd_1464457 : Nat := 4983230072969 + 3 ^ 40 * 1464457 * 2
def baseEnd_1464457 : Nat := 751970338841482038952591

theorem tailTrace_1464457 : CollatzResearch.WordTrace tailWord_1464457 prefixEnd_1464457 751970338841482038952591 := by
  unfold tailWord_1464457
  simp only [CollatzResearch.WordTrace]
  refine ⟨53413134855529873188487625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35608756570353248792325083 53413134855529873188487625)
  ·
    refine ⟨40059851141647404891365719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53413134855529873188487625 40059851141647404891365719)
    ·
      refine ⟨60089776712471107337048579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40059851141647404891365719 60089776712471107337048579)
      ·
        refine ⟨90134665068706661005572869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60089776712471107337048579 90134665068706661005572869)
        ·
          refine ⟨16900249700382498938544913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90134665068706661005572869 16900249700382498938544913)
          ·
            refine ⟨12675187275286874203908685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16900249700382498938544913 12675187275286874203908685)
            ·
              refine ⟨4753195228232577826465757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12675187275286874203908685 4753195228232577826465757)
              ·
                refine ⟨1782448210587216684924659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4753195228232577826465757 1782448210587216684924659)
                ·
                  refine ⟨2673672315880825027386989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782448210587216684924659 2673672315880825027386989)
                  ·
                    refine ⟨1002627118455309385270121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2673672315880825027386989 1002627118455309385270121)
                    ·
                      refine ⟨751970338841482038952591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1002627118455309385270121 751970338841482038952591)
                      ·
                        rfl

theorem cell23_1464457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 3, 2].length) (baseStart_1464457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464457 prefixEnd_1464457 := by exact prefixLift 1464457
  have htrace : WordTrace (prefixWord ++ tailWord_1464457) baseStart_1464457 baseEnd_1464457 := by
    simpa [prefixWord, tailWord_1464457, baseEnd_1464457] using wordTrace_append hprefix tailTrace_1464457
  have hstable : (prefixWord ++ tailWord_1464457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464457).length < 2 ^ (prefixWord ++ tailWord_1464457).sum := by decide
  have hdescent : baseEnd_1464457 < baseStart_1464457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464473 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 1, 6, 3]
def baseStart_1464473 : Nat := 118140960795 + 1464473 * 2 ^ 59
def prefixEnd_1464473 : Nat := 4983230072969 + 3 ^ 40 * 1464473 * 2
def baseEnd_1464473 : Nat := 751978554531953976352517

theorem tailTrace_1464473 : CollatzResearch.WordTrace tailWord_1464473 prefixEnd_1464473 751978554531953976352517 := by
  unfold tailWord_1464473
  simp only [CollatzResearch.WordTrace]
  refine ⟨53413718423471907921070073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35609145615647938614046715 53413718423471907921070073)
  ·
    refine ⟨40060288817603930940802555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53413718423471907921070073 40060288817603930940802555)
    ·
      refine ⟨60090433226405896411203833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40060288817603930940802555 60090433226405896411203833)
      ·
        refine ⟨45067824919804422308402875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60090433226405896411203833 45067824919804422308402875)
        ·
          refine ⟨67601737379706633462604313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45067824919804422308402875 67601737379706633462604313)
          ·
            refine ⟨50701303034779975096953235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67601737379706633462604313 50701303034779975096953235)
            ·
              refine ⟨76051954552169962645429853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50701303034779975096953235 76051954552169962645429853)
              ·
                refine ⟨28519482957063735992036195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76051954552169962645429853 28519482957063735992036195)
                ·
                  refine ⟨42779224435595603988054293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28519482957063735992036195 42779224435595603988054293)
                  ·
                    refine ⟨2005276145418543936940045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42779224435595603988054293 2005276145418543936940045)
                    ·
                      refine ⟨751978554531953976352517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2005276145418543936940045 751978554531953976352517)
                      ·
                        rfl

theorem cell23_1464473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_1464473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464473 prefixEnd_1464473 := by exact prefixLift 1464473
  have htrace : WordTrace (prefixWord ++ tailWord_1464473) baseStart_1464473 baseEnd_1464473 := by
    simpa [prefixWord, tailWord_1464473, baseEnd_1464473] using wordTrace_append hprefix tailTrace_1464473
  have hstable : (prefixWord ++ tailWord_1464473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464473).length < 2 ^ (prefixWord ++ tailWord_1464473).sum := by decide
  have hdescent : baseEnd_1464473 < baseStart_1464473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464527 : List Nat := [1, 1, 2, 1, 1, 3, 7, 2, 5]
def baseStart_1464527 : Nat := 118140960795 + 1464527 * 2 ^ 59
def prefixEnd_1464527 : Nat := 4983230072969 + 3 ^ 40 * 1464527 * 2
def baseEnd_1464527 : Nat := 83556253609699640564141

theorem tailTrace_1464527 : CollatzResearch.WordTrace tailWord_1464527 prefixEnd_1464527 83556253609699640564141 := by
  unfold tailWord_1464527
  simp only [CollatzResearch.WordTrace]
  refine ⟨53415687965276275143535835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35610458643517516762357223 53415687965276275143535835)
  ·
    refine ⟨80123531947914412715303753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53415687965276275143535835 80123531947914412715303753)
    ·
      refine ⟨60092648960935809536477815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80123531947914412715303753 60092648960935809536477815)
      ·
        refine ⟨90138973441403714304716723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60092648960935809536477815 90138973441403714304716723)
        ·
          refine ⟨135208460162105571457075085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90138973441403714304716723 135208460162105571457075085)
          ·
            refine ⟨50703172560789589296403157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135208460162105571457075085 50703172560789589296403157)
            ·
              refine ⟨1188355606893505999134449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 50703172560789589296403157 1188355606893505999134449)
              ·
                refine ⟨891266705170129499350837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1188355606893505999134449 891266705170129499350837)
                ·
                  refine ⟨83556253609699640564141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 891266705170129499350837 83556253609699640564141)
                  ·
                    rfl

theorem cell23_1464527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 5].length) (baseStart_1464527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464527 prefixEnd_1464527 := by exact prefixLift 1464527
  have htrace : WordTrace (prefixWord ++ tailWord_1464527) baseStart_1464527 baseEnd_1464527 := by
    simpa [prefixWord, tailWord_1464527, baseEnd_1464527] using wordTrace_append hprefix tailTrace_1464527
  have hstable : (prefixWord ++ tailWord_1464527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464527).length < 2 ^ (prefixWord ++ tailWord_1464527).sum := by decide
  have hdescent : baseEnd_1464527 < baseStart_1464527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464577 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 2, 4, 2]
def baseStart_1464577 : Nat := 118140960795 + 1464577 * 2 ^ 59
def prefixEnd_1464577 : Nat := 4983230072969 + 3 ^ 40 * 1464577 * 2
def baseEnd_1464577 : Nat := 752031956520021569452039

theorem tailTrace_1464577 : CollatzResearch.WordTrace tailWord_1464577 prefixEnd_1464577 752031956520021569452039 := by
  unfold tailWord_1464577
  simp only [CollatzResearch.WordTrace]
  refine ⟨53417511615095133682855985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35611674410063422455237323 53417511615095133682855985)
  ·
    refine ⟨40063133711321350262141989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53417511615095133682855985 40063133711321350262141989)
    ·
      refine ⟨7511837570872753174151623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40063133711321350262141989 7511837570872753174151623)
      ·
        refine ⟨11267756356309129761227435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7511837570872753174151623 11267756356309129761227435)
        ·
          refine ⟨16901634534463694641841153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11267756356309129761227435 16901634534463694641841153)
          ·
            refine ⟨12676225900847770981380865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16901634534463694641841153 12676225900847770981380865)
            ·
              refine ⟨9507169425635828236035649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12676225900847770981380865 9507169425635828236035649)
              ·
                refine ⟨7130377069226871177026737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9507169425635828236035649 7130377069226871177026737)
                ·
                  refine ⟨5347782801920153382770053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7130377069226871177026737 5347782801920153382770053)
                  ·
                    refine ⟨1002709275360028759269385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5347782801920153382770053 1002709275360028759269385)
                    ·
                      refine ⟨752031956520021569452039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1002709275360028759269385 752031956520021569452039)
                      ·
                        rfl

theorem cell23_1464577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_1464577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464577 prefixEnd_1464577 := by exact prefixLift 1464577
  have htrace : WordTrace (prefixWord ++ tailWord_1464577) baseStart_1464577 baseEnd_1464577 := by
    simpa [prefixWord, tailWord_1464577, baseEnd_1464577] using wordTrace_append hprefix tailTrace_1464577
  have hstable : (prefixWord ++ tailWord_1464577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464577).length < 2 ^ (prefixWord ++ tailWord_1464577).sum := by decide
  have hdescent : baseEnd_1464577 < baseStart_1464577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464600 : List Nat := [2, 1, 2, 3, 1, 2, 1, 5, 6]
def baseStart_1464600 : Nat := 118140960795 + 1464600 * 2 ^ 59
def prefixEnd_1464600 : Nat := 4983230072969 + 3 ^ 40 * 1464600 * 2
def baseEnd_1464600 : Nat := 83560418508341664384937

theorem tailTrace_1464600 : CollatzResearch.WordTrace tailWord_1464600 prefixEnd_1464600 83560418508341664384937 := by
  unfold tailWord_1464600
  simp only [CollatzResearch.WordTrace]
  refine ⟨26709175247005904305471627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35612233662674539073962169 26709175247005904305471627)
  ·
    refine ⟨40063762870508856458207441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26709175247005904305471627 40063762870508856458207441)
    ·
      refine ⟨30047822152881642343655581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40063762870508856458207441 30047822152881642343655581)
      ·
        refine ⟨11267933307330615878870843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30047822152881642343655581 11267933307330615878870843)
        ·
          refine ⟨16901899960995923818306265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11267933307330615878870843 16901899960995923818306265)
          ·
            refine ⟨12676424970746942863729699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16901899960995923818306265 12676424970746942863729699)
            ·
              refine ⟨19014637456120414295594549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12676424970746942863729699 19014637456120414295594549)
              ·
                refine ⟨1782622261511288840211989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19014637456120414295594549 1782622261511288840211989)
                ·
                  refine ⟨83560418508341664384937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1782622261511288840211989 83560418508341664384937)
                  ·
                    rfl

theorem cell23_1464600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 6].length) (baseStart_1464600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464600 prefixEnd_1464600 := by exact prefixLift 1464600
  have htrace : WordTrace (prefixWord ++ tailWord_1464600) baseStart_1464600 baseEnd_1464600 := by
    simpa [prefixWord, tailWord_1464600, baseEnd_1464600] using wordTrace_append hprefix tailTrace_1464600
  have hstable : (prefixWord ++ tailWord_1464600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464600).length < 2 ^ (prefixWord ++ tailWord_1464600).sum := by decide
  have hdescent : baseEnd_1464600 < baseStart_1464600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464627 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 5, 1, 3]
def baseStart_1464627 : Nat := 118140960795 + 1464627 * 2 ^ 59
def prefixEnd_1464627 : Nat := 4983230072969 + 3 ^ 40 * 1464627 * 2
def baseEnd_1464627 : Nat := 752057630552746373826809

theorem tailTrace_1464627 : CollatzResearch.WordTrace tailWord_1464627 prefixEnd_1464627 752057630552746373826809 := by
  unfold tailWord_1464627
  simp only [CollatzResearch.WordTrace]
  refine ⟨53419335264913992222176135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35612890176609328148117423 53419335264913992222176135)
  ·
    refine ⟨80129002897370988333264203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53419335264913992222176135 80129002897370988333264203)
    ·
      refine ⟨120193504346056482499896305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80129002897370988333264203 120193504346056482499896305)
      ·
        refine ⟨90145128259542361874922229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120193504346056482499896305 90145128259542361874922229)
        ·
          refine ⟨8451105774332096425773959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90145128259542361874922229 8451105774332096425773959)
          ·
            refine ⟨12676658661498144638660939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8451105774332096425773959 12676658661498144638660939)
            ·
              refine ⟨19014987992247216957991409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12676658661498144638660939 19014987992247216957991409)
              ·
                refine ⟨14261240994185412718493557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19014987992247216957991409 14261240994185412718493557)
                ·
                  refine ⟨1336991343204882442358771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14261240994185412718493557 1336991343204882442358771)
                  ·
                    refine ⟨2005487014807323663538157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1336991343204882442358771 2005487014807323663538157)
                    ·
                      refine ⟨752057630552746373826809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2005487014807323663538157 752057630552746373826809)
                      ·
                        rfl

theorem cell23_1464627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 1, 3].length) (baseStart_1464627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464627 prefixEnd_1464627 := by exact prefixLift 1464627
  have htrace : WordTrace (prefixWord ++ tailWord_1464627) baseStart_1464627 baseEnd_1464627 := by
    simpa [prefixWord, tailWord_1464627, baseEnd_1464627] using wordTrace_append hprefix tailTrace_1464627
  have hstable : (prefixWord ++ tailWord_1464627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464627).length < 2 ^ (prefixWord ++ tailWord_1464627).sum := by decide
  have hdescent : baseEnd_1464627 < baseStart_1464627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464677 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 4, 4]
def baseStart_1464677 : Nat := 118140960795 + 1464677 * 2 ^ 59
def prefixEnd_1464677 : Nat := 4983230072969 + 3 ^ 40 * 1464677 * 2
def baseEnd_1464677 : Nat := 250694434861823726067193

theorem tailTrace_1464677 : CollatzResearch.WordTrace tailWord_1464677 prefixEnd_1464677 250694434861823726067193 := by
  unfold tailWord_1464677
  simp only [CollatzResearch.WordTrace]
  refine ⟨53421158914732850761496285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35614105943155233840997523 53421158914732850761496285)
  ·
    refine ⟨20032934593024819035561107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53421158914732850761496285 20032934593024819035561107)
    ·
      refine ⟨30049401889537228553341661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20032934593024819035561107 30049401889537228553341661)
      ·
        refine ⟨11268525708576460707503123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30049401889537228553341661 11268525708576460707503123)
        ·
          refine ⟨16902788562864691061254685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11268525708576460707503123 16902788562864691061254685)
          ·
            refine ⟨6338545711074259147970507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16902788562864691061254685 6338545711074259147970507)
            ·
              refine ⟨9507818566611388721955761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6338545711074259147970507 9507818566611388721955761)
              ·
                refine ⟨7130863924958541541466821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9507818566611388721955761 7130863924958541541466821)
                ·
                  refine ⟨1337036985929726539025029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7130863924958541541466821 1337036985929726539025029)
                  ·
                    refine ⟨250694434861823726067193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1337036985929726539025029 250694434861823726067193)
                    ·
                      rfl

theorem cell23_1464677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_1464677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464677 prefixEnd_1464677 := by exact prefixLift 1464677
  have htrace : WordTrace (prefixWord ++ tailWord_1464677) baseStart_1464677 baseEnd_1464677 := by
    simpa [prefixWord, tailWord_1464677, baseEnd_1464677] using wordTrace_append hprefix tailTrace_1464677
  have hstable : (prefixWord ++ tailWord_1464677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464677).length < 2 ^ (prefixWord ++ tailWord_1464677).sum := by decide
  have hdescent : baseEnd_1464677 < baseStart_1464677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464690 : List Nat := [3, 2, 1, 2, 1, 3, 11]
def baseStart_1464690 : Nat := 118140960795 + 1464690 * 2 ^ 59
def prefixEnd_1464690 : Nat := 4983230072969 + 3 ^ 40 * 1464690 * 2
def baseEnd_1464690 : Nat := 9285061479431847251099

theorem tailTrace_1464690 : CollatzResearch.WordTrace tailWord_1464690 prefixEnd_1464690 9285061479431847251099 := by
  unfold tailWord_1464690
  simp only [CollatzResearch.WordTrace]
  refine ⟨13355408265921438495429881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35614422042457169321146349 13355408265921438495429881)
  ·
    refine ⟨10016556199441078871572411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13355408265921438495429881 10016556199441078871572411)
    ·
      refine ⟨15024834299161618307358617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10016556199441078871572411 15024834299161618307358617)
      ·
        refine ⟨11268625724371213730518963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15024834299161618307358617 11268625724371213730518963)
        ·
          refine ⟨16902938586556820595778445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11268625724371213730518963 16902938586556820595778445)
          ·
            refine ⟨6338601969958807723416917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16902938586556820595778445 6338601969958807723416917)
            ·
              refine ⟨9285061479431847251099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6338601969958807723416917 9285061479431847251099)
              ·
                rfl

theorem cell23_1464690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 11].length) (baseStart_1464690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464690 prefixEnd_1464690 := by exact prefixLift 1464690
  have htrace : WordTrace (prefixWord ++ tailWord_1464690) baseStart_1464690 baseEnd_1464690 := by
    simpa [prefixWord, tailWord_1464690, baseEnd_1464690] using wordTrace_append hprefix tailTrace_1464690
  have hstable : (prefixWord ++ tailWord_1464690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464690).length < 2 ^ (prefixWord ++ tailWord_1464690).sum := by decide
  have hdescent : baseEnd_1464690 < baseStart_1464690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464701 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 3, 2, 2]
def baseStart_1464701 : Nat := 118140960795 + 1464701 * 2 ^ 59
def prefixEnd_1464701 : Nat := 4983230072969 + 3 ^ 40 * 1464701 * 2
def baseEnd_1464701 : Nat := 752095628121179084301469

theorem tailTrace_1464701 : CollatzResearch.WordTrace tailWord_1464701 prefixEnd_1464701 752095628121179084301469 := by
  unfold tailWord_1464701
  simp only [CollatzResearch.WordTrace]
  refine ⟨53422034266645902860369957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35614689511097268573579971 53422034266645902860369957)
  ·
    refine ⟨10016631424996106786319367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53422034266645902860369957 10016631424996106786319367)
    ·
      refine ⟨15024947137494160179479051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10016631424996106786319367 15024947137494160179479051)
      ·
        refine ⟨22537420706241240269218577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15024947137494160179479051 22537420706241240269218577)
        ·
          refine ⟨16903065529680930201913933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22537420706241240269218577 16903065529680930201913933)
          ·
            refine ⟨6338649573630348825717725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16903065529680930201913933 6338649573630348825717725)
            ·
              refine ⟨2376993590111380809644147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6338649573630348825717725 2376993590111380809644147)
              ·
                refine ⟨3565490385167071214466221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2376993590111380809644147 3565490385167071214466221)
                ·
                  refine ⟨1337058894437651705424833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3565490385167071214466221 1337058894437651705424833)
                  ·
                    refine ⟨1002794170828238779068625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1337058894437651705424833 1002794170828238779068625)
                    ·
                      refine ⟨752095628121179084301469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1002794170828238779068625 752095628121179084301469)
                      ·
                        rfl

theorem cell23_1464701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_1464701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464701 prefixEnd_1464701 := by exact prefixLift 1464701
  have htrace : WordTrace (prefixWord ++ tailWord_1464701) baseStart_1464701 baseEnd_1464701 := by
    simpa [prefixWord, tailWord_1464701, baseEnd_1464701] using wordTrace_append hprefix tailTrace_1464701
  have hstable : (prefixWord ++ tailWord_1464701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464701).length < 2 ^ (prefixWord ++ tailWord_1464701).sum := by decide
  have hdescent : baseEnd_1464701 < baseStart_1464701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464707 : List Nat := [1, 1, 1, 3, 6, 1, 2, 8]
def baseStart_1464707 : Nat := 118140960795 + 1464707 * 2 ^ 59
def prefixEnd_1464707 : Nat := 4983230072969 + 3 ^ 40 * 1464707 * 2
def baseEnd_1464707 : Nat := 27855507740929854104683

theorem tailTrace_1464707 : CollatzResearch.WordTrace tailWord_1464707 prefixEnd_1464707 27855507740929854104683 := by
  unfold tailWord_1464707
  simp only [CollatzResearch.WordTrace]
  refine ⟨53422253104624165885088375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35614835403082777256725583 53422253104624165885088375)
  ·
    refine ⟨80133379656936248827632563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53422253104624165885088375 80133379656936248827632563)
    ·
      refine ⟨120200069485404373241448845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80133379656936248827632563 120200069485404373241448845)
      ·
        refine ⟨45075026057026639965543317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120200069485404373241448845 45075026057026639965543317)
        ·
          refine ⟨2112891846423123748384843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45075026057026639965543317 2112891846423123748384843)
          ·
            refine ⟨3169337769634685622577265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2112891846423123748384843 3169337769634685622577265)
            ·
              refine ⟨2377003327226014216932949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3169337769634685622577265 2377003327226014216932949)
              ·
                refine ⟨27855507740929854104683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2377003327226014216932949 27855507740929854104683)
                ·
                  rfl

theorem cell23_1464707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 8].length) (baseStart_1464707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464707 prefixEnd_1464707 := by exact prefixLift 1464707
  have htrace : WordTrace (prefixWord ++ tailWord_1464707) baseStart_1464707 baseEnd_1464707 := by
    simpa [prefixWord, tailWord_1464707, baseEnd_1464707] using wordTrace_append hprefix tailTrace_1464707
  have hstable : (prefixWord ++ tailWord_1464707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464707).length < 2 ^ (prefixWord ++ tailWord_1464707).sum := by decide
  have hdescent : baseEnd_1464707 < baseStart_1464707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464746 : List Nat := [3, 1, 6, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_1464746 : Nat := 118140960795 + 1464746 * 2 ^ 59
def prefixEnd_1464746 : Nat := 4983230072969 + 3 ^ 40 * 1464746 * 2
def baseEnd_1464746 : Nat := 752118734750631408238763

theorem tailTrace_1464746 : CollatzResearch.WordTrace tailWord_1464746 prefixEnd_1464746 752118734750631408238763 := by
  unfold tailWord_1464746
  simp only [CollatzResearch.WordTrace]
  refine ⟨13355918887870718886439523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35615783700988583697172061 13355918887870718886439523)
  ·
    refine ⟨20033878331806078329659285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13355918887870718886439523 20033878331806078329659285)
    ·
      refine ⟨939088046803409921702779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20033878331806078329659285 939088046803409921702779)
      ·
        refine ⟨1408632070205114882554169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 939088046803409921702779 1408632070205114882554169)
        ·
          refine ⟨1056474052653836161915627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1408632070205114882554169 1056474052653836161915627)
          ·
            refine ⟨1584711078980754242873441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056474052653836161915627 1584711078980754242873441)
            ·
              refine ⟨1188533309235565682155081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1584711078980754242873441 1188533309235565682155081)
              ·
                refine ⟨891399981926674261616311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1188533309235565682155081 891399981926674261616311)
                ·
                  refine ⟨1337099972890011392424467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 891399981926674261616311 1337099972890011392424467)
                  ·
                    refine ⟨2005649959335017088636701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1337099972890011392424467 2005649959335017088636701)
                    ·
                      refine ⟨752118734750631408238763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2005649959335017088636701 752118734750631408238763)
                      ·
                        rfl

theorem cell23_1464746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_1464746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464746 prefixEnd_1464746 := by exact prefixLift 1464746
  have htrace : WordTrace (prefixWord ++ tailWord_1464746) baseStart_1464746 baseEnd_1464746 := by
    simpa [prefixWord, tailWord_1464746, baseEnd_1464746] using wordTrace_append hprefix tailTrace_1464746
  have hstable : (prefixWord ++ tailWord_1464746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464746).length < 2 ^ (prefixWord ++ tailWord_1464746).sum := by decide
  have hdescent : baseEnd_1464746 < baseStart_1464746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464797 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 9]
def baseStart_1464797 : Nat := 118140960795 + 1464797 * 2 ^ 59
def prefixEnd_1464797 : Nat := 4983230072969 + 3 ^ 40 * 1464797 * 2
def baseEnd_1464797 : Nat := 83571658029334523189003

theorem tailTrace_1464797 : CollatzResearch.WordTrace tailWord_1464797 prefixEnd_1464797 83571658029334523189003 := by
  unfold tailWord_1464797
  simp only [CollatzResearch.WordTrace]
  refine ⟨53425535674298111255864645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35617023782865407503909763 53425535674298111255864645)
  ·
    refine ⟨10017287938930895860474621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53425535674298111255864645 10017287938930895860474621)
    ·
      refine ⟨3756482977099085947677983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10017287938930895860474621 3756482977099085947677983)
      ·
        refine ⟨5634724465648628921516975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3756482977099085947677983 5634724465648628921516975)
        ·
          refine ⟨8452086698472943382275463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5634724465648628921516975 8452086698472943382275463)
          ·
            refine ⟨12678130047709415073413195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8452086698472943382275463 12678130047709415073413195)
            ·
              refine ⟨19017195071564122610119793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12678130047709415073413195 19017195071564122610119793)
              ·
                refine ⟨14262896303673091957589845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19017195071564122610119793 14262896303673091957589845)
                ·
                  refine ⟨83571658029334523189003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14262896303673091957589845 83571658029334523189003)
                  ·
                    rfl

theorem cell23_1464797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_1464797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464797 prefixEnd_1464797 := by exact prefixLift 1464797
  have htrace : WordTrace (prefixWord ++ tailWord_1464797) baseStart_1464797 baseEnd_1464797 := by
    simpa [prefixWord, tailWord_1464797, baseEnd_1464797] using wordTrace_append hprefix tailTrace_1464797
  have hstable : (prefixWord ++ tailWord_1464797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464797).length < 2 ^ (prefixWord ++ tailWord_1464797).sum := by decide
  have hdescent : baseEnd_1464797 < baseStart_1464797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464802 : List Nat := [3, 3, 3, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1464802 : Nat := 118140960795 + 1464802 * 2 ^ 59
def prefixEnd_1464802 : Nat := 4983230072969 + 3 ^ 40 * 1464802 * 2
def baseEnd_1464802 : Nat := 752147489667283189138505

theorem tailTrace_1464802 : CollatzResearch.WordTrace tailWord_1464802 prefixEnd_1464802 752147489667283189138505 := by
  unfold tailWord_1464802
  simp only [CollatzResearch.WordTrace]
  refine ⟨13356429509819999277449165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35617145359519998073197773 13356429509819999277449165)
  ·
    refine ⟨5008661066182499729043437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13356429509819999277449165 5008661066182499729043437)
    ·
      refine ⟨1878247899818437398391289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5008661066182499729043437 1878247899818437398391289)
      ·
        refine ⟨1408685924863828048793467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1878247899818437398391289 1408685924863828048793467)
        ·
          refine ⟨2113028887295742073190201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1408685924863828048793467 2113028887295742073190201)
          ·
            refine ⟨1584771665471806554892651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2113028887295742073190201 1584771665471806554892651)
            ·
              refine ⟨2377157498207709832338977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584771665471806554892651 2377157498207709832338977)
              ·
                refine ⟨1782868123655782374254233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2377157498207709832338977 1782868123655782374254233)
                ·
                  refine ⟨1337151092741836780690675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1782868123655782374254233 1337151092741836780690675)
                  ·
                    refine ⟨2005726639112755171036013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1337151092741836780690675 2005726639112755171036013)
                    ·
                      refine ⟨752147489667283189138505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2005726639112755171036013 752147489667283189138505)
                      ·
                        rfl

theorem cell23_1464802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1464802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464802 prefixEnd_1464802 := by exact prefixLift 1464802
  have htrace : WordTrace (prefixWord ++ tailWord_1464802) baseStart_1464802 baseEnd_1464802 := by
    simpa [prefixWord, tailWord_1464802, baseEnd_1464802] using wordTrace_append hprefix tailTrace_1464802
  have hstable : (prefixWord ++ tailWord_1464802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464802).length < 2 ^ (prefixWord ++ tailWord_1464802).sum := by decide
  have hdescent : baseEnd_1464802 < baseStart_1464802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464808 : List Nat := [2, 1, 4, 1, 1, 3, 3, 2, 2, 2, 2]
def baseStart_1464808 : Nat := 118140960795 + 1464808 * 2 ^ 59
def prefixEnd_1464808 : Nat := 4983230072969 + 3 ^ 40 * 1464808 * 2
def baseEnd_1464808 : Nat := 752150570551210165663477

theorem tailTrace_1464808 : CollatzResearch.WordTrace tailWord_1464808 prefixEnd_1464808 752150570551210165663477 := by
  unfold tailWord_1464808
  simp only [CollatzResearch.WordTrace]
  refine ⟨26712968438629130067257539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35617291251505506756343385 26712968438629130067257539)
  ·
    refine ⟨40069452657943695100886309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26712968438629130067257539 40069452657943695100886309)
    ·
      refine ⟨7513022373364442831416183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40069452657943695100886309 7513022373364442831416183)
      ·
        refine ⟨11269533560046664247124275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7513022373364442831416183 11269533560046664247124275)
        ·
          refine ⟨16904300340069996370686413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11269533560046664247124275 16904300340069996370686413)
          ·
            refine ⟨6339112627526248639007405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16904300340069996370686413 6339112627526248639007405)
            ·
              refine ⟨2377167235322343239627777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6339112627526248639007405 2377167235322343239627777)
              ·
                refine ⟨1782875426491757429720833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2377167235322343239627777 1782875426491757429720833)
                ·
                  refine ⟨1337156569868818072290625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1782875426491757429720833 1337156569868818072290625)
                  ·
                    refine ⟨1002867427401613554217969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1337156569868818072290625 1002867427401613554217969)
                    ·
                      refine ⟨752150570551210165663477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1002867427401613554217969 752150570551210165663477)
                      ·
                        rfl

theorem cell23_1464808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_1464808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464808 prefixEnd_1464808 := by exact prefixLift 1464808
  have htrace : WordTrace (prefixWord ++ tailWord_1464808) baseStart_1464808 baseEnd_1464808 := by
    simpa [prefixWord, tailWord_1464808, baseEnd_1464808] using wordTrace_append hprefix tailTrace_1464808
  have hstable : (prefixWord ++ tailWord_1464808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464808).length < 2 ^ (prefixWord ++ tailWord_1464808).sum := by decide
  have hdescent : baseEnd_1464808 < baseStart_1464808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464814 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 7]
def baseStart_1464814 : Nat := 118140960795 + 1464814 * 2 ^ 59
def prefixEnd_1464814 : Nat := 4983230072969 + 3 ^ 40 * 1464814 * 2
def baseEnd_1464814 : Nat := 83572627937237460243161

theorem tailTrace_1464814 : CollatzResearch.WordTrace tailWord_1464814 prefixEnd_1464814 83572627937237460243161 := by
  unfold tailWord_1464814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6678269464404565394904187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35617437143491015439488997 6678269464404565394904187)
  ·
    refine ⟨10017404196606848092356281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6678269464404565394904187 10017404196606848092356281)
    ·
      refine ⟨7513053147455136069267211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10017404196606848092356281 7513053147455136069267211)
      ·
        refine ⟨11269579721182704103900817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7513053147455136069267211 11269579721182704103900817)
        ·
          refine ⟨8452184790887028077925613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11269579721182704103900817 8452184790887028077925613)
          ·
            refine ⟨3169569296582635529222105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8452184790887028077925613 3169569296582635529222105)
            ·
              refine ⟨2377176972436976646916579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3169569296582635529222105 2377176972436976646916579)
              ·
                refine ⟨3565765458655464970374869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2377176972436976646916579 3565765458655464970374869)
                ·
                  refine ⟨83572627937237460243161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3565765458655464970374869 83572627937237460243161)
                  ·
                    rfl

theorem cell23_1464814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_1464814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464814 prefixEnd_1464814 := by exact prefixLift 1464814
  have htrace : WordTrace (prefixWord ++ tailWord_1464814) baseStart_1464814 baseEnd_1464814 := by
    simpa [prefixWord, tailWord_1464814, baseEnd_1464814] using wordTrace_append hprefix tailTrace_1464814
  have hstable : (prefixWord ++ tailWord_1464814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464814).length < 2 ^ (prefixWord ++ tailWord_1464814).sum := by decide
  have hdescent : baseEnd_1464814 < baseStart_1464814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464901 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 2, 2, 3]
def baseStart_1464901 : Nat := 118140960795 + 1464901 * 2 ^ 59
def prefixEnd_1464901 : Nat := 4983230072969 + 3 ^ 40 * 1464901 * 2
def baseEnd_1464901 : Nat := 752198324252078301800549

theorem tailTrace_1464901 : CollatzResearch.WordTrace tailWord_1464901 prefixEnd_1464901 752198324252078301800549 := by
  unfold tailWord_1464901
  simp only [CollatzResearch.WordTrace]
  refine ⟨53429328865921337017650557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35619552577280891345100371 53429328865921337017650557)
  ·
    refine ⟨20035998324720501381618959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53429328865921337017650557 20035998324720501381618959)
    ·
      refine ⟨30053997487080752072428439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20035998324720501381618959 30053997487080752072428439)
      ·
        refine ⟨45080996230621128108642659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30053997487080752072428439 45080996230621128108642659)
        ·
          refine ⟨67621494345931692162963989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45080996230621128108642659 67621494345931692162963989)
          ·
            refine ⟨3169757547465548070138937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67621494345931692162963989 3169757547465548070138937)
            ·
              refine ⟨2377318160599161052604203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3169757547465548070138937 2377318160599161052604203)
              ·
                refine ⟨3565977240898741578906305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2377318160599161052604203 3565977240898741578906305)
                ·
                  refine ⟨2674482930674056184179729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3565977240898741578906305 2674482930674056184179729)
                  ·
                    refine ⟨2005862198005542138134797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2674482930674056184179729 2005862198005542138134797)
                    ·
                      refine ⟨752198324252078301800549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2005862198005542138134797 752198324252078301800549)
                      ·
                        rfl

theorem cell23_1464901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_1464901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464901 prefixEnd_1464901 := by exact prefixLift 1464901
  have htrace : WordTrace (prefixWord ++ tailWord_1464901) baseStart_1464901 baseEnd_1464901 := by
    simpa [prefixWord, tailWord_1464901, baseEnd_1464901] using wordTrace_append hprefix tailTrace_1464901
  have hstable : (prefixWord ++ tailWord_1464901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464901).length < 2 ^ (prefixWord ++ tailWord_1464901).sum := by decide
  have hdescent : baseEnd_1464901 < baseStart_1464901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464927 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 5]
def baseStart_1464927 : Nat := 118140960795 + 1464927 * 2 ^ 59
def prefixEnd_1464927 : Nat := 4983230072969 + 3 ^ 40 * 1464927 * 2
def baseEnd_1464927 : Nat := 752211674749095200075429

theorem tailTrace_1464927 : CollatzResearch.WordTrace tailWord_1464927 prefixEnd_1464927 752211674749095200075429 := by
  unfold tailWord_1464927
  simp only [CollatzResearch.WordTrace]
  refine ⟨53430277163827143458097035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35620184775884762305398023 53430277163827143458097035)
  ·
    refine ⟨80145415745740715187145553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53430277163827143458097035 80145415745740715187145553)
    ·
      refine ⟨60109061809305536390359165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80145415745740715187145553 60109061809305536390359165)
      ·
        refine ⟨22540898178489576146384687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60109061809305536390359165 22540898178489576146384687)
        ·
          refine ⟨33811347267734364219577031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22540898178489576146384687 33811347267734364219577031)
          ·
            refine ⟨50717020901601546329365547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33811347267734364219577031 50717020901601546329365547)
            ·
              refine ⟨76075531352402319494048321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50717020901601546329365547 76075531352402319494048321)
              ·
                refine ⟨57056648514301739620536241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76075531352402319494048321 57056648514301739620536241)
                ·
                  refine ⟨42792486385726304715402181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57056648514301739620536241 42792486385726304715402181)
                  ·
                    refine ⟨8023591197323682134137909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42792486385726304715402181 8023591197323682134137909)
                    ·
                      refine ⟨752211674749095200075429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8023591197323682134137909 752211674749095200075429)
                      ·
                        rfl

theorem cell23_1464927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_1464927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464927 prefixEnd_1464927 := by exact prefixLift 1464927
  have htrace : WordTrace (prefixWord ++ tailWord_1464927) baseStart_1464927 baseEnd_1464927 := by
    simpa [prefixWord, tailWord_1464927, baseEnd_1464927] using wordTrace_append hprefix tailTrace_1464927
  have hstable : (prefixWord ++ tailWord_1464927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464927).length < 2 ^ (prefixWord ++ tailWord_1464927).sum := by decide
  have hdescent : baseEnd_1464927 < baseStart_1464927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464931 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 3, 1, 3]
def baseStart_1464931 : Nat := 118140960795 + 1464931 * 2 ^ 59
def prefixEnd_1464931 : Nat := 4983230072969 + 3 ^ 40 * 1464931 * 2
def baseEnd_1464931 : Nat := 752213728671713184425411

theorem tailTrace_1464931 : CollatzResearch.WordTrace tailWord_1464931 prefixEnd_1464931 752213728671713184425411 := by
  unfold tailWord_1464931
  simp only [CollatzResearch.WordTrace]
  refine ⟨53430423055812652141242647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35620282037208434760828431 53430423055812652141242647)
  ·
    refine ⟨80145634583718978211863971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53430423055812652141242647 80145634583718978211863971)
    ·
      refine ⟨120218451875578467317795957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80145634583718978211863971 120218451875578467317795957)
      ·
        refine ⟨11270479863335481311043371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120218451875578467317795957 11270479863335481311043371)
        ·
          refine ⟨16905719795003221966565057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11270479863335481311043371 16905719795003221966565057)
          ·
            refine ⟨12679289846252416474923793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16905719795003221966565057 12679289846252416474923793)
            ·
              refine ⟨9509467384689312356192845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12679289846252416474923793 9509467384689312356192845)
              ·
                refine ⟨3566050269258492133572317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9509467384689312356192845 3566050269258492133572317)
                ·
                  refine ⟨1337268850971934550089619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3566050269258492133572317 1337268850971934550089619)
                  ·
                    refine ⟨2005903276457901825134429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1337268850971934550089619 2005903276457901825134429)
                    ·
                      refine ⟨752213728671713184425411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2005903276457901825134429 752213728671713184425411)
                      ·
                        rfl

theorem cell23_1464931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_1464931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464931 prefixEnd_1464931 := by exact prefixLift 1464931
  have htrace : WordTrace (prefixWord ++ tailWord_1464931) baseStart_1464931 baseEnd_1464931 := by
    simpa [prefixWord, tailWord_1464931, baseEnd_1464931] using wordTrace_append hprefix tailTrace_1464931
  have hstable : (prefixWord ++ tailWord_1464931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464931).length < 2 ^ (prefixWord ++ tailWord_1464931).sum := by decide
  have hdescent : baseEnd_1464931 < baseStart_1464931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464965 : List Nat := [1, 3, 1, 1, 4, 3, 2, 3, 1, 1, 3]
def baseStart_1464965 : Nat := 118140960795 + 1464965 * 2 ^ 59
def prefixEnd_1464965 : Nat := 4983230072969 + 3 ^ 40 * 1464965 * 2
def baseEnd_1464965 : Nat := 752231187013966051400255

theorem tailTrace_1464965 : CollatzResearch.WordTrace tailWord_1464965 prefixEnd_1464965 752231187013966051400255 := by
  unfold tailWord_1464965
  simp only [CollatzResearch.WordTrace]
  refine ⟨53431663137689475947980349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35621108758459650631986899 53431663137689475947980349)
  ·
    refine ⟨20036873676633553480492631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53431663137689475947980349 20036873676633553480492631)
    ·
      refine ⟨30055310514950330220738947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20036873676633553480492631 30055310514950330220738947)
      ·
        refine ⟨45082965772425495331108421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30055310514950330220738947 45082965772425495331108421)
        ·
          refine ⟨8453056082329780374582829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45082965772425495331108421 8453056082329780374582829)
          ·
            refine ⟨3169896030873667640468561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8453056082329780374582829 3169896030873667640468561)
            ·
              refine ⟨2377422023155250730351421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3169896030873667640468561 2377422023155250730351421)
              ·
                refine ⟨891533258683219023881783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2377422023155250730351421 891533258683219023881783)
                ·
                  refine ⟨1337299888024828535822675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 891533258683219023881783 1337299888024828535822675)
                  ·
                    refine ⟨2005949832037242803734013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1337299888024828535822675 2005949832037242803734013)
                    ·
                      refine ⟨752231187013966051400255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2005949832037242803734013 752231187013966051400255)
                      ·
                        rfl

theorem cell23_1464965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 1, 1, 3].length) (baseStart_1464965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464965 prefixEnd_1464965 := by exact prefixLift 1464965
  have htrace : WordTrace (prefixWord ++ tailWord_1464965) baseStart_1464965 baseEnd_1464965 := by
    simpa [prefixWord, tailWord_1464965, baseEnd_1464965] using wordTrace_append hprefix tailTrace_1464965
  have hstable : (prefixWord ++ tailWord_1464965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464965).length < 2 ^ (prefixWord ++ tailWord_1464965).sum := by decide
  have hdescent : baseEnd_1464965 < baseStart_1464965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464984 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1464984 : Nat := 118140960795 + 1464984 * 2 ^ 59
def prefixEnd_1464984 : Nat := 4983230072969 + 3 ^ 40 * 1464984 * 2
def baseEnd_1464984 : Nat := 752240943146401477062667

theorem tailTrace_1464984 : CollatzResearch.WordTrace tailWord_1464984 prefixEnd_1464984 752240943146401477062667 := by
  unfold tailWord_1464984
  simp only [CollatzResearch.WordTrace]
  refine ⟨26716178062310321096461003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35621570749747094795281337 26716178062310321096461003)
  ·
    refine ⟨40074267093465481644691505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26716178062310321096461003 40074267093465481644691505)
    ·
      refine ⟨30055700320099111233518629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40074267093465481644691505 30055700320099111233518629)
      ·
        refine ⟨5635443810018583356284743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30055700320099111233518629 5635443810018583356284743)
        ·
          refine ⟨8453165715027875034427115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5635443810018583356284743 8453165715027875034427115)
          ·
            refine ⟨12679748572541812551640673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8453165715027875034427115 12679748572541812551640673)
            ·
              refine ⟨9509811429406359413730505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12679748572541812551640673 9509811429406359413730505)
              ·
                refine ⟨7132358572054769560297879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9509811429406359413730505 7132358572054769560297879)
                ·
                  refine ⟨10698537858082154340446819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7132358572054769560297879 10698537858082154340446819)
                  ·
                    refine ⟨16047806787123231510670229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10698537858082154340446819 16047806787123231510670229)
                    ·
                      refine ⟨752240943146401477062667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16047806787123231510670229 752240943146401477062667)
                      ·
                        rfl

theorem cell23_1464984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1464984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1464984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1464984 prefixEnd_1464984 := by exact prefixLift 1464984
  have htrace : WordTrace (prefixWord ++ tailWord_1464984) baseStart_1464984 baseEnd_1464984 := by
    simpa [prefixWord, tailWord_1464984, baseEnd_1464984] using wordTrace_append hprefix tailTrace_1464984
  have hstable : (prefixWord ++ tailWord_1464984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464984).length < 2 ^ (prefixWord ++ tailWord_1464984).sum := by decide
  have hdescent : baseEnd_1464984 < baseStart_1464984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465005 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_1465005 : Nat := 118140960795 + 1465005 * 2 ^ 59
def prefixEnd_1465005 : Nat := 4983230072969 + 3 ^ 40 * 1465005 * 2
def baseEnd_1465005 : Nat := 752251726240145894900071

theorem tailTrace_1465005 : CollatzResearch.WordTrace tailWord_1465005 prefixEnd_1465005 752251726240145894900071 := by
  unfold tailWord_1465005
  simp only [CollatzResearch.WordTrace]
  refine ⟨53433122057544562779436469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35622081371696375186290979 53433122057544562779436469)
  ·
    refine ⟨5009355192894802760572169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53433122057544562779436469 5009355192894802760572169)
    ·
      refine ⟨3757016394671102070429127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5009355192894802760572169 3757016394671102070429127)
      ·
        refine ⟨5635524592006653105643691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3757016394671102070429127 5635524592006653105643691)
        ·
          refine ⟨8453286888009979658465537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5635524592006653105643691 8453286888009979658465537)
          ·
            refine ⟨6339965166007484743849153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8453286888009979658465537 6339965166007484743849153)
            ·
              refine ⟨4754973874505613557886865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6339965166007484743849153 4754973874505613557886865)
              ·
                refine ⟨3566230405879210168415149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4754973874505613557886865 3566230405879210168415149)
                ·
                  refine ⟨1337336402204703813155681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3566230405879210168415149 1337336402204703813155681)
                  ·
                    refine ⟨1003002301653527859866761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1337336402204703813155681 1003002301653527859866761)
                    ·
                      refine ⟨752251726240145894900071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1003002301653527859866761 752251726240145894900071)
                      ·
                        rfl

theorem cell23_1465005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_1465005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465005 prefixEnd_1465005 := by exact prefixLift 1465005
  have htrace : WordTrace (prefixWord ++ tailWord_1465005) baseStart_1465005 baseEnd_1465005 := by
    simpa [prefixWord, tailWord_1465005, baseEnd_1465005] using wordTrace_append hprefix tailTrace_1465005
  have hstable : (prefixWord ++ tailWord_1465005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465005).length < 2 ^ (prefixWord ++ tailWord_1465005).sum := by decide
  have hdescent : baseEnd_1465005 < baseStart_1465005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465011 : List Nat := [1, 1, 1, 2, 3, 6, 2, 7]
def baseStart_1465011 : Nat := 118140960795 + 1465011 * 2 ^ 59
def prefixEnd_1465011 : Nat := 4983230072969 + 3 ^ 40 * 1465011 * 2
def baseEnd_1465011 : Nat := 27861289152743439682409

theorem tailTrace_1465011 : CollatzResearch.WordTrace tailWord_1465011 prefixEnd_1465011 27861289152743439682409 := by
  unfold tailWord_1465011
  simp only [CollatzResearch.WordTrace]
  refine ⟨53433340895522825804154887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35622227263681883869436591 53433340895522825804154887)
  ·
    refine ⟨80150011343284238706232331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53433340895522825804154887 80150011343284238706232331)
    ·
      refine ⟨120225017014926358059348497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80150011343284238706232331 120225017014926358059348497)
      ·
        refine ⟨90168762761194768544511373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120225017014926358059348497 90168762761194768544511373)
        ·
          refine ⟨33813286035448038204191765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90168762761194768544511373 33813286035448038204191765)
          ·
            refine ⟨1584997782911626790821489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33813286035448038204191765 1584997782911626790821489)
            ·
              refine ⟨1188748337183720093116117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1584997782911626790821489 1188748337183720093116117)
              ·
                refine ⟨27861289152743439682409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1188748337183720093116117 27861289152743439682409)
                ·
                  rfl

theorem cell23_1465011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 7].length) (baseStart_1465011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465011 prefixEnd_1465011 := by exact prefixLift 1465011
  have htrace : WordTrace (prefixWord ++ tailWord_1465011) baseStart_1465011 baseEnd_1465011 := by
    simpa [prefixWord, tailWord_1465011, baseEnd_1465011] using wordTrace_append hprefix tailTrace_1465011
  have hstable : (prefixWord ++ tailWord_1465011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465011).length < 2 ^ (prefixWord ++ tailWord_1465011).sum := by decide
  have hdescent : baseEnd_1465011 < baseStart_1465011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465025 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1465025 : Nat := 118140960795 + 1465025 * 2 ^ 59
def prefixEnd_1465025 : Nat := 4983230072969 + 3 ^ 40 * 1465025 * 2
def baseEnd_1465025 : Nat := 752261995853235816649979

theorem tailTrace_1465025 : CollatzResearch.WordTrace tailWord_1465025 prefixEnd_1465025 752261995853235816649979 := by
  unfold tailWord_1465025
  simp only [CollatzResearch.WordTrace]
  refine ⟨53433851517472106195164529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35622567678314737463443019 53433851517472106195164529)
  ·
    refine ⟨40075388638104079646373397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53433851517472106195164529 40075388638104079646373397)
    ·
      refine ⟨1878533842411128733423753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40075388638104079646373397 1878533842411128733423753)
      ·
        refine ⟨1408900381808346550067815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1878533842411128733423753 1408900381808346550067815)
        ·
          refine ⟨2113350572712519825101723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1408900381808346550067815 2113350572712519825101723)
          ·
            refine ⟨3170025859068779737652585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2113350572712519825101723 3170025859068779737652585)
            ·
              refine ⟨2377519394301584803239439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3170025859068779737652585 2377519394301584803239439)
              ·
                refine ⟨3566279091452377204859159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2377519394301584803239439 3566279091452377204859159)
                ·
                  refine ⟨5349418637178565807288739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3566279091452377204859159 5349418637178565807288739)
                  ·
                    refine ⟨8024127955767848710933109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5349418637178565807288739 8024127955767848710933109)
                    ·
                      refine ⟨752261995853235816649979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8024127955767848710933109 752261995853235816649979)
                      ·
                        rfl

theorem cell23_1465025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1465025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465025 prefixEnd_1465025 := by exact prefixLift 1465025
  have htrace : WordTrace (prefixWord ++ tailWord_1465025) baseStart_1465025 baseEnd_1465025 := by
    simpa [prefixWord, tailWord_1465025, baseEnd_1465025] using wordTrace_append hprefix tailTrace_1465025
  have hstable : (prefixWord ++ tailWord_1465025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465025).length < 2 ^ (prefixWord ++ tailWord_1465025).sum := by decide
  have hdescent : baseEnd_1465025 < baseStart_1465025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465038 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3]
def baseStart_1465038 : Nat := 118140960795 + 1465038 * 2 ^ 59
def prefixEnd_1465038 : Nat := 4983230072969 + 3 ^ 40 * 1465038 * 2
def baseEnd_1465038 : Nat := 752268671101744265787419

theorem tailTrace_1465038 : CollatzResearch.WordTrace tailWord_1465038 prefixEnd_1465038 752268671101744265787419 := by
  unfold tailWord_1465038
  simp only [CollatzResearch.WordTrace]
  refine ⟨6679290708303126176923471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35622883777616672943591845 6679290708303126176923471)
  ·
    refine ⟨10018936062454689265385207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6679290708303126176923471 10018936062454689265385207)
    ·
      refine ⟨15028404093682033898077811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10018936062454689265385207 15028404093682033898077811)
      ·
        refine ⟨22542606140523050847116717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15028404093682033898077811 22542606140523050847116717)
        ·
          refine ⟨8453477302696144067668769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22542606140523050847116717 8453477302696144067668769)
          ·
            refine ⟨6340107977022108050751577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8453477302696144067668769 6340107977022108050751577)
            ·
              refine ⟨4755080982766581038063683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6340107977022108050751577 4755080982766581038063683)
              ·
                refine ⟨7132621474149871557095525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4755080982766581038063683 7132621474149871557095525)
                ·
                  refine ⟨1337366526403100916955411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7132621474149871557095525 1337366526403100916955411)
                  ·
                    refine ⟨2006049789604651375433117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1337366526403100916955411 2006049789604651375433117)
                    ·
                      refine ⟨752268671101744265787419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2006049789604651375433117 752268671101744265787419)
                      ·
                        rfl

theorem cell23_1465038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_1465038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465038 prefixEnd_1465038 := by exact prefixLift 1465038
  have htrace : WordTrace (prefixWord ++ tailWord_1465038) baseStart_1465038 baseEnd_1465038 := by
    simpa [prefixWord, tailWord_1465038, baseEnd_1465038] using wordTrace_append hprefix tailTrace_1465038
  have hstable : (prefixWord ++ tailWord_1465038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465038).length < 2 ^ (prefixWord ++ tailWord_1465038).sum := by decide
  have hdescent : baseEnd_1465038 < baseStart_1465038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465055 : List Nat := [1, 1, 2, 3, 2, 3, 4, 1, 2, 1, 3]
def baseStart_1465055 : Nat := 118140960795 + 1465055 * 2 ^ 59
def prefixEnd_1465055 : Nat := 4983230072969 + 3 ^ 40 * 1465055 * 2
def baseEnd_1465055 : Nat := 752277400272870699274841

theorem tailTrace_1465055 : CollatzResearch.WordTrace tailWord_1465055 prefixEnd_1465055 752277400272870699274841 := by
  unfold tailWord_1465055
  simp only [CollatzResearch.WordTrace]
  refine ⟨53434945707363421318756619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35623297138242280879171079 53434945707363421318756619)
  ·
    refine ⟨80152418561045131978134929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53434945707363421318756619 80152418561045131978134929)
    ·
      refine ⟨60114313920783848983601197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80152418561045131978134929 60114313920783848983601197)
      ·
        refine ⟨22542867720293943368850449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60114313920783848983601197 22542867720293943368850449)
        ·
          refine ⟨16907150790220457526637837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22542867720293943368850449 16907150790220457526637837)
          ·
            refine ⟨6340181546332671572489189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16907150790220457526637837 6340181546332671572489189)
            ·
              refine ⟨1188784039937375919841723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6340181546332671572489189 1188784039937375919841723)
              ·
                refine ⟨1783176059906063879762585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188784039937375919841723 1783176059906063879762585)
                ·
                  refine ⟨1337382044929547909821939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1783176059906063879762585 1337382044929547909821939)
                  ·
                    refine ⟨2006073067394321864732909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1337382044929547909821939 2006073067394321864732909)
                    ·
                      refine ⟨752277400272870699274841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2006073067394321864732909 752277400272870699274841)
                      ·
                        rfl

theorem cell23_1465055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_1465055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465055 prefixEnd_1465055 := by exact prefixLift 1465055
  have htrace : WordTrace (prefixWord ++ tailWord_1465055) baseStart_1465055 baseEnd_1465055 := by
    simpa [prefixWord, tailWord_1465055, baseEnd_1465055] using wordTrace_append hprefix tailTrace_1465055
  have hstable : (prefixWord ++ tailWord_1465055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465055).length < 2 ^ (prefixWord ++ tailWord_1465055).sum := by decide
  have hdescent : baseEnd_1465055 < baseStart_1465055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465133 : List Nat := [1, 5, 3, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_1465133 : Nat := 118140960795 + 1465133 * 2 ^ 59
def prefixEnd_1465133 : Nat := 4983230072969 + 3 ^ 40 * 1465133 * 2
def baseEnd_1465133 : Nat := 752317451763921394099483

theorem tailTrace_1465133 : CollatzResearch.WordTrace tailWord_1465133 prefixEnd_1465133 752317451763921394099483 := by
  unfold tailWord_1465133
  simp only [CollatzResearch.WordTrace]
  refine ⟨53437790601080840640096053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35625193734053893760064035 53437790601080840640096053)
  ·
    refine ⟨5009792868851328810009005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53437790601080840640096053 5009792868851328810009005)
    ·
      refine ⟨1878672325819248303753377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5009792868851328810009005 1878672325819248303753377)
      ·
        refine ⟨1409004244364436227815033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1878672325819248303753377 1409004244364436227815033)
        ·
          refine ⟨1056753183273327170861275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1409004244364436227815033 1056753183273327170861275)
          ·
            refine ⟨1585129774909990756291913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056753183273327170861275 1585129774909990756291913)
            ·
              refine ⟨1188847331182493067218935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1585129774909990756291913 1188847331182493067218935)
              ·
                refine ⟨1783270996773739600828403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188847331182493067218935 1783270996773739600828403)
                ·
                  refine ⟨2674906495160609401242605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783270996773739600828403 2674906495160609401242605)
                  ·
                    refine ⟨1003089935685228525465977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2674906495160609401242605 1003089935685228525465977)
                    ·
                      refine ⟨752317451763921394099483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1003089935685228525465977 752317451763921394099483)
                      ·
                        rfl

theorem cell23_1465133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_1465133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465133 prefixEnd_1465133 := by exact prefixLift 1465133
  have htrace : WordTrace (prefixWord ++ tailWord_1465133) baseStart_1465133 baseEnd_1465133 := by
    simpa [prefixWord, tailWord_1465133, baseEnd_1465133] using wordTrace_append hprefix tailTrace_1465133
  have hstable : (prefixWord ++ tailWord_1465133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465133).length < 2 ^ (prefixWord ++ tailWord_1465133).sum := by decide
  have hdescent : baseEnd_1465133 < baseStart_1465133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465168 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 2, 4, 2]
def baseStart_1465168 : Nat := 118140960795 + 1465168 * 2 ^ 59
def prefixEnd_1465168 : Nat := 4983230072969 + 3 ^ 40 * 1465168 * 2
def baseEnd_1465168 : Nat := 752335423586828757161821

theorem tailTrace_1465168 : CollatzResearch.WordTrace tailWord_1465168 prefixEnd_1465168 752335423586828757161821 := by
  unfold tailWord_1465168
  simp only [CollatzResearch.WordTrace]
  refine ⟨26719533577977020808810079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35626044770636027745080105 26719533577977020808810079)
  ·
    refine ⟨40079300366965531213215119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26719533577977020808810079 40079300366965531213215119)
    ·
      refine ⟨60118950550448296819822679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40079300366965531213215119 60118950550448296819822679)
      ·
        refine ⟨90178425825672445229734019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60118950550448296819822679 90178425825672445229734019)
        ·
          refine ⟨135267638738508667844601029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90178425825672445229734019 135267638738508667844601029)
          ·
            refine ⟨25362682263470375220862693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135267638738508667844601029 25362682263470375220862693)
            ·
              refine ⟨4755502924400695353911755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25362682263470375220862693 4755502924400695353911755)
              ·
                refine ⟨7133254386601043030867633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4755502924400695353911755 7133254386601043030867633)
                ·
                  refine ⟨5349940789950782273150725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7133254386601043030867633 5349940789950782273150725)
                  ·
                    refine ⟨1003113898115771676215761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5349940789950782273150725 1003113898115771676215761)
                    ·
                      refine ⟨752335423586828757161821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1003113898115771676215761 752335423586828757161821)
                      ·
                        rfl

theorem cell23_1465168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 2, 4, 2].length) (baseStart_1465168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465168 prefixEnd_1465168 := by exact prefixLift 1465168
  have htrace : WordTrace (prefixWord ++ tailWord_1465168) baseStart_1465168 baseEnd_1465168 := by
    simpa [prefixWord, tailWord_1465168, baseEnd_1465168] using wordTrace_append hprefix tailTrace_1465168
  have hstable : (prefixWord ++ tailWord_1465168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465168).length < 2 ^ (prefixWord ++ tailWord_1465168).sum := by decide
  have hdescent : baseEnd_1465168 < baseStart_1465168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465178 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 3, 4]
def baseStart_1465178 : Nat := 118140960795 + 1465178 * 2 ^ 59
def prefixEnd_1465178 : Nat := 4983230072969 + 3 ^ 40 * 1465178 * 2
def baseEnd_1465178 : Nat := 250780186131124572678925

theorem tailTrace_1465178 : CollatzResearch.WordTrace tailWord_1465178 prefixEnd_1465178 250780186131124572678925 := by
  unfold tailWord_1465178
  simp only [CollatzResearch.WordTrace]
  refine ⟨13359857971479453331371047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35626287923945208883656125 13359857971479453331371047)
  ·
    refine ⟨20039786957219179997056571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13359857971479453331371047 20039786957219179997056571)
    ·
      refine ⟨30059680435828769995584857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20039786957219179997056571 30059680435828769995584857)
      ·
        refine ⟨22544760326871577496688643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30059680435828769995584857 22544760326871577496688643)
        ·
          refine ⟨33817140490307366245032965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22544760326871577496688643 33817140490307366245032965)
          ·
            refine ⟨6340713841932631170943681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33817140490307366245032965 6340713841932631170943681)
            ·
              refine ⟨4755535381449473378207761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6340713841932631170943681 4755535381449473378207761)
              ·
                refine ⟨3566651536087105033655821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4755535381449473378207761 3566651536087105033655821)
                ·
                  refine ⟨1337494326032664387620933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3566651536087105033655821 1337494326032664387620933)
                  ·
                    refine ⟨250780186131124572678925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1337494326032664387620933 250780186131124572678925)
                    ·
                      rfl

theorem cell23_1465178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_1465178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465178 prefixEnd_1465178 := by exact prefixLift 1465178
  have htrace : WordTrace (prefixWord ++ tailWord_1465178) baseStart_1465178 baseEnd_1465178 := by
    simpa [prefixWord, tailWord_1465178, baseEnd_1465178] using wordTrace_append hprefix tailTrace_1465178
  have hstable : (prefixWord ++ tailWord_1465178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465178).length < 2 ^ (prefixWord ++ tailWord_1465178).sum := by decide
  have hdescent : baseEnd_1465178 < baseStart_1465178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465188 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 1, 4, 3]
def baseStart_1465188 : Nat := 118140960795 + 1465188 * 2 ^ 59
def prefixEnd_1465188 : Nat := 4983230072969 + 3 ^ 40 * 1465188 * 2
def baseEnd_1465188 : Nat := 752345693199918678911729

theorem tailTrace_1465188 : CollatzResearch.WordTrace tailWord_1465188 prefixEnd_1465188 752345693199918678911729 := by
  unfold tailWord_1465188
  simp only [CollatzResearch.WordTrace]
  refine ⟨26719898307940792516674109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35626531077254390022232145 26719898307940792516674109)
  ·
    refine ⟨10019961865477797193752791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26719898307940792516674109 10019961865477797193752791)
    ·
      refine ⟨15029942798216695790629187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10019961865477797193752791 15029942798216695790629187)
      ·
        refine ⟨22544914197325043685943781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15029942798216695790629187 22544914197325043685943781)
        ·
          refine ⟨4227171411998445691114459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22544914197325043685943781 4227171411998445691114459)
          ·
            refine ⟨6340757117997668536671689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4227171411998445691114459 6340757117997668536671689)
            ·
              refine ⟨4755567838498251402503767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6340757117997668536671689 4755567838498251402503767)
              ·
                refine ⟨7133351757747377103755651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4755567838498251402503767 7133351757747377103755651)
                ·
                  refine ⟨10700027636621065655633477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7133351757747377103755651 10700027636621065655633477)
                  ·
                    refine ⟨2006255181866449810431277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10700027636621065655633477 2006255181866449810431277)
                    ·
                      refine ⟨752345693199918678911729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2006255181866449810431277 752345693199918678911729)
                      ·
                        rfl

theorem cell23_1465188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_1465188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465188 prefixEnd_1465188 := by exact prefixLift 1465188
  have htrace : WordTrace (prefixWord ++ tailWord_1465188) baseStart_1465188 baseEnd_1465188 := by
    simpa [prefixWord, tailWord_1465188, baseEnd_1465188] using wordTrace_append hprefix tailTrace_1465188
  have hstable : (prefixWord ++ tailWord_1465188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465188).length < 2 ^ (prefixWord ++ tailWord_1465188).sum := by decide
  have hdescent : baseEnd_1465188 < baseStart_1465188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465191 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 8]
def baseStart_1465191 : Nat := 118140960795 + 1465191 * 2 ^ 59
def prefixEnd_1465191 : Nat := 4983230072969 + 3 ^ 40 * 1465191 * 2
def baseEnd_1465191 : Nat := 83594137071320240797135

theorem tailTrace_1465191 : CollatzResearch.WordTrace tailWord_1465191 prefixEnd_1465191 83594137071320240797135 := by
  unfold tailWord_1465191
  simp only [CollatzResearch.WordTrace]
  refine ⟨53439906034870716545707427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35626604023247144363804951 53439906034870716545707427)
  ·
    refine ⟨80159859052306074818561141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53439906034870716545707427 80159859052306074818561141)
    ·
      refine ⟨7514986786153694514240107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80159859052306074818561141 7514986786153694514240107)
      ·
        refine ⟨11272480179230541771360161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7514986786153694514240107 11272480179230541771360161)
        ·
          refine ⟨8454360134422906328520121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11272480179230541771360161 8454360134422906328520121)
          ·
            refine ⟨6340770100817179746390091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8454360134422906328520121 6340770100817179746390091)
            ·
              refine ⟨9511155151225769619585137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6340770100817179746390091 9511155151225769619585137)
              ·
                refine ⟨7133366363419327214688853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9511155151225769619585137 7133366363419327214688853)
                ·
                  refine ⟨83594137071320240797135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7133366363419327214688853 83594137071320240797135)
                  ·
                    rfl

theorem cell23_1465191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 8].length) (baseStart_1465191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465191 prefixEnd_1465191 := by exact prefixLift 1465191
  have htrace : WordTrace (prefixWord ++ tailWord_1465191) baseStart_1465191 baseEnd_1465191 := by
    simpa [prefixWord, tailWord_1465191, baseEnd_1465191] using wordTrace_append hprefix tailTrace_1465191
  have hstable : (prefixWord ++ tailWord_1465191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465191).length < 2 ^ (prefixWord ++ tailWord_1465191).sum := by decide
  have hdescent : baseEnd_1465191 < baseStart_1465191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465195 : List Nat := [1, 1, 1, 1, 2, 2, 7, 3, 1, 4]
def baseStart_1465195 : Nat := 118140960795 + 1465195 * 2 ^ 59
def prefixEnd_1465195 : Nat := 4983230072969 + 3 ^ 40 * 1465195 * 2
def baseEnd_1465195 : Nat := 250783095854833383841399

theorem tailTrace_1465195 : CollatzResearch.WordTrace tailWord_1465195 prefixEnd_1465195 250783095854833383841399 := by
  unfold tailWord_1465195
  simp only [CollatzResearch.WordTrace]
  refine ⟨53440051926856225228853039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35626701284570816819235359 53440051926856225228853039)
  ·
    refine ⟨80160077890284337843279559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53440051926856225228853039 80160077890284337843279559)
    ·
      refine ⟨120240116835426506764919339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80160077890284337843279559 120240116835426506764919339)
      ·
        refine ⟨180360175253139760147379009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120240116835426506764919339 180360175253139760147379009)
        ·
          refine ⟨135270131439854820110534257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180360175253139760147379009 135270131439854820110534257)
          ·
            refine ⟨101452598579891115082900693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135270131439854820110534257 101452598579891115082900693)
            ·
              refine ⟨2377795279216198009755485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 101452598579891115082900693 2377795279216198009755485)
              ·
                refine ⟨891673229706074253658307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2377795279216198009755485 891673229706074253658307)
                ·
                  refine ⟨1337509844559111380487461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 891673229706074253658307 1337509844559111380487461)
                  ·
                    refine ⟨250783095854833383841399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1337509844559111380487461 250783095854833383841399)
                    ·
                      rfl

theorem cell23_1465195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 1, 4].length) (baseStart_1465195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465195 prefixEnd_1465195 := by exact prefixLift 1465195
  have htrace : WordTrace (prefixWord ++ tailWord_1465195) baseStart_1465195 baseEnd_1465195 := by
    simpa [prefixWord, tailWord_1465195, baseEnd_1465195] using wordTrace_append hprefix tailTrace_1465195
  have hstable : (prefixWord ++ tailWord_1465195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465195).length < 2 ^ (prefixWord ++ tailWord_1465195).sum := by decide
  have hdescent : baseEnd_1465195 < baseStart_1465195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465205 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_1465205 : Nat := 118140960795 + 1465205 * 2 ^ 59
def prefixEnd_1465205 : Nat := 4983230072969 + 3 ^ 40 * 1465205 * 2
def baseEnd_1465205 : Nat := 752354422371045112399151

theorem tailTrace_1465205 : CollatzResearch.WordTrace tailWord_1465205 prefixEnd_1465205 752354422371045112399151 := by
  unfold tailWord_1465205
  simp only [CollatzResearch.WordTrace]
  refine ⟨53440416656819996936717069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35626944437879997957811379 53440416656819996936717069)
  ·
    refine ⟨20040156246307498851268901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53440416656819996936717069 20040156246307498851268901)
    ·
      refine ⟨3757529296182656034612919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20040156246307498851268901 3757529296182656034612919)
      ·
        refine ⟨5636293944273984051919379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3757529296182656034612919 5636293944273984051919379)
        ·
          refine ⟨8454440916410976077879069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5636293944273984051919379 8454440916410976077879069)
          ·
            refine ⟨3170415343654116029204651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8454440916410976077879069 3170415343654116029204651)
            ·
              refine ⟨4755623015481174043806977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3170415343654116029204651 4755623015481174043806977)
              ·
                refine ⟨3566717261610880532855233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4755623015481174043806977 3566717261610880532855233)
                ·
                  refine ⟨2675037946208160399641425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3566717261610880532855233 2675037946208160399641425)
                  ·
                    refine ⟨2006278459656120299731069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2675037946208160399641425 2006278459656120299731069)
                    ·
                      refine ⟨752354422371045112399151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2006278459656120299731069 752354422371045112399151)
                      ·
                        rfl

theorem cell23_1465205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_1465205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465205 prefixEnd_1465205 := by exact prefixLift 1465205
  have htrace : WordTrace (prefixWord ++ tailWord_1465205) baseStart_1465205 baseEnd_1465205 := by
    simpa [prefixWord, tailWord_1465205, baseEnd_1465205] using wordTrace_append hprefix tailTrace_1465205
  have hstable : (prefixWord ++ tailWord_1465205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465205).length < 2 ^ (prefixWord ++ tailWord_1465205).sum := by decide
  have hdescent : baseEnd_1465205 < baseStart_1465205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465225 : List Nat := [1, 2, 1, 1, 5, 4, 2, 1, 6]
def baseStart_1465225 : Nat := 118140960795 + 1465225 * 2 ^ 59
def prefixEnd_1465225 : Nat := 4983230072969 + 3 ^ 40 * 1465225 * 2
def baseEnd_1465225 : Nat := 83596076887126114905451

theorem tailTrace_1465225 : CollatzResearch.WordTrace tailWord_1465225 prefixEnd_1465225 83596076887126114905451 := by
  unfold tailWord_1465225
  simp only [CollatzResearch.WordTrace]
  refine ⟨53441146116747540352445129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35627430744498360234963419 53441146116747540352445129)
  ·
    refine ⟨40080859587560655264333847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53441146116747540352445129 40080859587560655264333847)
    ·
      refine ⟨60121289381340982896500771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40080859587560655264333847 60121289381340982896500771)
      ·
        refine ⟨90181934072011474344751157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60121289381340982896500771 90181934072011474344751157)
        ·
          refine ⟨8454556319251075719820421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90181934072011474344751157 8454556319251075719820421)
          ·
            refine ⟨1585229309859576697466329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8454556319251075719820421 1585229309859576697466329)
            ·
              refine ⟨1188921982394682523099747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1585229309859576697466329 1188921982394682523099747)
              ·
                refine ⟨1783382973592023784649621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188921982394682523099747 1783382973592023784649621)
                ·
                  refine ⟨83596076887126114905451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1783382973592023784649621 83596076887126114905451)
                  ·
                    rfl

theorem cell23_1465225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 6].length) (baseStart_1465225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465225 prefixEnd_1465225 := by exact prefixLift 1465225
  have htrace : WordTrace (prefixWord ++ tailWord_1465225) baseStart_1465225 baseEnd_1465225 := by
    simpa [prefixWord, tailWord_1465225, baseEnd_1465225] using wordTrace_append hprefix tailTrace_1465225
  have hstable : (prefixWord ++ tailWord_1465225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465225).length < 2 ^ (prefixWord ++ tailWord_1465225).sum := by decide
  have hdescent : baseEnd_1465225 < baseStart_1465225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465228 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 3, 5, 2]
def baseStart_1465228 : Nat := 118140960795 + 1465228 * 2 ^ 59
def prefixEnd_1465228 : Nat := 4983230072969 + 3 ^ 40 * 1465228 * 2
def baseEnd_1465228 : Nat := 752366232426098522411545

theorem tailTrace_1465228 : CollatzResearch.WordTrace tailWord_1465228 prefixEnd_1465228 752366232426098522411545 := by
  unfold tailWord_1465228
  simp only [CollatzResearch.WordTrace]
  refine ⟨26720627767868335932402169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35627503690491114576536225 26720627767868335932402169)
  ·
    refine ⟨20040470825901251949301627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26720627767868335932402169 20040470825901251949301627)
    ·
      refine ⟨30060706238851877923952441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20040470825901251949301627 30060706238851877923952441)
      ·
        refine ⟨22545529679138908442964331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30060706238851877923952441 22545529679138908442964331)
        ·
          refine ⟨33818294518708362664446497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22545529679138908442964331 33818294518708362664446497)
          ·
            refine ⟨25363720889031271998334873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33818294518708362664446497 25363720889031271998334873)
            ·
              refine ⟨19022790666773453998751155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25363720889031271998334873 19022790666773453998751155)
              ·
                refine ⟨28534186000160180998126733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19022790666773453998751155 28534186000160180998126733)
                ·
                  refine ⟨10700319750060067874297525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28534186000160180998126733 10700319750060067874297525)
                  ·
                    refine ⟨1003154976568131363215393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10700319750060067874297525 1003154976568131363215393)
                    ·
                      refine ⟨752366232426098522411545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1003154976568131363215393 752366232426098522411545)
                      ·
                        rfl

theorem cell23_1465228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_1465228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465228 prefixEnd_1465228 := by exact prefixLift 1465228
  have htrace : WordTrace (prefixWord ++ tailWord_1465228) baseStart_1465228 baseEnd_1465228 := by
    simpa [prefixWord, tailWord_1465228, baseEnd_1465228] using wordTrace_append hprefix tailTrace_1465228
  have hstable : (prefixWord ++ tailWord_1465228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465228).length < 2 ^ (prefixWord ++ tailWord_1465228).sum := by decide
  have hdescent : baseEnd_1465228 < baseStart_1465228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465251 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 3, 6]
def baseStart_1465251 : Nat := 118140960795 + 1465251 * 2 ^ 59
def prefixEnd_1465251 : Nat := 4983230072969 + 3 ^ 40 * 1465251 * 2
def baseEnd_1465251 : Nat := 250792680827050644141313

theorem tailTrace_1465251 : CollatzResearch.WordTrace tailWord_1465251 prefixEnd_1465251 250792680827050644141313 := by
  unfold tailWord_1465251
  simp only [CollatzResearch.WordTrace]
  refine ⟨53442094414653346792891607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35628062943102231195261071 53442094414653346792891607)
  ·
    refine ⟨80163141621980020189337411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53442094414653346792891607 80163141621980020189337411)
    ·
      refine ⟨120244712432970030284006117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80163141621980020189337411 120244712432970030284006117)
      ·
        refine ⟨22545883581181880678251147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120244712432970030284006117 22545883581181880678251147)
        ·
          refine ⟨33818825371772821017376721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22545883581181880678251147 33818825371772821017376721)
          ·
            refine ⟨25364119028829615763032541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33818825371772821017376721 25364119028829615763032541)
            ·
              refine ⟨9511544635811105911137203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25364119028829615763032541 9511544635811105911137203)
              ·
                refine ⟨14267316953716658866705805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9511544635811105911137203 14267316953716658866705805)
                ·
                  refine ⟨5350243857643747075014677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14267316953716658866705805 5350243857643747075014677)
                  ·
                    refine ⟨250792680827050644141313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5350243857643747075014677 250792680827050644141313)
                    ·
                      rfl

theorem cell23_1465251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 6].length) (baseStart_1465251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465251 prefixEnd_1465251 := by exact prefixLift 1465251
  have htrace : WordTrace (prefixWord ++ tailWord_1465251) baseStart_1465251 baseEnd_1465251 := by
    simpa [prefixWord, tailWord_1465251, baseEnd_1465251] using wordTrace_append hprefix tailTrace_1465251
  have hstable : (prefixWord ++ tailWord_1465251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465251).length < 2 ^ (prefixWord ++ tailWord_1465251).sum := by decide
  have hdescent : baseEnd_1465251 < baseStart_1465251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465252 : List Nat := [2, 3, 1, 2, 1, 2, 2, 5, 1, 1, 3]
def baseStart_1465252 : Nat := 118140960795 + 1465252 * 2 ^ 59
def prefixEnd_1465252 : Nat := 4983230072969 + 3 ^ 40 * 1465252 * 2
def baseEnd_1465252 : Nat := 752378555961806428511435

theorem tailTrace_1465252 : CollatzResearch.WordTrace tailWord_1465252 prefixEnd_1465252 752378555961806428511435 := by
  unfold tailWord_1465252
  simp only [CollatzResearch.WordTrace]
  refine ⟨26721065443824861981839005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35628087258433149309118673 26721065443824861981839005)
  ·
    refine ⟨10020399541434323243189627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26721065443824861981839005 10020399541434323243189627)
    ·
      refine ⟨15030599312151484864784441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10020399541434323243189627 15030599312151484864784441)
      ·
        refine ⟨11272949484113613648588331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15030599312151484864784441 11272949484113613648588331)
        ·
          refine ⟨16909424226170420472882497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11272949484113613648588331 16909424226170420472882497)
          ·
            refine ⟨12682068169627815354661873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16909424226170420472882497 12682068169627815354661873)
            ·
              refine ⟨9511551127220861515996405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12682068169627815354661873 9511551127220861515996405)
              ·
                refine ⟨891707918176955767124663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9511551127220861515996405 891707918176955767124663)
                ·
                  refine ⟨1337561877265433650686995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 891707918176955767124663 1337561877265433650686995)
                  ·
                    refine ⟨2006342815898150476030493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1337561877265433650686995 2006342815898150476030493)
                    ·
                      refine ⟨752378555961806428511435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2006342815898150476030493 752378555961806428511435)
                      ·
                        rfl

theorem cell23_1465252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_1465252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465252 prefixEnd_1465252 := by exact prefixLift 1465252
  have htrace : WordTrace (prefixWord ++ tailWord_1465252) baseStart_1465252 baseEnd_1465252 := by
    simpa [prefixWord, tailWord_1465252, baseEnd_1465252] using wordTrace_append hprefix tailTrace_1465252
  have hstable : (prefixWord ++ tailWord_1465252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465252).length < 2 ^ (prefixWord ++ tailWord_1465252).sum := by decide
  have hdescent : baseEnd_1465252 < baseStart_1465252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465271 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 6]
def baseStart_1465271 : Nat := 118140960795 + 1465271 * 2 ^ 59
def prefixEnd_1465271 : Nat := 4983230072969 + 3 ^ 40 * 1465271 * 2
def baseEnd_1465271 : Nat := 752388312094241854173847

theorem tailTrace_1465271 : CollatzResearch.WordTrace tailWord_1465271 prefixEnd_1465271 752388312094241854173847 := by
  unfold tailWord_1465271
  simp only [CollatzResearch.WordTrace]
  refine ⟨53442823874580890208619667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35628549249720593472413111 53442823874580890208619667)
  ·
    refine ⟨80164235811871335312929501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53442823874580890208619667 80164235811871335312929501)
    ·
      refine ⟨30061588429451750742348563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80164235811871335312929501 30061588429451750742348563)
      ·
        refine ⟨45092382644177626113522845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30061588429451750742348563 45092382644177626113522845)
        ·
          refine ⟨16909643491566609792571067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45092382644177626113522845 16909643491566609792571067)
          ·
            refine ⟨25364465237349914688856601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16909643491566609792571067 25364465237349914688856601)
            ·
              refine ⟨19023348928012436016642451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25364465237349914688856601 19023348928012436016642451)
              ·
                refine ⟨28535023392018654024963677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19023348928012436016642451 28535023392018654024963677)
                ·
                  refine ⟨10700633772006995259361379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28535023392018654024963677 10700633772006995259361379)
                  ·
                    refine ⟨16050950658010492889042069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10700633772006995259361379 16050950658010492889042069)
                    ·
                      refine ⟨752388312094241854173847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16050950658010492889042069 752388312094241854173847)
                      ·
                        rfl

theorem cell23_1465271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_1465271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465271 prefixEnd_1465271 := by exact prefixLift 1465271
  have htrace : WordTrace (prefixWord ++ tailWord_1465271) baseStart_1465271 baseEnd_1465271 := by
    simpa [prefixWord, tailWord_1465271, baseEnd_1465271] using wordTrace_append hprefix tailTrace_1465271
  have hstable : (prefixWord ++ tailWord_1465271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465271).length < 2 ^ (prefixWord ++ tailWord_1465271).sum := by decide
  have hdescent : baseEnd_1465271 < baseStart_1465271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465278 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_1465278 : Nat := 118140960795 + 1465278 * 2 ^ 59
def prefixEnd_1465278 : Nat := 4983230072969 + 3 ^ 40 * 1465278 * 2
def baseEnd_1465278 : Nat := 752391906458823326786315

theorem tailTrace_1465278 : CollatzResearch.WordTrace tailWord_1465278 prefixEnd_1465278 752391906458823326786315 := by
  unfold tailWord_1465278
  simp only [CollatzResearch.WordTrace]
  refine ⟨6680384898194441300515561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35628719457037020269416325 6680384898194441300515561)
  ·
    refine ⟨5010288673645830975386671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6680384898194441300515561 5010288673645830975386671)
    ·
      refine ⟨7515433010468746463080007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5010288673645830975386671 7515433010468746463080007)
      ·
        refine ⟨11273149515703119694620011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7515433010468746463080007 11273149515703119694620011)
        ·
          refine ⟨16909724273554679541930017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11273149515703119694620011 16909724273554679541930017)
          ·
            refine ⟨12682293205166009656447513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16909724273554679541930017 12682293205166009656447513)
            ·
              refine ⟨9511719903874507242335635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12682293205166009656447513 9511719903874507242335635)
              ·
                refine ⟨14267579855811760863503453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9511719903874507242335635 14267579855811760863503453)
                ·
                  refine ⟨5350342445929410323813795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14267579855811760863503453 5350342445929410323813795)
                  ·
                    refine ⟨8025513668894115485720693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5350342445929410323813795 8025513668894115485720693)
                    ·
                      refine ⟨752391906458823326786315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8025513668894115485720693 752391906458823326786315)
                      ·
                        rfl

theorem cell23_1465278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_1465278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465278 prefixEnd_1465278 := by exact prefixLift 1465278
  have htrace : WordTrace (prefixWord ++ tailWord_1465278) baseStart_1465278 baseEnd_1465278 := by
    simpa [prefixWord, tailWord_1465278, baseEnd_1465278] using wordTrace_append hprefix tailTrace_1465278
  have hstable : (prefixWord ++ tailWord_1465278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465278).length < 2 ^ (prefixWord ++ tailWord_1465278).sum := by decide
  have hdescent : baseEnd_1465278 < baseStart_1465278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465292 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 3, 2, 2]
def baseStart_1465292 : Nat := 118140960795 + 1465292 * 2 ^ 59
def prefixEnd_1465292 : Nat := 4983230072969 + 3 ^ 40 * 1465292 * 2
def baseEnd_1465292 : Nat := 752399095187986272011251

theorem tailTrace_1465292 : CollatzResearch.WordTrace tailWord_1465292 prefixEnd_1465292 752399095187986272011251 := by
  unfold tailWord_1465292
  simp only [CollatzResearch.WordTrace]
  refine ⟨26721794903752405397567065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35629059871669873863422753 26721794903752405397567065)
  ·
    refine ⟨20041346177814304048175299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26721794903752405397567065 20041346177814304048175299)
    ·
      refine ⟨30062019266721456072262949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20041346177814304048175299 30062019266721456072262949)
      ·
        refine ⟨5636628612510273013549303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30062019266721456072262949 5636628612510273013549303)
        ·
          refine ⟨8454942918765409520323955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5636628612510273013549303 8454942918765409520323955)
          ·
            refine ⟨12682414378148114280485933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8454942918765409520323955 12682414378148114280485933)
            ·
              refine ⟨4755905391805542855182225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12682414378148114280485933 4755905391805542855182225)
              ·
                refine ⟨3566929043854157141386669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4755905391805542855182225 3566929043854157141386669)
                ·
                  refine ⟨1337598391445308928020001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3566929043854157141386669 1337598391445308928020001)
                  ·
                    refine ⟨1003198793583981696015001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1337598391445308928020001 1003198793583981696015001)
                    ·
                      refine ⟨752399095187986272011251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1003198793583981696015001 752399095187986272011251)
                      ·
                        rfl

theorem cell23_1465292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_1465292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465292 prefixEnd_1465292 := by exact prefixLift 1465292
  have htrace : WordTrace (prefixWord ++ tailWord_1465292) baseStart_1465292 baseEnd_1465292 := by
    simpa [prefixWord, tailWord_1465292, baseEnd_1465292] using wordTrace_append hprefix tailTrace_1465292
  have hstable : (prefixWord ++ tailWord_1465292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465292).length < 2 ^ (prefixWord ++ tailWord_1465292).sum := by decide
  have hdescent : baseEnd_1465292 < baseStart_1465292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465309 : List Nat := [1, 4, 3, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_1465309 : Nat := 118140960795 + 1465309 * 2 ^ 59
def prefixEnd_1465309 : Nat := 4983230072969 + 3 ^ 40 * 1465309 * 2
def baseEnd_1465309 : Nat := 752407824359112705498673

theorem tailTrace_1465309 : CollatzResearch.WordTrace tailWord_1465309 prefixEnd_1465309 752407824359112705498673 := by
  unfold tailWord_1465309
  simp only [CollatzResearch.WordTrace]
  refine ⟨53444209848443222698502981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35629473232295481799001987 53444209848443222698502981)
  ·
    refine ⟨10020789346583104255969309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53444209848443222698502981 10020789346583104255969309)
    ·
      refine ⟨3757796004968664095988491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10020789346583104255969309 3757796004968664095988491)
      ·
        refine ⟨5636694007452996143982737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3757796004968664095988491 5636694007452996143982737)
        ·
          refine ⟨4227520505589747107987053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5636694007452996143982737 4227520505589747107987053)
          ·
            refine ⟨1585320189596155165495145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4227520505589747107987053 1585320189596155165495145)
            ·
              refine ⟨1188990142197116374121359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1585320189596155165495145 1188990142197116374121359)
              ·
                refine ⟨1783485213295674561182039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188990142197116374121359 1783485213295674561182039)
                ·
                  refine ⟨2675227819943511841773059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783485213295674561182039 2675227819943511841773059)
                  ·
                    refine ⟨4012841729915267762659589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2675227819943511841773059 4012841729915267762659589)
                    ·
                      refine ⟨752407824359112705498673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4012841729915267762659589 752407824359112705498673)
                      ·
                        rfl

theorem cell23_1465309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_1465309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465309 prefixEnd_1465309 := by exact prefixLift 1465309
  have htrace : WordTrace (prefixWord ++ tailWord_1465309) baseStart_1465309 baseEnd_1465309 := by
    simpa [prefixWord, tailWord_1465309, baseEnd_1465309] using wordTrace_append hprefix tailTrace_1465309
  have hstable : (prefixWord ++ tailWord_1465309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465309).length < 2 ^ (prefixWord ++ tailWord_1465309).sum := by decide
  have hdescent : baseEnd_1465309 < baseStart_1465309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465346 : List Nat := [3, 4, 1, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1465346 : Nat := 118140960795 + 1465346 * 2 ^ 59
def prefixEnd_1465346 : Nat := 4983230072969 + 3 ^ 40 * 1465346 * 2
def baseEnd_1465346 : Nat := 752426823143329060736003

theorem tailTrace_1465346 : CollatzResearch.WordTrace tailWord_1465346 prefixEnd_1465346 752426823143329060736003 := by
  unfold tailWord_1465346
  simp only [CollatzResearch.WordTrace]
  refine ⟨13361389837327294504399973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35630372899539452011733261 13361389837327294504399973)
  ·
    refine ⟨2505260594498867719574995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13361389837327294504399973 2505260594498867719574995)
    ·
      refine ⟨3757890891748301579362493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2505260594498867719574995 3757890891748301579362493)
      ·
        refine ⟨1409209084405613092260935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3757890891748301579362493 1409209084405613092260935)
        ·
          refine ⟨2113813626608419638391403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1409209084405613092260935 2113813626608419638391403)
          ·
            refine ⟨3170720439912629457587105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2113813626608419638391403 3170720439912629457587105)
            ·
              refine ⟨2378040329934472093190329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3170720439912629457587105 2378040329934472093190329)
              ·
                refine ⟨1783530247450854069892747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2378040329934472093190329 1783530247450854069892747)
                ·
                  refine ⟨2675295371176281104839121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783530247450854069892747 2675295371176281104839121)
                  ·
                    refine ⟨2006471528382210828629341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2675295371176281104839121 2006471528382210828629341)
                    ·
                      refine ⟨752426823143329060736003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2006471528382210828629341 752426823143329060736003)
                      ·
                        rfl

theorem cell23_1465346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1465346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465346 prefixEnd_1465346 := by exact prefixLift 1465346
  have htrace : WordTrace (prefixWord ++ tailWord_1465346) baseStart_1465346 baseEnd_1465346 := by
    simpa [prefixWord, tailWord_1465346, baseEnd_1465346] using wordTrace_append hprefix tailTrace_1465346
  have hstable : (prefixWord ++ tailWord_1465346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465346).length < 2 ^ (prefixWord ++ tailWord_1465346).sum := by decide
  have hdescent : baseEnd_1465346 < baseStart_1465346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465352 : List Nat := [2, 1, 3, 2, 1, 3, 1, 4, 1, 3, 2]
def baseStart_1465352 : Nat := 118140960795 + 1465352 * 2 ^ 59
def prefixEnd_1465352 : Nat := 4983230072969 + 3 ^ 40 * 1465352 * 2
def baseEnd_1465352 : Nat := 752429904027256037260975

theorem tailTrace_1465352 : CollatzResearch.WordTrace tailWord_1465352 prefixEnd_1465352 752429904027256037260975 := by
  unfold tailWord_1465352
  simp only [CollatzResearch.WordTrace]
  refine ⟨26722889093643720521159155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35630518791524960694878873 26722889093643720521159155)
  ·
    refine ⟨40084333640465580781738733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26722889093643720521159155 40084333640465580781738733)
    ·
      refine ⟨15031625115174592793152025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40084333640465580781738733 15031625115174592793152025)
      ·
        refine ⟨11273718836380944594864019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15031625115174592793152025 11273718836380944594864019)
        ·
          refine ⟨16910578254571416892296029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11273718836380944594864019 16910578254571416892296029)
          ·
            refine ⟨6341466845464281334611011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16910578254571416892296029 6341466845464281334611011)
            ·
              refine ⟨9512200268196422001916517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6341466845464281334611011 9512200268196422001916517)
              ·
                refine ⟨1783537550286829125359347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9512200268196422001916517 1783537550286829125359347)
                ·
                  refine ⟨2675306325430243688039021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783537550286829125359347 2675306325430243688039021)
                  ·
                    refine ⟨1003239872036341383014633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2675306325430243688039021 1003239872036341383014633)
                    ·
                      refine ⟨752429904027256037260975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1003239872036341383014633 752429904027256037260975)
                      ·
                        rfl

theorem cell23_1465352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_1465352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465352 prefixEnd_1465352 := by exact prefixLift 1465352
  have htrace : WordTrace (prefixWord ++ tailWord_1465352) baseStart_1465352 baseEnd_1465352 := by
    simpa [prefixWord, tailWord_1465352, baseEnd_1465352] using wordTrace_append hprefix tailTrace_1465352
  have hstable : (prefixWord ++ tailWord_1465352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465352).length < 2 ^ (prefixWord ++ tailWord_1465352).sum := by decide
  have hdescent : baseEnd_1465352 < baseStart_1465352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465368 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1465368 : Nat := 118140960795 + 1465368 * 2 ^ 59
def prefixEnd_1465368 : Nat := 4983230072969 + 3 ^ 40 * 1465368 * 2
def baseEnd_1465368 : Nat := 752438119717727974660901

theorem tailTrace_1465368 : CollatzResearch.WordTrace tailWord_1465368 prefixEnd_1465368 752438119717727974660901 := by
  unfold tailWord_1465368
  simp only [CollatzResearch.WordTrace]
  refine ⟨26723180877614737887450379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35630907836819650516600505 26723180877614737887450379)
  ·
    refine ⟨40084771316422106831175569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26723180877614737887450379 40084771316422106831175569)
    ·
      refine ⟨30063578487316580123381677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40084771316422106831175569 30063578487316580123381677)
      ·
        refine ⟨11273841932743717546268129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30063578487316580123381677 11273841932743717546268129)
        ·
          refine ⟨8455381449557788159701097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11273841932743717546268129 8455381449557788159701097)
          ·
            refine ⟨6341536087168341119775823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8455381449557788159701097 6341536087168341119775823)
            ·
              refine ⟨9512304130752511679663735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6341536087168341119775823 9512304130752511679663735)
              ·
                refine ⟨14268456196128767519495603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9512304130752511679663735 14268456196128767519495603)
                ·
                  refine ⟨21402684294193151279243405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14268456196128767519495603 21402684294193151279243405)
                  ·
                    refine ⟨8026006610322431729716277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21402684294193151279243405 8026006610322431729716277)
                    ·
                      refine ⟨752438119717727974660901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8026006610322431729716277 752438119717727974660901)
                      ·
                        rfl

theorem cell23_1465368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1465368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465368 prefixEnd_1465368 := by exact prefixLift 1465368
  have htrace : WordTrace (prefixWord ++ tailWord_1465368) baseStart_1465368 baseEnd_1465368 := by
    simpa [prefixWord, tailWord_1465368, baseEnd_1465368] using wordTrace_append hprefix tailTrace_1465368
  have hstable : (prefixWord ++ tailWord_1465368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465368).length < 2 ^ (prefixWord ++ tailWord_1465368).sum := by decide
  have hdescent : baseEnd_1465368 < baseStart_1465368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465418 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 1, 7]
def baseStart_1465418 : Nat := 118140960795 + 1465418 * 2 ^ 59
def prefixEnd_1465418 : Nat := 4983230072969 + 3 ^ 40 * 1465418 * 2
def baseEnd_1465418 : Nat := 250821264583484259678557

theorem tailTrace_1465418 : CollatzResearch.WordTrace tailWord_1465418 prefixEnd_1465418 250821264583484259678557 := by
  unfold tailWord_1465418
  simp only [CollatzResearch.WordTrace]
  refine ⟨13362046351262083578555227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35632123603365556209480605 13362046351262083578555227)
  ·
    refine ⟨20043069526893125367832841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13362046351262083578555227 20043069526893125367832841)
    ·
      refine ⟨15032302145169844025874631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20043069526893125367832841 15032302145169844025874631)
      ·
        refine ⟨22548453217754766038811947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15032302145169844025874631 22548453217754766038811947)
        ·
          refine ⟨33822679826632149058217921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22548453217754766038811947 33822679826632149058217921)
          ·
            refine ⟨25367009869974111793663441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33822679826632149058217921 25367009869974111793663441)
            ·
              refine ⟨19025257402480583845247581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25367009869974111793663441 19025257402480583845247581)
              ·
                refine ⟨7134471525930218941967843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19025257402480583845247581 7134471525930218941967843)
                ·
                  refine ⟨10701707288895328412951765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7134471525930218941967843 10701707288895328412951765)
                  ·
                    refine ⟨250821264583484259678557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10701707288895328412951765 250821264583484259678557)
                    ·
                      rfl

theorem cell23_1465418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_1465418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465418 prefixEnd_1465418 := by exact prefixLift 1465418
  have htrace : WordTrace (prefixWord ++ tailWord_1465418) baseStart_1465418 baseEnd_1465418 := by
    simpa [prefixWord, tailWord_1465418, baseEnd_1465418] using wordTrace_append hprefix tailTrace_1465418
  have hstable : (prefixWord ++ tailWord_1465418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465418).length < 2 ^ (prefixWord ++ tailWord_1465418).sum := by decide
  have hdescent : baseEnd_1465418 < baseStart_1465418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465475 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 3]
def baseStart_1465475 : Nat := 118140960795 + 1465475 * 2 ^ 59
def prefixEnd_1465475 : Nat := 4983230072969 + 3 ^ 40 * 1465475 * 2
def baseEnd_1465475 : Nat := 752493062147759056022909

theorem tailTrace_1465475 : CollatzResearch.WordTrace tailWord_1465475 prefixEnd_1465475 752493062147759056022909 := by
  unfold tailWord_1465475
  simp only [CollatzResearch.WordTrace]
  refine ⟨53450264365841833049045879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35633509577227888699363919 53450264365841833049045879)
  ·
    refine ⟨80175396548762749573568819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53450264365841833049045879 80175396548762749573568819)
    ·
      refine ⟨120263094823144124360353229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80175396548762749573568819 120263094823144124360353229)
      ·
        refine ⟨45098660558679046635132461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120263094823144124360353229 45098660558679046635132461)
        ·
          refine ⟨16911997709504642488174673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45098660558679046635132461 16911997709504642488174673)
          ·
            refine ⟨12683998282128481866131005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16911997709504642488174673 12683998282128481866131005)
            ·
              refine ⟨4756499355798180699799127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12683998282128481866131005 4756499355798180699799127)
              ·
                refine ⟨7134749033697271049698691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4756499355798180699799127 7134749033697271049698691)
                ·
                  refine ⟨10702123550545906574548037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7134749033697271049698691 10702123550545906574548037)
                  ·
                    refine ⟨2006648165727357482727757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10702123550545906574548037 2006648165727357482727757)
                    ·
                      refine ⟨752493062147759056022909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2006648165727357482727757 752493062147759056022909)
                      ·
                        rfl

theorem cell23_1465475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_1465475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465475 prefixEnd_1465475 := by exact prefixLift 1465475
  have htrace : WordTrace (prefixWord ++ tailWord_1465475) baseStart_1465475 baseEnd_1465475 := by
    simpa [prefixWord, tailWord_1465475, baseEnd_1465475] using wordTrace_append hprefix tailTrace_1465475
  have hstable : (prefixWord ++ tailWord_1465475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465475).length < 2 ^ (prefixWord ++ tailWord_1465475).sum := by decide
  have hdescent : baseEnd_1465475 < baseStart_1465475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465495 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 8]
def baseStart_1465495 : Nat := 118140960795 + 1465495 * 2 ^ 59
def prefixEnd_1465495 : Nat := 4983230072969 + 3 ^ 40 * 1465495 * 2
def baseEnd_1465495 : Nat := 83611481306760997530313

theorem tailTrace_1465495 : CollatzResearch.WordTrace tailWord_1465495 prefixEnd_1465495 83611481306760997530313 := by
  unfold tailWord_1465495
  simp only [CollatzResearch.WordTrace]
  refine ⟨53450993825769376464773939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35633995883846250976515959 53450993825769376464773939)
  ·
    refine ⟨80176490738654064697160909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53450993825769376464773939 80176490738654064697160909)
    ·
      refine ⟨30066184026995274261435341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80176490738654064697160909 30066184026995274261435341)
      ·
        refine ⟨11274819010123227848038253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30066184026995274261435341 11274819010123227848038253)
        ·
          refine ⟨4228057128796210443014345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11274819010123227848038253 4228057128796210443014345)
          ·
            refine ⟨3171042846597157832260759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4228057128796210443014345 3171042846597157832260759)
            ·
              refine ⟨4756564269895736748391139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3171042846597157832260759 4756564269895736748391139)
              ·
                refine ⟨7134846404843605122586709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4756564269895736748391139 7134846404843605122586709)
                ·
                  refine ⟨83611481306760997530313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7134846404843605122586709 83611481306760997530313)
                  ·
                    rfl

theorem cell23_1465495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 8].length) (baseStart_1465495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465495 prefixEnd_1465495 := by exact prefixLift 1465495
  have htrace : WordTrace (prefixWord ++ tailWord_1465495) baseStart_1465495 baseEnd_1465495 := by
    simpa [prefixWord, tailWord_1465495, baseEnd_1465495] using wordTrace_append hprefix tailTrace_1465495
  have hstable : (prefixWord ++ tailWord_1465495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465495).length < 2 ^ (prefixWord ++ tailWord_1465495).sum := by decide
  have hdescent : baseEnd_1465495 < baseStart_1465495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465539 : List Nat := [1, 1, 1, 3, 1, 1, 1, 9, 1, 1, 3]
def baseStart_1465539 : Nat := 118140960795 + 1465539 * 2 ^ 59
def prefixEnd_1465539 : Nat := 4983230072969 + 3 ^ 40 * 1465539 * 2
def baseEnd_1465539 : Nat := 752525924909646805622615

theorem tailTrace_1465539 : CollatzResearch.WordTrace tailWord_1465539 prefixEnd_1465539 752525924909646805622615 := by
  unfold tailWord_1465539
  simp only [CollatzResearch.WordTrace]
  refine ⟨53452598637609971979375671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35635065758406647986250447 53452598637609971979375671)
  ·
    refine ⟨80178897956414957969063507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53452598637609971979375671 80178897956414957969063507)
    ·
      refine ⟨120268346934622436953595261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80178897956414957969063507 120268346934622436953595261)
      ·
        refine ⟨45100630100483413857598223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120268346934622436953595261 45100630100483413857598223)
        ·
          refine ⟨67650945150725120786397335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45100630100483413857598223 67650945150725120786397335)
          ·
            refine ⟨101476417726087681179596003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67650945150725120786397335 101476417726087681179596003)
            ·
              refine ⟨152214626589131521769394005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101476417726087681179596003 152214626589131521769394005)
              ·
                refine ⟨891882577670692510367543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 152214626589131521769394005 891882577670692510367543)
                ·
                  refine ⟨1337823866506038765551315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 891882577670692510367543 1337823866506038765551315)
                  ·
                    refine ⟨2006735799759058148326973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1337823866506038765551315 2006735799759058148326973)
                    ·
                      refine ⟨752525924909646805622615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2006735799759058148326973 752525924909646805622615)
                      ·
                        rfl

theorem cell23_1465539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 1, 1, 3].length) (baseStart_1465539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465539 prefixEnd_1465539 := by exact prefixLift 1465539
  have htrace : WordTrace (prefixWord ++ tailWord_1465539) baseStart_1465539 baseEnd_1465539 := by
    simpa [prefixWord, tailWord_1465539, baseEnd_1465539] using wordTrace_append hprefix tailTrace_1465539
  have hstable : (prefixWord ++ tailWord_1465539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465539).length < 2 ^ (prefixWord ++ tailWord_1465539).sum := by decide
  have hdescent : baseEnd_1465539 < baseStart_1465539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465579 : List Nat := [1, 1, 1, 1, 2, 8, 1, 2, 1, 1, 4]
def baseStart_1465579 : Nat := 118140960795 + 1465579 * 2 ^ 59
def prefixEnd_1465579 : Nat := 4983230072969 + 3 ^ 40 * 1465579 * 2
def baseEnd_1465579 : Nat := 752546464135826649122431

theorem tailTrace_1465579 : CollatzResearch.WordTrace tailWord_1465579 prefixEnd_1465579 752546464135826649122431 := by
  unfold tailWord_1465579
  simp only [CollatzResearch.WordTrace]
  refine ⟨53454057557465058810831791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35636038371643372540554527 53454057557465058810831791)
  ·
    refine ⟨80181086336197588216247687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53454057557465058810831791 80181086336197588216247687)
    ·
      refine ⟨120271629504296382324371531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80181086336197588216247687 120271629504296382324371531)
      ·
        refine ⟨180407444256444573486557297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120271629504296382324371531 180407444256444573486557297)
        ·
          refine ⟨135305583192333430114917973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180407444256444573486557297 135305583192333430114917973)
          ·
            refine ⟨1585612303035157384159195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 135305583192333430114917973 1585612303035157384159195)
            ·
              refine ⟨2378418454552736076238793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1585612303035157384159195 2378418454552736076238793)
              ·
                refine ⟨1783813840914552057179095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2378418454552736076238793 1783813840914552057179095)
                ·
                  refine ⟨2675720761371828085768643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783813840914552057179095 2675720761371828085768643)
                  ·
                    refine ⟨4013581142057742128652965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2675720761371828085768643 4013581142057742128652965)
                    ·
                      refine ⟨752546464135826649122431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4013581142057742128652965 752546464135826649122431)
                      ·
                        rfl

theorem cell23_1465579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 1, 4].length) (baseStart_1465579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465579 prefixEnd_1465579 := by exact prefixLift 1465579
  have htrace : WordTrace (prefixWord ++ tailWord_1465579) baseStart_1465579 baseEnd_1465579 := by
    simpa [prefixWord, tailWord_1465579, baseEnd_1465579] using wordTrace_append hprefix tailTrace_1465579
  have hstable : (prefixWord ++ tailWord_1465579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465579).length < 2 ^ (prefixWord ++ tailWord_1465579).sum := by decide
  have hdescent : baseEnd_1465579 < baseStart_1465579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465596 : List Nat := [2, 2, 2, 1, 5, 1, 3, 1, 1, 1, 4]
def baseStart_1465596 : Nat := 118140960795 + 1465596 * 2 ^ 59
def prefixEnd_1465596 : Nat := 4983230072969 + 3 ^ 40 * 1465596 * 2
def baseEnd_1465596 : Nat := 752555193306953082609853

theorem tailTrace_1465596 : CollatzResearch.WordTrace tailWord_1465596 prefixEnd_1465596 752555193306953082609853 := by
  unfold tailWord_1465596
  simp only [CollatzResearch.WordTrace]
  refine ⟨26727338799201735357100321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35636451732268980476133761 26727338799201735357100321)
  ·
    refine ⟨20045504099401301517825241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26727338799201735357100321 20045504099401301517825241)
    ·
      refine ⟨15034128074550976138368931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20045504099401301517825241 15034128074550976138368931)
      ·
        refine ⟨22551192111826464207553397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15034128074550976138368931 22551192111826464207553397)
        ·
          refine ⟨2114174260483731019458131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22551192111826464207553397 2114174260483731019458131)
          ·
            refine ⟨3171261390725596529187197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2114174260483731019458131 3171261390725596529187197)
            ·
              refine ⟨1189223021522098698445199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3171261390725596529187197 1189223021522098698445199)
              ·
                refine ⟨1783834532283148047667799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189223021522098698445199 1783834532283148047667799)
                ·
                  refine ⟨2675751798424722071501699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783834532283148047667799 2675751798424722071501699)
                  ·
                    refine ⟨4013627697637083107252549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2675751798424722071501699 4013627697637083107252549)
                    ·
                      refine ⟨752555193306953082609853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4013627697637083107252549 752555193306953082609853)
                      ·
                        rfl

theorem cell23_1465596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_1465596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465596 prefixEnd_1465596 := by exact prefixLift 1465596
  have htrace : WordTrace (prefixWord ++ tailWord_1465596) baseStart_1465596 baseEnd_1465596 := by
    simpa [prefixWord, tailWord_1465596, baseEnd_1465596] using wordTrace_append hprefix tailTrace_1465596
  have hstable : (prefixWord ++ tailWord_1465596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465596).length < 2 ^ (prefixWord ++ tailWord_1465596).sum := by decide
  have hdescent : baseEnd_1465596 < baseStart_1465596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465602 : List Nat := [3, 4, 1, 1, 3, 11]
def baseStart_1465602 : Nat := 118140960795 + 1465602 * 2 ^ 59
def prefixEnd_1465602 : Nat := 4983230072969 + 3 ^ 40 * 1465602 * 2
def baseEnd_1465602 : Nat := 3096947630415144276275

theorem tailTrace_1465602 : CollatzResearch.WordTrace tailWord_1465602 prefixEnd_1465602 3096947630415144276275 := by
  unfold tailWord_1465602
  simp only [CollatzResearch.WordTrace]
  refine ⟨13363724109095433434729765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35636597624254489159279373 13363724109095433434729765)
  ·
    refine ⟨2505698270455393769011831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13363724109095433434729765 2505698270455393769011831)
    ·
      refine ⟨3758547405683090653517747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2505698270455393769011831 3758547405683090653517747)
      ·
        refine ⟨5637821108524635980276621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3758547405683090653517747 5637821108524635980276621)
        ·
          refine ⟨2114182915696738492603733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5637821108524635980276621 2114182915696738492603733)
          ·
            refine ⟨3096947630415144276275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2114182915696738492603733 3096947630415144276275)
            ·
              rfl

theorem cell23_1465602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 11].length) (baseStart_1465602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465602 prefixEnd_1465602 := by exact prefixLift 1465602
  have htrace : WordTrace (prefixWord ++ tailWord_1465602) baseStart_1465602 baseEnd_1465602 := by
    simpa [prefixWord, tailWord_1465602, baseEnd_1465602] using wordTrace_append hprefix tailTrace_1465602
  have hstable : (prefixWord ++ tailWord_1465602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465602).length < 2 ^ (prefixWord ++ tailWord_1465602).sum := by decide
  have hdescent : baseEnd_1465602 < baseStart_1465602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465629 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_1465629 : Nat := 118140960795 + 1465629 * 2 ^ 59
def prefixEnd_1465629 : Nat := 4983230072969 + 3 ^ 40 * 1465629 * 2
def baseEnd_1465629 : Nat := 752572138168551453497201

theorem tailTrace_1465629 : CollatzResearch.WordTrace tailWord_1465629 prefixEnd_1465629 752572138168551453497201 := by
  unfold tailWord_1465629
  simp only [CollatzResearch.WordTrace]
  refine ⟨53455881207283917350151941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35637254138189278233434627 53455881207283917350151941)
  ·
    refine ⟨10022977726365734503153489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53455881207283917350151941 10022977726365734503153489)
    ·
      refine ⟨7517233294774300877365117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10022977726365734503153489 7517233294774300877365117)
      ·
        refine ⟨2818962485540362829011919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7517233294774300877365117 2818962485540362829011919)
        ·
          refine ⟨4228443728310544243517879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2818962485540362829011919 4228443728310544243517879)
          ·
            refine ⟨6342665592465816365276819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4228443728310544243517879 6342665592465816365276819)
            ·
              refine ⟨9513998388698724547915229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6342665592465816365276819 9513998388698724547915229)
              ·
                refine ⟨3567749395762021705468211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9513998388698724547915229 3567749395762021705468211)
                ·
                  refine ⟨5351624093643032558202317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3567749395762021705468211 5351624093643032558202317)
                  ·
                    refine ⟨2006859035116137209325869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5351624093643032558202317 2006859035116137209325869)
                    ·
                      refine ⟨752572138168551453497201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2006859035116137209325869 752572138168551453497201)
                      ·
                        rfl

theorem cell23_1465629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_1465629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465629 prefixEnd_1465629 := by exact prefixLift 1465629
  have htrace : WordTrace (prefixWord ++ tailWord_1465629) baseStart_1465629 baseEnd_1465629 := by
    simpa [prefixWord, tailWord_1465629, baseEnd_1465629] using wordTrace_append hprefix tailTrace_1465629
  have hstable : (prefixWord ++ tailWord_1465629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465629).length < 2 ^ (prefixWord ++ tailWord_1465629).sum := by decide
  have hdescent : baseEnd_1465629 < baseStart_1465629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465630 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_1465630 : Nat := 118140960795 + 1465630 * 2 ^ 59
def prefixEnd_1465630 : Nat := 4983230072969 + 3 ^ 40 * 1465630 * 2
def baseEnd_1465630 : Nat := 752572651649205949584697

theorem tailTrace_1465630 : CollatzResearch.WordTrace tailWord_1465630 prefixEnd_1465630 752572651649205949584697 := by
  unfold tailWord_1465630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6681989710035036815117293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35637278453520196347292229 6681989710035036815117293)
  ·
    refine ⟨2505746141263138805668985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6681989710035036815117293 2505746141263138805668985)
    ·
      refine ⟨1879309605947354104251739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2505746141263138805668985 1879309605947354104251739)
      ·
        refine ⟨2818964408921031156377609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1879309605947354104251739 2818964408921031156377609)
        ·
          refine ⟨2114223306690773367283207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2818964408921031156377609 2114223306690773367283207)
          ·
            refine ⟨3171334960036160050924811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2114223306690773367283207 3171334960036160050924811)
            ·
              refine ⟨4757002440054240076387217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3171334960036160050924811 4757002440054240076387217)
              ·
                refine ⟨3567751830040680057290413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4757002440054240076387217 3567751830040680057290413)
                ·
                  refine ⟨1337906936265255021483905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3567751830040680057290413 1337906936265255021483905)
                  ·
                    refine ⟨1003430202198941266112929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1337906936265255021483905 1003430202198941266112929)
                    ·
                      refine ⟨752572651649205949584697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1003430202198941266112929 752572651649205949584697)
                      ·
                        rfl

theorem cell23_1465630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_1465630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465630 prefixEnd_1465630 := by exact prefixLift 1465630
  have htrace : WordTrace (prefixWord ++ tailWord_1465630) baseStart_1465630 baseEnd_1465630 := by
    simpa [prefixWord, tailWord_1465630, baseEnd_1465630] using wordTrace_append hprefix tailTrace_1465630
  have hstable : (prefixWord ++ tailWord_1465630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465630).length < 2 ^ (prefixWord ++ tailWord_1465630).sum := by decide
  have hdescent : baseEnd_1465630 < baseStart_1465630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465662 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_1465662 : Nat := 118140960795 + 1465662 * 2 ^ 59
def prefixEnd_1465662 : Nat := 4983230072969 + 3 ^ 40 * 1465662 * 2
def baseEnd_1465662 : Nat := 250863027676716608128183

theorem tailTrace_1465662 : CollatzResearch.WordTrace tailWord_1465662 prefixEnd_1465662 250863027676716608128183 := by
  unfold tailWord_1465662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6682135602020545498262905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35638056544109575990735493 6682135602020545498262905)
  ·
    refine ⟨5011601701515409123697179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6682135602020545498262905 5011601701515409123697179)
    ·
      refine ⟨7517402552273113685545769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5011601701515409123697179 7517402552273113685545769)
      ·
        refine ⟨5638051914204835264159327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7517402552273113685545769 5638051914204835264159327)
        ·
          refine ⟨8457077871307252896238991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5638051914204835264159327 8457077871307252896238991)
          ·
            refine ⟨12685616806960879344358487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8457077871307252896238991 12685616806960879344358487)
            ·
              refine ⟨19028425210441319016537731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12685616806960879344358487 19028425210441319016537731)
              ·
                refine ⟨28542637815661978524806597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19028425210441319016537731 28542637815661978524806597)
                ·
                  refine ⟨5351744590436620973401237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28542637815661978524806597 5351744590436620973401237)
                  ·
                    refine ⟨250863027676716608128183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5351744590436620973401237 250863027676716608128183)
                    ·
                      rfl

theorem cell23_1465662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_1465662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465662 prefixEnd_1465662 := by exact prefixLift 1465662
  have htrace : WordTrace (prefixWord ++ tailWord_1465662) baseStart_1465662 baseEnd_1465662 := by
    simpa [prefixWord, tailWord_1465662, baseEnd_1465662] using wordTrace_append hprefix tailTrace_1465662
  have hstable : (prefixWord ++ tailWord_1465662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465662).length < 2 ^ (prefixWord ++ tailWord_1465662).sum := by decide
  have hdescent : baseEnd_1465662 < baseStart_1465662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465722 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 2, 5]
def baseStart_1465722 : Nat := 118140960795 + 1465722 * 2 ^ 59
def prefixEnd_1465722 : Nat := 4983230072969 + 3 ^ 40 * 1465722 * 2
def baseEnd_1465722 : Nat := 250873297289806529878091

theorem tailTrace_1465722 : CollatzResearch.WordTrace tailWord_1465722 prefixEnd_1465722 250873297289806529878091 := by
  unfold tailWord_1465722
  simp only [CollatzResearch.WordTrace]
  refine ⟨13364818298986748558321855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35639515463964662822191613 13364818298986748558321855)
  ·
    refine ⟨20047227448480122837482783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13364818298986748558321855 20047227448480122837482783)
    ·
      refine ⟨30070841172720184256224175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20047227448480122837482783 30070841172720184256224175)
      ·
        refine ⟨45106261759080276384336263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30070841172720184256224175 45106261759080276384336263)
        ·
          refine ⟨67659392638620414576504395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45106261759080276384336263 67659392638620414576504395)
          ·
            refine ⟨101489088957930621864756593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67659392638620414576504395 101489088957930621864756593)
            ·
              refine ⟨76116816718447966398567445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101489088957930621864756593 76116816718447966398567445)
              ·
                refine ⟨3567975783677248424932849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76116816718447966398567445 3567975783677248424932849)
                ·
                  refine ⟨2675981837757936318699637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3567975783677248424932849 2675981837757936318699637)
                  ·
                    refine ⟨250873297289806529878091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2675981837757936318699637 250873297289806529878091)
                    ·
                      rfl

theorem cell23_1465722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_1465722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465722 prefixEnd_1465722 := by exact prefixLift 1465722
  have htrace : WordTrace (prefixWord ++ tailWord_1465722) baseStart_1465722 baseEnd_1465722 := by
    simpa [prefixWord, tailWord_1465722, baseEnd_1465722] using wordTrace_append hprefix tailTrace_1465722
  have hstable : (prefixWord ++ tailWord_1465722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465722).length < 2 ^ (prefixWord ++ tailWord_1465722).sum := by decide
  have hdescent : baseEnd_1465722 < baseStart_1465722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465732 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1465732 : Nat := 118140960795 + 1465732 * 2 ^ 59
def prefixEnd_1465732 : Nat := 4983230072969 + 3 ^ 40 * 1465732 * 2
def baseEnd_1465732 : Nat := 752625026675964550509227

theorem tailTrace_1465732 : CollatzResearch.WordTrace tailWord_1465732 prefixEnd_1465732 752625026675964550509227 := by
  unfold tailWord_1465732
  simp only [CollatzResearch.WordTrace]
  refine ⟨26729818962955382970575725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35639758617273843960767633 26729818962955382970575725)
  ·
    refine ⟨10023682111108268613965897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26729818962955382970575725 10023682111108268613965897)
    ·
      refine ⟨7517761583331201460474423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10023682111108268613965897 7517761583331201460474423)
      ·
        refine ⟨11276642374996802190711635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7517761583331201460474423 11276642374996802190711635)
        ·
          refine ⟨16914963562495203286067453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11276642374996802190711635 16914963562495203286067453)
          ·
            refine ⟨6343111335935701232275295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16914963562495203286067453 6343111335935701232275295)
            ·
              refine ⟨9514667003903551848412943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6343111335935701232275295 9514667003903551848412943)
              ·
                refine ⟨14272000505855327772619415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9514667003903551848412943 14272000505855327772619415)
                ·
                  refine ⟨21408000758782991658929123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14272000505855327772619415 21408000758782991658929123)
                  ·
                    refine ⟨32112001138174487488393685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21408000758782991658929123 32112001138174487488393685)
                    ·
                      refine ⟨752625026675964550509227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32112001138174487488393685 752625026675964550509227)
                      ·
                        rfl

theorem cell23_1465732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1465732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465732 prefixEnd_1465732 := by exact prefixLift 1465732
  have htrace : WordTrace (prefixWord ++ tailWord_1465732) baseStart_1465732 baseEnd_1465732 := by
    simpa [prefixWord, tailWord_1465732, baseEnd_1465732] using wordTrace_append hprefix tailTrace_1465732
  have hstable : (prefixWord ++ tailWord_1465732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465732).length < 2 ^ (prefixWord ++ tailWord_1465732).sum := by decide
  have hdescent : baseEnd_1465732 < baseStart_1465732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465737 : List Nat := [1, 2, 1, 1, 8, 1, 2, 1, 2, 2, 2]
def baseStart_1465737 : Nat := 118140960795 + 1465737 * 2 ^ 59
def prefixEnd_1465737 : Nat := 4983230072969 + 3 ^ 40 * 1465737 * 2
def baseEnd_1465737 : Nat := 752627594079237030946705

theorem tailTrace_1465737 : CollatzResearch.WordTrace tailWord_1465737 prefixEnd_1465737 752627594079237030946705 := by
  unfold tailWord_1465737
  simp only [CollatzResearch.WordTrace]
  refine ⟨53459820290892651795083465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35639880193928434530055643 53459820290892651795083465)
  ·
    refine ⟨40094865218169488846312599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53459820290892651795083465 40094865218169488846312599)
    ·
      refine ⟨60142297827254233269468899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40094865218169488846312599 60142297827254233269468899)
      ·
        refine ⟨90213446740881349904203349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60142297827254233269468899 90213446740881349904203349)
        ·
          refine ⟨1057188828994703319189883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 90213446740881349904203349 1057188828994703319189883)
          ·
            refine ⟨1585783243492054978784825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057188828994703319189883 1585783243492054978784825)
            ·
              refine ⟨1189337432619041234088619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1585783243492054978784825 1189337432619041234088619)
              ·
                refine ⟨1784006148928561851132929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189337432619041234088619 1784006148928561851132929)
                ·
                  refine ⟨1338004611696421388349697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1784006148928561851132929 1338004611696421388349697)
                  ·
                    refine ⟨1003503458772316041262273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1338004611696421388349697 1003503458772316041262273)
                    ·
                      refine ⟨752627594079237030946705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1003503458772316041262273 752627594079237030946705)
                      ·
                        rfl

theorem cell23_1465737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 2, 2, 2].length) (baseStart_1465737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465737 prefixEnd_1465737 := by exact prefixLift 1465737
  have htrace : WordTrace (prefixWord ++ tailWord_1465737) baseStart_1465737 baseEnd_1465737 := by
    simpa [prefixWord, tailWord_1465737, baseEnd_1465737] using wordTrace_append hprefix tailTrace_1465737
  have hstable : (prefixWord ++ tailWord_1465737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465737).length < 2 ^ (prefixWord ++ tailWord_1465737).sum := by decide
  have hdescent : baseEnd_1465737 < baseStart_1465737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465759 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1465759 : Nat := 118140960795 + 1465759 * 2 ^ 59
def prefixEnd_1465759 : Nat := 4983230072969 + 3 ^ 40 * 1465759 * 2
def baseEnd_1465759 : Nat := 752638890653635944871603

theorem tailTrace_1465759 : CollatzResearch.WordTrace tailWord_1465759 prefixEnd_1465759 752638890653635944871603 := by
  unfold tailWord_1465759
  simp only [CollatzResearch.WordTrace]
  refine ⟨53460622696812949552384331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35640415131208633034922887 53460622696812949552384331)
  ·
    refine ⟨80190934045219424328576497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53460622696812949552384331 80190934045219424328576497)
    ·
      refine ⟨60143200533914568246432373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80190934045219424328576497 60143200533914568246432373)
      ·
        refine ⟨5638425050054490773103035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60143200533914568246432373 5638425050054490773103035)
        ·
          refine ⟨8457637575081736159654553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5638425050054490773103035 8457637575081736159654553)
          ·
            refine ⟨6343228181311302119740915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8457637575081736159654553 6343228181311302119740915)
            ·
              refine ⟨9514842271966953179611373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6343228181311302119740915 9514842271966953179611373)
              ·
                refine ⟨3568065851987607442354265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9514842271966953179611373 3568065851987607442354265)
                ·
                  refine ⟨2676049388990705581765699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3568065851987607442354265 2676049388990705581765699)
                  ·
                    refine ⟨4014074083486058372648549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2676049388990705581765699 4014074083486058372648549)
                    ·
                      refine ⟨752638890653635944871603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4014074083486058372648549 752638890653635944871603)
                      ·
                        rfl

theorem cell23_1465759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1465759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465759 prefixEnd_1465759 := by exact prefixLift 1465759
  have htrace : WordTrace (prefixWord ++ tailWord_1465759) baseStart_1465759 baseEnd_1465759 := by
    simpa [prefixWord, tailWord_1465759, baseEnd_1465759] using wordTrace_append hprefix tailTrace_1465759
  have hstable : (prefixWord ++ tailWord_1465759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465759).length < 2 ^ (prefixWord ++ tailWord_1465759).sum := by decide
  have hdescent : baseEnd_1465759 < baseStart_1465759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465866 : List Nat := [3, 1, 2, 2, 2, 2, 1, 4, 1, 1, 4]
def baseStart_1465866 : Nat := 118140960795 + 1465866 * 2 ^ 59
def prefixEnd_1465866 : Nat := 4983230072969 + 3 ^ 40 * 1465866 * 2
def baseEnd_1465866 : Nat := 752693833083667026233611

theorem tailTrace_1465866 : CollatzResearch.WordTrace tailWord_1465866 prefixEnd_1465866 752693833083667026233611 := by
  unfold tailWord_1465866
  simp only [CollatzResearch.WordTrace]
  refine ⟨13366131326856326706632363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35643016871616871217686301 13366131326856326706632363)
  ·
    refine ⟨20049196990284490059948545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13366131326856326706632363 20049196990284490059948545)
    ·
      refine ⟨15036897742713367544961409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20049196990284490059948545 15036897742713367544961409)
      ·
        refine ⟨11277673307035025658721057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15036897742713367544961409 11277673307035025658721057)
        ·
          refine ⟨8458254980276269244040793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11277673307035025658721057 8458254980276269244040793)
          ·
            refine ⟨6343691235207201933030595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8458254980276269244040793 6343691235207201933030595)
            ·
              refine ⟨9515536852810802899545893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6343691235207201933030595 9515536852810802899545893)
              ·
                refine ⟨1784163159902025543664855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9515536852810802899545893 1784163159902025543664855)
                ·
                  refine ⟨2676244739853038315497283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1784163159902025543664855 2676244739853038315497283)
                  ·
                    refine ⟨4014367109779557473245925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2676244739853038315497283 4014367109779557473245925)
                    ·
                      refine ⟨752693833083667026233611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4014367109779557473245925 752693833083667026233611)
                      ·
                        rfl

theorem cell23_1465866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_1465866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465866 prefixEnd_1465866 := by exact prefixLift 1465866
  have htrace : WordTrace (prefixWord ++ tailWord_1465866) baseStart_1465866 baseEnd_1465866 := by
    simpa [prefixWord, tailWord_1465866, baseEnd_1465866] using wordTrace_append hprefix tailTrace_1465866
  have hstable : (prefixWord ++ tailWord_1465866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465866).length < 2 ^ (prefixWord ++ tailWord_1465866).sum := by decide
  have hdescent : baseEnd_1465866 < baseStart_1465866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465889 : List Nat := [1, 2, 3, 2, 2, 4, 9]
def baseStart_1465889 : Nat := 118140960795 + 1465889 * 2 ^ 59
def prefixEnd_1465889 : Nat := 4983230072969 + 3 ^ 40 * 1465889 * 2
def baseEnd_1465889 : Nat := 9292662260971857237605

theorem tailTrace_1465889 : CollatzResearch.WordTrace tailWord_1465889 prefixEnd_1465889 9292662260971857237605 := by
  unfold tailWord_1465889
  simp only [CollatzResearch.WordTrace]
  refine ⟨53465364186341981754616721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35643576124227987836411147 53465364186341981754616721)
  ·
    refine ⟨40099023139756486315962541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53465364186341981754616721 40099023139756486315962541)
    ·
      refine ⟨15037133677408682368485953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40099023139756486315962541 15037133677408682368485953)
      ·
        refine ⟨11277850258056511776364465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15037133677408682368485953 11277850258056511776364465)
        ·
          refine ⟨8458387693542383832273349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11277850258056511776364465 8458387693542383832273349)
          ·
            refine ⟨1585947692539196968551253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8458387693542383832273349 1585947692539196968551253)
            ·
              refine ⟨9292662260971857237605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1585947692539196968551253 9292662260971857237605)
              ·
                rfl

theorem cell23_1465889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 9].length) (baseStart_1465889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465889 prefixEnd_1465889 := by exact prefixLift 1465889
  have htrace : WordTrace (prefixWord ++ tailWord_1465889) baseStart_1465889 baseEnd_1465889 := by
    simpa [prefixWord, tailWord_1465889, baseEnd_1465889] using wordTrace_append hprefix tailTrace_1465889
  have hstable : (prefixWord ++ tailWord_1465889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465889).length < 2 ^ (prefixWord ++ tailWord_1465889).sum := by decide
  have hdescent : baseEnd_1465889 < baseStart_1465889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465910 : List Nat := [5, 1, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_1465910 : Nat := 118140960795 + 1465910 * 2 ^ 59
def prefixEnd_1465910 : Nat := 4983230072969 + 3 ^ 40 * 1465910 * 2
def baseEnd_1465910 : Nat := 250905475410821618027803

theorem tailTrace_1465910 : CollatzResearch.WordTrace tailWord_1465910 prefixEnd_1465910 250905475410821618027803 := by
  unfold tailWord_1465910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3341633132454118896320699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35644086746177268227420789 3341633132454118896320699)
  ·
    refine ⟨5012449698681178344481049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3341633132454118896320699 5012449698681178344481049)
    ·
      refine ⟨3759337274010883758360787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5012449698681178344481049 3759337274010883758360787)
      ·
        refine ⟨5639005911016325637541181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3759337274010883758360787 5639005911016325637541181)
        ·
          refine ⟨2114627216631122114077943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5639005911016325637541181 2114627216631122114077943)
          ·
            refine ⟨3171940824946683171116915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2114627216631122114077943 3171940824946683171116915)
            ·
              refine ⟨4757911237420024756675373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3171940824946683171116915 4757911237420024756675373)
              ·
                refine ⟨1784216714032509283753265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4757911237420024756675373 1784216714032509283753265)
                ·
                  refine ⟨1338162535524381962814949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1784216714032509283753265 1338162535524381962814949)
                  ·
                    refine ⟨250905475410821618027803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1338162535524381962814949 250905475410821618027803)
                    ·
                      rfl

theorem cell23_1465910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_1465910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465910 prefixEnd_1465910 := by exact prefixLift 1465910
  have htrace : WordTrace (prefixWord ++ tailWord_1465910) baseStart_1465910 baseEnd_1465910 := by
    simpa [prefixWord, tailWord_1465910, baseEnd_1465910] using wordTrace_append hprefix tailTrace_1465910
  have hstable : (prefixWord ++ tailWord_1465910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465910).length < 2 ^ (prefixWord ++ tailWord_1465910).sum := by decide
  have hdescent : baseEnd_1465910 < baseStart_1465910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465959 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1465959 : Nat := 118140960795 + 1465959 * 2 ^ 59
def prefixEnd_1465959 : Nat := 4983230072969 + 3 ^ 40 * 1465959 * 2
def baseEnd_1465959 : Nat := 752741586784535162370683

theorem tailTrace_1465959 : CollatzResearch.WordTrace tailWord_1465959 prefixEnd_1465959 752741586784535162370683 := by
  unfold tailWord_1465959
  simp only [CollatzResearch.WordTrace]
  refine ⟨53467917296088383709664931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35645278197392255806443287 53467917296088383709664931)
  ·
    refine ⟨80201875944132575564497397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53467917296088383709664931 80201875944132575564497397)
    ·
      refine ⟨7518925869762428959171631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80201875944132575564497397 7518925869762428959171631)
      ·
        refine ⟨11278388804643643438757447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7518925869762428959171631 11278388804643643438757447)
        ·
          refine ⟨16917583206965465158136171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11278388804643643438757447 16917583206965465158136171)
          ·
            refine ⟨25376374810448197737204257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16917583206965465158136171 25376374810448197737204257)
            ·
              refine ⟨19032281107836148302903193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25376374810448197737204257 19032281107836148302903193)
              ·
                refine ⟨14274210830877111227177395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19032281107836148302903193 14274210830877111227177395)
                ·
                  refine ⟨21411316246315666840766093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14274210830877111227177395 21411316246315666840766093)
                  ·
                    refine ⟨8029243592368375065287285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21411316246315666840766093 8029243592368375065287285)
                    ·
                      refine ⟨752741586784535162370683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8029243592368375065287285 752741586784535162370683)
                      ·
                        rfl

theorem cell23_1465959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1465959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465959 prefixEnd_1465959 := by exact prefixLift 1465959
  have htrace : WordTrace (prefixWord ++ tailWord_1465959) baseStart_1465959 baseEnd_1465959 := by
    simpa [prefixWord, tailWord_1465959, baseEnd_1465959] using wordTrace_append hprefix tailTrace_1465959
  have hstable : (prefixWord ++ tailWord_1465959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465959).length < 2 ^ (prefixWord ++ tailWord_1465959).sum := by decide
  have hdescent : baseEnd_1465959 < baseStart_1465959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465979 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 7]
def baseStart_1465979 : Nat := 118140960795 + 1465979 * 2 ^ 59
def prefixEnd_1465979 : Nat := 4983230072969 + 3 ^ 40 * 1465979 * 2
def baseEnd_1465979 : Nat := 83639095155291676013399

theorem tailTrace_1465979 : CollatzResearch.WordTrace tailWord_1465979 prefixEnd_1465979 83639095155291676013399 := by
  unfold tailWord_1465979
  simp only [CollatzResearch.WordTrace]
  refine ⟨53468646756015927125392991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35645764504010618083595327 53468646756015927125392991)
  ·
    refine ⟨80202970134023890688089487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53468646756015927125392991 80202970134023890688089487)
    ·
      refine ⟨120304455201035836032134231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80202970134023890688089487 120304455201035836032134231)
      ·
        refine ⟨180456682801553754048201347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120304455201035836032134231 180456682801553754048201347)
        ·
          refine ⟨270685024202330631072302021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180456682801553754048201347 270685024202330631072302021)
          ·
            refine ⟨50753442037936993326056629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270685024202330631072302021 50753442037936993326056629)
            ·
              refine ⟨4758135191056593124317809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50753442037936993326056629 4758135191056593124317809)
              ·
                refine ⟨3568601393292444843238357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4758135191056593124317809 3568601393292444843238357)
                ·
                  refine ⟨83639095155291676013399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3568601393292444843238357 83639095155291676013399)
                  ·
                    rfl

theorem cell23_1465979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 7].length) (baseStart_1465979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1465979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1465979 prefixEnd_1465979 := by exact prefixLift 1465979
  have htrace : WordTrace (prefixWord ++ tailWord_1465979) baseStart_1465979 baseEnd_1465979 := by
    simpa [prefixWord, tailWord_1465979, baseEnd_1465979] using wordTrace_append hprefix tailTrace_1465979
  have hstable : (prefixWord ++ tailWord_1465979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465979).length < 2 ^ (prefixWord ++ tailWord_1465979).sum := by decide
  have hdescent : baseEnd_1465979 < baseStart_1465979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466007 : List Nat := [1, 1, 3, 3, 2, 4, 1, 2, 2, 2, 2]
def baseStart_1466007 : Nat := 118140960795 + 1466007 * 2 ^ 59
def prefixEnd_1466007 : Nat := 4983230072969 + 3 ^ 40 * 1466007 * 2
def baseEnd_1466007 : Nat := 752766233855950974570463

theorem tailTrace_1466007 : CollatzResearch.WordTrace tailWord_1466007 prefixEnd_1466007 752766233855950974570463 := by
  unfold tailWord_1466007
  simp only [CollatzResearch.WordTrace]
  refine ⟨53469667999914487907412275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35646445333276325271608183 53469667999914487907412275)
  ·
    refine ⟨80204501999871731861118413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53469667999914487907412275 80204501999871731861118413)
    ·
      refine ⟨30076688249951899447919405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80204501999871731861118413 30076688249951899447919405)
      ·
        refine ⟨11278758093731962292969777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30076688249951899447919405 11278758093731962292969777)
        ·
          refine ⟨8459068570298971719727333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11278758093731962292969777 8459068570298971719727333)
          ·
            refine ⟨1586075356931057197448875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8459068570298971719727333 1586075356931057197448875)
            ·
              refine ⟨2379113035396585796173313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1586075356931057197448875 2379113035396585796173313)
              ·
                refine ⟨1784334776547439347129985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2379113035396585796173313 1784334776547439347129985)
                ·
                  refine ⟨1338251082410579510347489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1784334776547439347129985 1338251082410579510347489)
                  ·
                    refine ⟨1003688311807934632760617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1338251082410579510347489 1003688311807934632760617)
                    ·
                      refine ⟨752766233855950974570463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1003688311807934632760617 752766233855950974570463)
                      ·
                        rfl

theorem cell23_1466007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_1466007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466007 prefixEnd_1466007 := by exact prefixLift 1466007
  have htrace : WordTrace (prefixWord ++ tailWord_1466007) baseStart_1466007 baseEnd_1466007 := by
    simpa [prefixWord, tailWord_1466007, baseEnd_1466007] using wordTrace_append hprefix tailTrace_1466007
  have hstable : (prefixWord ++ tailWord_1466007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466007).length < 2 ^ (prefixWord ++ tailWord_1466007).sum := by decide
  have hdescent : baseEnd_1466007 < baseStart_1466007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466019 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 7]
def baseStart_1466019 : Nat := 118140960795 + 1466019 * 2 ^ 59
def prefixEnd_1466019 : Nat := 4983230072969 + 3 ^ 40 * 1466019 * 2
def baseEnd_1466019 : Nat := 752772395623804927620407

theorem tailTrace_1466019 : CollatzResearch.WordTrace tailWord_1466019 prefixEnd_1466019 752772395623804927620407 := by
  unfold tailWord_1466019
  simp only [CollatzResearch.WordTrace]
  refine ⟨53470105675871013956849111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35646737117247342637899407 53470105675871013956849111)
  ·
    refine ⟨80205158513806520935273667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53470105675871013956849111 80205158513806520935273667)
    ·
      refine ⟨120307737770709781402910501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80205158513806520935273667 120307737770709781402910501)
      ·
        refine ⟨22557700832008084013045719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120307737770709781402910501 22557700832008084013045719)
        ·
          refine ⟨33836551248012126019568579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22557700832008084013045719 33836551248012126019568579)
          ·
            refine ⟨50754826872018189029352869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33836551248012126019568579 50754826872018189029352869)
            ·
              refine ⟨9516530038503410443003663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50754826872018189029352869 9516530038503410443003663)
              ·
                refine ⟨14274795057755115664505495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9516530038503410443003663 14274795057755115664505495)
                ·
                  refine ⟨21412192586632673496758243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14274795057755115664505495 21412192586632673496758243)
                  ·
                    refine ⟨32118288879949010245137365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21412192586632673496758243 32118288879949010245137365)
                    ·
                      refine ⟨752772395623804927620407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32118288879949010245137365 752772395623804927620407)
                      ·
                        rfl

theorem cell23_1466019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_1466019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466019 prefixEnd_1466019 := by exact prefixLift 1466019
  have htrace : WordTrace (prefixWord ++ tailWord_1466019) baseStart_1466019 baseEnd_1466019 := by
    simpa [prefixWord, tailWord_1466019, baseEnd_1466019] using wordTrace_append hprefix tailTrace_1466019
  have hstable : (prefixWord ++ tailWord_1466019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466019).length < 2 ^ (prefixWord ++ tailWord_1466019).sum := by decide
  have hdescent : baseEnd_1466019 < baseStart_1466019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466059 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 6]
def baseStart_1466059 : Nat := 118140960795 + 1466059 * 2 ^ 59
def prefixEnd_1466059 : Nat := 4983230072969 + 3 ^ 40 * 1466059 * 2
def baseEnd_1466059 : Nat := 752792934849984771120223

theorem tailTrace_1466059 : CollatzResearch.WordTrace tailWord_1466059 prefixEnd_1466059 752792934849984771120223 := by
  unfold tailWord_1466059
  simp only [CollatzResearch.WordTrace]
  refine ⟨53471564595726100788305231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35647709730484067192203487 53471564595726100788305231)
  ·
    refine ⟨80207346893589151182457847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53471564595726100788305231 80207346893589151182457847)
    ·
      refine ⟨120311020340383726773686771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80207346893589151182457847 120311020340383726773686771)
      ·
        refine ⟨180466530510575590160530157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120311020340383726773686771 180466530510575590160530157)
        ·
          refine ⟨67674948941465846310198809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180466530510575590160530157 67674948941465846310198809)
          ·
            refine ⟨50756211706099384732649107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67674948941465846310198809 50756211706099384732649107)
            ·
              refine ⟨76134317559149077098973661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50756211706099384732649107 76134317559149077098973661)
              ·
                refine ⟨28550369084680903912115123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76134317559149077098973661 28550369084680903912115123)
                ·
                  refine ⟨42825553627021355868172685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28550369084680903912115123 42825553627021355868172685)
                  ·
                    refine ⟨16059582610133008450564757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42825553627021355868172685 16059582610133008450564757)
                    ·
                      refine ⟨752792934849984771120223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16059582610133008450564757 752792934849984771120223)
                      ·
                        rfl

theorem cell23_1466059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 6].length) (baseStart_1466059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466059 prefixEnd_1466059 := by exact prefixLift 1466059
  have htrace : WordTrace (prefixWord ++ tailWord_1466059) baseStart_1466059 baseEnd_1466059 := by
    simpa [prefixWord, tailWord_1466059, baseEnd_1466059] using wordTrace_append hprefix tailTrace_1466059
  have hstable : (prefixWord ++ tailWord_1466059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466059).length < 2 ^ (prefixWord ++ tailWord_1466059).sum := by decide
  have hdescent : baseEnd_1466059 < baseStart_1466059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466073 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 3, 4]
def baseStart_1466073 : Nat := 118140960795 + 1466073 * 2 ^ 59
def prefixEnd_1466073 : Nat := 4983230072969 + 3 ^ 40 * 1466073 * 2
def baseEnd_1466073 : Nat := 250933374526382572115053

theorem tailTrace_1466073 : CollatzResearch.WordTrace tailWord_1466073 prefixEnd_1466073 250933374526382572115053 := by
  unfold tailWord_1466073
  simp only [CollatzResearch.WordTrace]
  refine ⟨53472075217675381179314873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35648050145116920786209915 53472075217675381179314873)
  ·
    refine ⟨40104056413256535884486155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53472075217675381179314873 40104056413256535884486155)
    ·
      refine ⟨60156084619884803826729233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40104056413256535884486155 60156084619884803826729233)
      ·
        refine ⟨45117063464913602870046925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60156084619884803826729233 45117063464913602870046925)
        ·
          refine ⟨16918898799342601076267597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45117063464913602870046925 16918898799342601076267597)
          ·
            refine ⟨6344587049753475403600349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16918898799342601076267597 6344587049753475403600349)
            ·
              refine ⟨2379220143657553276350131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6344587049753475403600349 2379220143657553276350131)
              ·
                refine ⟨3568830215486329914525197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2379220143657553276350131 3568830215486329914525197)
                ·
                  refine ⟨1338311330807373717946949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3568830215486329914525197 1338311330807373717946949)
                  ·
                    refine ⟨250933374526382572115053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1338311330807373717946949 250933374526382572115053)
                    ·
                      rfl

theorem cell23_1466073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 4].length) (baseStart_1466073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466073 prefixEnd_1466073 := by exact prefixLift 1466073
  have htrace : WordTrace (prefixWord ++ tailWord_1466073) baseStart_1466073 baseEnd_1466073 := by
    simpa [prefixWord, tailWord_1466073, baseEnd_1466073] using wordTrace_append hprefix tailTrace_1466073
  have hstable : (prefixWord ++ tailWord_1466073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466073).length < 2 ^ (prefixWord ++ tailWord_1466073).sum := by decide
  have hdescent : baseEnd_1466073 < baseStart_1466073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466164 : List Nat := [2, 5, 1, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_1466164 : Nat := 118140960795 + 1466164 * 2 ^ 59
def prefixEnd_1466164 : Nat := 4983230072969 + 3 ^ 40 * 1466164 * 2
def baseEnd_1466164 : Nat := 752846850318706860307241

theorem tailTrace_1466164 : CollatzResearch.WordTrace tailWord_1466164 prefixEnd_1466164 752846850318706860307241 := by
  unfold tailWord_1466164
  simp only [CollatzResearch.WordTrace]
  refine ⟨26737697130172851860438773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35650262840230469147251697 26737697130172851860438773)
  ·
    refine ⟨2506659105953704861916135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26737697130172851860438773 2506659105953704861916135)
    ·
      refine ⟨3759988658930557292874203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2506659105953704861916135 3759988658930557292874203)
      ·
        refine ⟨5639982988395835939311305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3759988658930557292874203 5639982988395835939311305)
        ·
          refine ⟨4229987241296876954483479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5639982988395835939311305 4229987241296876954483479)
          ·
            refine ⟨6344980861945315431725219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4229987241296876954483479 6344980861945315431725219)
            ·
              refine ⟨9517471292917973147587829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6344980861945315431725219 9517471292917973147587829)
              ·
                refine ⟨892262933711059982586359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9517471292917973147587829 892262933711059982586359)
                ·
                  refine ⟨1338394400566589973879539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 892262933711059982586359 1338394400566589973879539)
                  ·
                    refine ⟨2007591600849884960819309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1338394400566589973879539 2007591600849884960819309)
                    ·
                      refine ⟨752846850318706860307241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2007591600849884960819309 752846850318706860307241)
                      ·
                        rfl

theorem cell23_1466164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_1466164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466164 prefixEnd_1466164 := by exact prefixLift 1466164
  have htrace : WordTrace (prefixWord ++ tailWord_1466164) baseStart_1466164 baseEnd_1466164 := by
    simpa [prefixWord, tailWord_1466164, baseEnd_1466164] using wordTrace_append hprefix tailTrace_1466164
  have hstable : (prefixWord ++ tailWord_1466164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466164).length < 2 ^ (prefixWord ++ tailWord_1466164).sum := by decide
  have hdescent : baseEnd_1466164 < baseStart_1466164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466170 : List Nat := [3, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4]
def baseStart_1466170 : Nat := 118140960795 + 1466170 * 2 ^ 59
def prefixEnd_1466170 : Nat := 4983230072969 + 3 ^ 40 * 1466170 * 2
def baseEnd_1466170 : Nat := 752849931202633836832213

theorem tailTrace_1466170 : CollatzResearch.WordTrace tailWord_1466170 prefixEnd_1466170 752849931202633836832213 := by
  unfold tailWord_1466170
  simp only [CollatzResearch.WordTrace]
  refine ⟨13368903274580991686398991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35650408732215977830397309 13368903274580991686398991)
  ·
    refine ⟨20053354911871487529598487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13368903274580991686398991 20053354911871487529598487)
    ·
      refine ⟨30080032367807231294397731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20053354911871487529598487 30080032367807231294397731)
      ·
        refine ⟨45120048551710846941596597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30080032367807231294397731 45120048551710846941596597)
        ·
          refine ⟨4230004551722891900774681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45120048551710846941596597 4230004551722891900774681)
          ·
            refine ⟨3172503413792168925581011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4230004551722891900774681 3172503413792168925581011)
            ·
              refine ⟨4758755120688253388371517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3172503413792168925581011 4758755120688253388371517)
              ·
                refine ⟨1784533170258095020639319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4758755120688253388371517 1784533170258095020639319)
                ·
                  refine ⟨2676799755387142530958979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1784533170258095020639319 2676799755387142530958979)
                  ·
                    refine ⟨4015199633080713796438469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2676799755387142530958979 4015199633080713796438469)
                    ·
                      refine ⟨752849931202633836832213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4015199633080713796438469 752849931202633836832213)
                      ·
                        rfl

theorem cell23_1466170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_1466170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466170 prefixEnd_1466170 := by exact prefixLift 1466170
  have htrace : WordTrace (prefixWord ++ tailWord_1466170) baseStart_1466170 baseEnd_1466170 := by
    simpa [prefixWord, tailWord_1466170, baseEnd_1466170] using wordTrace_append hprefix tailTrace_1466170
  have hstable : (prefixWord ++ tailWord_1466170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466170).length < 2 ^ (prefixWord ++ tailWord_1466170).sum := by decide
  have hdescent : baseEnd_1466170 < baseStart_1466170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466197 : List Nat := [1, 3, 2, 2, 2, 3, 3, 1, 2, 4]
def baseStart_1466197 : Nat := 118140960795 + 1466197 * 2 ^ 59
def prefixEnd_1466197 : Nat := 4983230072969 + 3 ^ 40 * 1466197 * 2
def baseEnd_1466197 : Nat := 250954598393435077064863

theorem tailTrace_1466197 : CollatzResearch.WordTrace tailWord_1466197 prefixEnd_1466197 250954598393435077064863 := by
  unfold tailWord_1466197
  simp only [CollatzResearch.WordTrace]
  refine ⟨53476597869226150356828845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35651065246150766904552563 53476597869226150356828845)
  ·
    refine ⟨20053724200959806383810817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53476597869226150356828845 20053724200959806383810817)
    ·
      refine ⟨15040293150719854787858113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20053724200959806383810817 15040293150719854787858113)
      ·
        refine ⟨11280219863039891090893585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15040293150719854787858113 11280219863039891090893585)
        ·
          refine ⟨8460164897279918318170189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11280219863039891090893585 8460164897279918318170189)
          ·
            refine ⟨3172561836479969369313821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8460164897279918318170189 3172561836479969369313821)
            ·
              refine ⟨1189710688679988513492683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3172561836479969369313821 1189710688679988513492683)
              ·
                refine ⟨1784566033019982770239025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189710688679988513492683 1784566033019982770239025)
                ·
                  refine ⟨1338424524764987077679269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1784566033019982770239025 1338424524764987077679269)
                  ·
                    refine ⟨250954598393435077064863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1338424524764987077679269 250954598393435077064863)
                    ·
                      rfl

theorem cell23_1466197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_1466197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466197 prefixEnd_1466197 := by exact prefixLift 1466197
  have htrace : WordTrace (prefixWord ++ tailWord_1466197) baseStart_1466197 baseEnd_1466197 := by
    simpa [prefixWord, tailWord_1466197, baseEnd_1466197] using wordTrace_append hprefix tailTrace_1466197
  have hstable : (prefixWord ++ tailWord_1466197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466197).length < 2 ^ (prefixWord ++ tailWord_1466197).sum := by decide
  have hdescent : baseEnd_1466197 < baseStart_1466197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466210 : List Nat := [3, 3, 2, 1, 2, 1, 4, 7]
def baseStart_1466210 : Nat := 118140960795 + 1466210 * 2 ^ 59
def prefixEnd_1466210 : Nat := 4983230072969 + 3 ^ 40 * 1466210 * 2
def baseEnd_1466210 : Nat := 27884091497363469641927

theorem tailTrace_1466210 : CollatzResearch.WordTrace tailWord_1466210 prefixEnd_1466210 27884091497363469641927 := by
  unfold tailWord_1466210
  simp only [CollatzResearch.WordTrace]
  refine ⟨13369268004544763394263021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35651381345452702384701389 13369268004544763394263021)
  ·
    refine ⟨5013475501704286272848633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13369268004544763394263021 5013475501704286272848633)
    ·
      refine ⟨3760106626278214704636475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5013475501704286272848633 3760106626278214704636475)
      ·
        refine ⟨5640159939417322056954713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3760106626278214704636475 5640159939417322056954713)
        ·
          refine ⟨4230119954562991542716035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5640159939417322056954713 4230119954562991542716035)
          ·
            refine ⟨6345179931844487314074053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4230119954562991542716035 6345179931844487314074053)
            ·
              refine ⟨1189721237220841371388885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6345179931844487314074053 1189721237220841371388885)
              ·
                refine ⟨27884091497363469641927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1189721237220841371388885 27884091497363469641927)
                ·
                  rfl

theorem cell23_1466210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 7].length) (baseStart_1466210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466210 prefixEnd_1466210 := by exact prefixLift 1466210
  have htrace : WordTrace (prefixWord ++ tailWord_1466210) baseStart_1466210 baseEnd_1466210 := by
    simpa [prefixWord, tailWord_1466210, baseEnd_1466210] using wordTrace_append hprefix tailTrace_1466210
  have hstable : (prefixWord ++ tailWord_1466210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466210).length < 2 ^ (prefixWord ++ tailWord_1466210).sum := by decide
  have hdescent : baseEnd_1466210 < baseStart_1466210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466220 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 3]
def baseStart_1466220 : Nat := 118140960795 + 1466220 * 2 ^ 59
def prefixEnd_1466220 : Nat := 4983230072969 + 3 ^ 40 * 1466220 * 2
def baseEnd_1466220 : Nat := 752875605235358641206983

theorem tailTrace_1466220 : CollatzResearch.WordTrace tailWord_1466220 prefixEnd_1466220 752875605235358641206983 := by
  unfold tailWord_1466220
  simp only [CollatzResearch.WordTrace]
  refine ⟨26738718374071412642458057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35651624498761883523277409 26738718374071412642458057)
  ·
    refine ⟨20054038780553559481843543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26738718374071412642458057 20054038780553559481843543)
    ·
      refine ⟨30081058170830339222765315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20054038780553559481843543 30081058170830339222765315)
      ·
        refine ⟨45121587256245508834147973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30081058170830339222765315 45121587256245508834147973)
        ·
          refine ⟨8460297610546032906402745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45121587256245508834147973 8460297610546032906402745)
          ·
            refine ⟨6345223207909524679802059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8460297610546032906402745 6345223207909524679802059)
            ·
              refine ⟨9517834811864287019703089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6345223207909524679802059 9517834811864287019703089)
              ·
                refine ⟨7138376108898215264777317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9517834811864287019703089 7138376108898215264777317)
                ·
                  refine ⟨1338445520418415362145747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7138376108898215264777317 1338445520418415362145747)
                  ·
                    refine ⟨2007668280627623043218621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1338445520418415362145747 2007668280627623043218621)
                    ·
                      refine ⟨752875605235358641206983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2007668280627623043218621 752875605235358641206983)
                      ·
                        rfl

theorem cell23_1466220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_1466220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466220 prefixEnd_1466220 := by exact prefixLift 1466220
  have htrace : WordTrace (prefixWord ++ tailWord_1466220) baseStart_1466220 baseEnd_1466220 := by
    simpa [prefixWord, tailWord_1466220, baseEnd_1466220] using wordTrace_append hprefix tailTrace_1466220
  have hstable : (prefixWord ++ tailWord_1466220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466220).length < 2 ^ (prefixWord ++ tailWord_1466220).sum := by decide
  have hdescent : baseEnd_1466220 < baseStart_1466220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466263 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 5]
def baseStart_1466263 : Nat := 118140960795 + 1466263 * 2 ^ 59
def prefixEnd_1466263 : Nat := 4983230072969 + 3 ^ 40 * 1466263 * 2
def baseEnd_1466263 : Nat := 752897684903501972969285

theorem tailTrace_1466263 : CollatzResearch.WordTrace tailWord_1466263 prefixEnd_1466263 752897684903501972969285 := by
  unfold tailWord_1466263
  simp only [CollatzResearch.WordTrace]
  refine ⟨53479005086987043628731443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35652670057991362419154295 53479005086987043628731443)
  ·
    refine ⟨80218507630480565443097165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53479005086987043628731443 80218507630480565443097165)
    ·
      refine ⟨30081940361430212041161437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80218507630480565443097165 30081940361430212041161437)
      ·
        refine ⟨11280727635536329515435539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30081940361430212041161437 11280727635536329515435539)
        ·
          refine ⟨16921091453304494273153309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11280727635536329515435539 16921091453304494273153309)
          ·
            refine ⟨6345409294989185352432491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16921091453304494273153309 6345409294989185352432491)
            ·
              refine ⟨9518113942483778028648737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6345409294989185352432491 9518113942483778028648737)
              ·
                refine ⟨7138585456862833521486553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9518113942483778028648737 7138585456862833521486553)
                ·
                  refine ⟨5353939092647125141114915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7138585456862833521486553 5353939092647125141114915)
                  ·
                    refine ⟨8030908638970687711672373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5353939092647125141114915 8030908638970687711672373)
                    ·
                      refine ⟨752897684903501972969285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8030908638970687711672373 752897684903501972969285)
                      ·
                        rfl

theorem cell23_1466263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_1466263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466263 prefixEnd_1466263 := by exact prefixLift 1466263
  have htrace : WordTrace (prefixWord ++ tailWord_1466263) baseStart_1466263 baseEnd_1466263 := by
    simpa [prefixWord, tailWord_1466263, baseEnd_1466263] using wordTrace_append hprefix tailTrace_1466263
  have hstable : (prefixWord ++ tailWord_1466263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466263).length < 2 ^ (prefixWord ++ tailWord_1466263).sum := by decide
  have hdescent : baseEnd_1466263 < baseStart_1466263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466264 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 3, 3, 2]
def baseStart_1466264 : Nat := 118140960795 + 1466264 * 2 ^ 59
def prefixEnd_1466264 : Nat := 4983230072969 + 3 ^ 40 * 1466264 * 2
def baseEnd_1466264 : Nat := 752898198384156469056781

theorem tailTrace_1466264 : CollatzResearch.WordTrace tailWord_1466264 prefixEnd_1466264 752898198384156469056781 := by
  unfold tailWord_1466264
  simp only [CollatzResearch.WordTrace]
  refine ⟨26739520779991710399758923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35652694373322280533011897 26739520779991710399758923)
  ·
    refine ⟨40109281169987565599638385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26739520779991710399758923 40109281169987565599638385)
    ·
      refine ⟨30081960877490674199728789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40109281169987565599638385 30081960877490674199728789)
      ·
        refine ⟨1410091916132375353112287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30081960877490674199728789 1410091916132375353112287)
        ·
          refine ⟨2115137874198563029668431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1410091916132375353112287 2115137874198563029668431)
          ·
            refine ⟨3172706811297844544502647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115137874198563029668431 3172706811297844544502647)
            ·
              refine ⟨4759060216946766816753971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3172706811297844544502647 4759060216946766816753971)
              ·
                refine ⟨7138590325420150225130957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4759060216946766816753971 7138590325420150225130957)
                ·
                  refine ⟨2676971372032556334424109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7138590325420150225130957 2676971372032556334424109)
                  ·
                    refine ⟨1003864264512208625409041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2676971372032556334424109 1003864264512208625409041)
                    ·
                      refine ⟨752898198384156469056781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1003864264512208625409041 752898198384156469056781)
                      ·
                        rfl

theorem cell23_1466264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_1466264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466264 prefixEnd_1466264 := by exact prefixLift 1466264
  have htrace : WordTrace (prefixWord ++ tailWord_1466264) baseStart_1466264 baseEnd_1466264 := by
    simpa [prefixWord, tailWord_1466264, baseEnd_1466264] using wordTrace_append hprefix tailTrace_1466264
  have hstable : (prefixWord ++ tailWord_1466264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466264).length < 2 ^ (prefixWord ++ tailWord_1466264).sum := by decide
  have hdescent : baseEnd_1466264 < baseStart_1466264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466330 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 1, 7]
def baseStart_1466330 : Nat := 118140960795 + 1466330 * 2 ^ 59
def prefixEnd_1466330 : Nat := 4983230072969 + 3 ^ 40 * 1466330 * 2
def baseEnd_1466330 : Nat := 250977362702451070277159

theorem tailTrace_1466330 : CollatzResearch.WordTrace tailWord_1466330 prefixEnd_1466330 250977362702451070277159 := by
  unfold tailWord_1466330
  simp only [CollatzResearch.WordTrace]
  refine ⟨13370362194436078517855111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35654299185162876047613629 13370362194436078517855111)
  ·
    refine ⟨20055543291654117776782667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13370362194436078517855111 20055543291654117776782667)
    ·
      refine ⟨30083314937481176665174001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20055543291654117776782667 30083314937481176665174001)
      ·
        refine ⟨22562486203110882498880501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30083314937481176665174001 22562486203110882498880501)
        ·
          refine ⟨2115233081541645234270047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22562486203110882498880501 2115233081541645234270047)
          ·
            refine ⟨3172849622312467851405071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115233081541645234270047 3172849622312467851405071)
            ·
              refine ⟨4759274433468701777107607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3172849622312467851405071 4759274433468701777107607)
              ·
                refine ⟨7138911650203052665661411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4759274433468701777107607 7138911650203052665661411)
                ·
                  refine ⟨10708367475304578998492117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7138911650203052665661411 10708367475304578998492117)
                  ·
                    refine ⟨250977362702451070277159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10708367475304578998492117 250977362702451070277159)
                    ·
                      rfl

theorem cell23_1466330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_1466330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466330 prefixEnd_1466330 := by exact prefixLift 1466330
  have htrace : WordTrace (prefixWord ++ tailWord_1466330) baseStart_1466330 baseEnd_1466330 := by
    simpa [prefixWord, tailWord_1466330, baseEnd_1466330] using wordTrace_append hprefix tailTrace_1466330
  have hstable : (prefixWord ++ tailWord_1466330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466330).length < 2 ^ (prefixWord ++ tailWord_1466330).sum := by decide
  have hdescent : baseEnd_1466330 < baseStart_1466330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466332 : List Nat := [2, 2, 6, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_1466332 : Nat := 118140960795 + 1466332 * 2 ^ 59
def prefixEnd_1466332 : Nat := 4983230072969 + 3 ^ 40 * 1466332 * 2
def baseEnd_1466332 : Nat := 752933115068662203006469

theorem tailTrace_1466332 : CollatzResearch.WordTrace tailWord_1466332 prefixEnd_1466332 752933115068662203006469 := by
  unfold tailWord_1466332
  simp only [CollatzResearch.WordTrace]
  refine ⟨26740760861868534206496625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35654347815824712275328833 26740760861868534206496625)
  ·
    refine ⟨20055570646401400654872469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26740760861868534206496625 20055570646401400654872469)
    ·
      refine ⟨940104874050065655697147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20055570646401400654872469 940104874050065655697147)
      ·
        refine ⟨1410157311075098483545721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 940104874050065655697147 1410157311075098483545721)
        ·
          refine ⟨1057617983306323862659291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1410157311075098483545721 1057617983306323862659291)
          ·
            refine ⟨1586426974959485793988937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057617983306323862659291 1586426974959485793988937)
            ·
              refine ⟨1189820231219614345491703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1586426974959485793988937 1189820231219614345491703)
              ·
                refine ⟨1784730346829421518237555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189820231219614345491703 1784730346829421518237555)
                ·
                  refine ⟨2677095520244132277356333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1784730346829421518237555 2677095520244132277356333)
                  ·
                    refine ⟨1003910820091549604008625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2677095520244132277356333 1003910820091549604008625)
                    ·
                      refine ⟨752933115068662203006469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1003910820091549604008625 752933115068662203006469)
                      ·
                        rfl

theorem cell23_1466332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_1466332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466332 prefixEnd_1466332 := by exact prefixLift 1466332
  have htrace : WordTrace (prefixWord ++ tailWord_1466332) baseStart_1466332 baseEnd_1466332 := by
    simpa [prefixWord, tailWord_1466332, baseEnd_1466332] using wordTrace_append hprefix tailTrace_1466332
  have hstable : (prefixWord ++ tailWord_1466332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466332).length < 2 ^ (prefixWord ++ tailWord_1466332).sum := by decide
  have hdescent : baseEnd_1466332 < baseStart_1466332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466360 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 3, 4]
def baseStart_1466360 : Nat := 118140960795 + 1466360 * 2 ^ 59
def prefixEnd_1466360 : Nat := 4983230072969 + 3 ^ 40 * 1466360 * 2
def baseEnd_1466360 : Nat := 250982497508996031152113

theorem tailTrace_1466360 : CollatzResearch.WordTrace tailWord_1466360 prefixEnd_1466360 250982497508996031152113 := by
  unfold tailWord_1466360
  simp only [CollatzResearch.WordTrace]
  refine ⟨26741271483817814597506267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35655028645090419463341689 26741271483817814597506267)
  ·
    refine ⟨40111907225726721896259401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26741271483817814597506267 40111907225726721896259401)
    ·
      refine ⟨30083930419295041422194551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40111907225726721896259401 30083930419295041422194551)
      ·
        refine ⟨45125895628942562133291827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30083930419295041422194551 45125895628942562133291827)
        ·
          refine ⟨67688843443413843199937741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45125895628942562133291827 67688843443413843199937741)
          ·
            refine ⟨25383316291280191199976653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67688843443413843199937741 25383316291280191199976653)
            ·
              refine ⟨9518743609230071699991245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25383316291280191199976653 9518743609230071699991245)
              ·
                refine ⟨3569528853461276887496717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9518743609230071699991245 3569528853461276887496717)
                ·
                  refine ⟨1338573320047978832811269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3569528853461276887496717 1338573320047978832811269)
                  ·
                    refine ⟨250982497508996031152113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1338573320047978832811269 250982497508996031152113)
                    ·
                      rfl

theorem cell23_1466360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_1466360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466360 prefixEnd_1466360 := by exact prefixLift 1466360
  have htrace : WordTrace (prefixWord ++ tailWord_1466360) baseStart_1466360 baseEnd_1466360 := by
    simpa [prefixWord, tailWord_1466360, baseEnd_1466360] using wordTrace_append hprefix tailTrace_1466360
  have hstable : (prefixWord ++ tailWord_1466360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466360).length < 2 ^ (prefixWord ++ tailWord_1466360).sum := by decide
  have hdescent : baseEnd_1466360 < baseStart_1466360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466394 : List Nat := [3, 1, 1, 3, 1, 3, 3, 3, 1, 4]
def baseStart_1466394 : Nat := 118140960795 + 1466394 * 2 ^ 59
def prefixEnd_1466394 : Nat := 4983230072969 + 3 ^ 40 * 1466394 * 2
def baseEnd_1466394 : Nat := 250988316956413653477061

theorem tailTrace_1466394 : CollatzResearch.WordTrace tailWord_1466394 prefixEnd_1466394 250988316956413653477061 := by
  unfold tailWord_1466394
  simp only [CollatzResearch.WordTrace]
  refine ⟨13370945762378113250437559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35655855366341635334500157 13370945762378113250437559)
  ·
    refine ⟨20056418643567169875656339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13370945762378113250437559 20056418643567169875656339)
    ·
      refine ⟨30084627965350754813484509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20056418643567169875656339 30084627965350754813484509)
      ·
        refine ⟨11281735487006533055056691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30084627965350754813484509 11281735487006533055056691)
        ·
          refine ⟨16922603230509799582585037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11281735487006533055056691 16922603230509799582585037)
          ·
            refine ⟨6345976211441174843469389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16922603230509799582585037 6345976211441174843469389)
            ·
              refine ⟨2379741079290440566301021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6345976211441174843469389 2379741079290440566301021)
              ·
                refine ⟨892402904733915212362883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2379741079290440566301021 892402904733915212362883)
                ·
                  refine ⟨1338604357100872818544325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 892402904733915212362883 1338604357100872818544325)
                  ·
                    refine ⟨250988316956413653477061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1338604357100872818544325 250988316956413653477061)
                    ·
                      rfl

theorem cell23_1466394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 1, 4].length) (baseStart_1466394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466394 prefixEnd_1466394 := by exact prefixLift 1466394
  have htrace : WordTrace (prefixWord ++ tailWord_1466394) baseStart_1466394 baseEnd_1466394 := by
    simpa [prefixWord, tailWord_1466394, baseEnd_1466394] using wordTrace_append hprefix tailTrace_1466394
  have hstable : (prefixWord ++ tailWord_1466394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466394).length < 2 ^ (prefixWord ++ tailWord_1466394).sum := by decide
  have hdescent : baseEnd_1466394 < baseStart_1466394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466404 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 2, 2, 3]
def baseStart_1466404 : Nat := 118140960795 + 1466404 * 2 ^ 59
def prefixEnd_1466404 : Nat := 4983230072969 + 3 ^ 40 * 1466404 * 2
def baseEnd_1466404 : Nat := 752970085675785921306137

theorem tailTrace_1466404 : CollatzResearch.WordTrace tailWord_1466404 prefixEnd_1466404 752970085675785921306137 := by
  unfold tailWord_1466404
  simp only [CollatzResearch.WordTrace]
  refine ⟨26742073889738112354807133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35656098519650816473076177 26742073889738112354807133)
  ·
    refine ⟨10028277708651792133052675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26742073889738112354807133 10028277708651792133052675)
    ·
      refine ⟨15042416562977688199579013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10028277708651792133052675 15042416562977688199579013)
      ·
        refine ⟨2820453105558316537421065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15042416562977688199579013 2820453105558316537421065)
        ·
          refine ⟨2115339829168737403065799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2820453105558316537421065 2115339829168737403065799)
          ·
            refine ⟨3173009743753106104598699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115339829168737403065799 3173009743753106104598699)
            ·
              refine ⟨4759514615629659156898049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3173009743753106104598699 4759514615629659156898049)
              ·
                refine ⟨3569635961722244367673537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4759514615629659156898049 3569635961722244367673537)
                ·
                  refine ⟨2677226971291683275755153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3569635961722244367673537 2677226971291683275755153)
                  ·
                    refine ⟨2007920228468762456816365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2677226971291683275755153 2007920228468762456816365)
                    ·
                      refine ⟨752970085675785921306137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2007920228468762456816365 752970085675785921306137)
                      ·
                        rfl

theorem cell23_1466404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_1466404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466404 prefixEnd_1466404 := by exact prefixLift 1466404
  have htrace : WordTrace (prefixWord ++ tailWord_1466404) baseStart_1466404 baseEnd_1466404 := by
    simpa [prefixWord, tailWord_1466404, baseEnd_1466404] using wordTrace_append hprefix tailTrace_1466404
  have hstable : (prefixWord ++ tailWord_1466404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466404).length < 2 ^ (prefixWord ++ tailWord_1466404).sum := by decide
  have hdescent : baseEnd_1466404 < baseStart_1466404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466424 : List Nat := [2, 1, 2, 1, 6, 2, 2, 1, 6]
def baseStart_1466424 : Nat := 118140960795 + 1466424 * 2 ^ 59
def prefixEnd_1466424 : Nat := 4983230072969 + 3 ^ 40 * 1466424 * 2
def baseEnd_1466424 : Nat := 83664483920986204784005

theorem tailTrace_1466424 : CollatzResearch.WordTrace tailWord_1466424 prefixEnd_1466424 83664483920986204784005 := by
  unfold tailWord_1466424
  simp only [CollatzResearch.WordTrace]
  refine ⟨26742438619701884062671163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35656584826269178750228217 26742438619701884062671163)
  ·
    refine ⟨40113657929552826094006745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26742438619701884062671163 40113657929552826094006745)
    ·
      refine ⟨30085243447164619570505059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40113657929552826094006745 30085243447164619570505059)
      ·
        refine ⟨45127865170746929355757589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30085243447164619570505059 45127865170746929355757589)
        ·
          refine ⟨2115368679878762313551137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45127865170746929355757589 2115368679878762313551137)
          ·
            refine ⟨1586526509909071735163353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2115368679878762313551137 1586526509909071735163353)
            ·
              refine ⟨1189894882431803801372515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1586526509909071735163353 1189894882431803801372515)
              ·
                refine ⟨1784842323647705702058773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189894882431803801372515 1784842323647705702058773)
                ·
                  refine ⟨83664483920986204784005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1784842323647705702058773 83664483920986204784005)
                  ·
                    rfl

theorem cell23_1466424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 6].length) (baseStart_1466424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466424 prefixEnd_1466424 := by exact prefixLift 1466424
  have htrace : WordTrace (prefixWord ++ tailWord_1466424) baseStart_1466424 baseEnd_1466424 := by
    simpa [prefixWord, tailWord_1466424, baseEnd_1466424] using wordTrace_append hprefix tailTrace_1466424
  have hstable : (prefixWord ++ tailWord_1466424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466424).length < 2 ^ (prefixWord ++ tailWord_1466424).sum := by decide
  have hdescent : baseEnd_1466424 < baseStart_1466424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466461 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_1466461 : Nat := 118140960795 + 1466461 * 2 ^ 59
def prefixEnd_1466461 : Nat := 4983230072969 + 3 ^ 40 * 1466461 * 2
def baseEnd_1466461 : Nat := 752999354073092198293375

theorem tailTrace_1466461 : CollatzResearch.WordTrace tailWord_1466461 prefixEnd_1466461 752999354073092198293375 := by
  unfold tailWord_1466461
  simp only [CollatzResearch.WordTrace]
  refine ⟨53486226740269723444439237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35657484493513148962959491 53486226740269723444439237)
  ·
    refine ⟨10028667513800573145832357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53486226740269723444439237 10028667513800573145832357)
    ·
      refine ⟨1880375158837607464843567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10028667513800573145832357 1880375158837607464843567)
      ·
        refine ⟨2820562738256411197265351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880375158837607464843567 2820562738256411197265351)
        ·
          refine ⟨4230844107384616795898027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2820562738256411197265351 4230844107384616795898027)
          ·
            refine ⟨6346266161076925193847041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4230844107384616795898027 6346266161076925193847041)
            ·
              refine ⟨4759699620807693895385281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6346266161076925193847041 4759699620807693895385281)
              ·
                refine ⟨3569774715605770421538961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4759699620807693895385281 3569774715605770421538961)
                ·
                  refine ⟨2677331036704327816154221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3569774715605770421538961 2677331036704327816154221)
                  ·
                    refine ⟨1003999138764122931057833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2677331036704327816154221 1003999138764122931057833)
                    ·
                      refine ⟨752999354073092198293375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1003999138764122931057833 752999354073092198293375)
                      ·
                        rfl

theorem cell23_1466461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_1466461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466461 prefixEnd_1466461 := by exact prefixLift 1466461
  have htrace : WordTrace (prefixWord ++ tailWord_1466461) baseStart_1466461 baseEnd_1466461 := by
    simpa [prefixWord, tailWord_1466461, baseEnd_1466461] using wordTrace_append hprefix tailTrace_1466461
  have hstable : (prefixWord ++ tailWord_1466461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466461).length < 2 ^ (prefixWord ++ tailWord_1466461).sum := by decide
  have hdescent : baseEnd_1466461 < baseStart_1466461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466462 : List Nat := [4, 4, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_1466462 : Nat := 118140960795 + 1466462 * 2 ^ 59
def prefixEnd_1466462 : Nat := 4983230072969 + 3 ^ 40 * 1466462 * 2
def baseEnd_1466462 : Nat := 250999955851248898126957

theorem tailTrace_1466462 : CollatzResearch.WordTrace tailWord_1466462 prefixEnd_1466462 250999955851248898126957 := by
  unfold tailWord_1466462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6685782901658262576903205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35657508808844067076817093 6685782901658262576903205)
  ·
    refine ⟨1253584294060924233169351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6685782901658262576903205 1253584294060924233169351)
    ·
      refine ⟨1880376441091386349754027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1253584294060924233169351 1880376441091386349754027)
      ·
        refine ⟨2820564661637079524631041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880376441091386349754027 2820564661637079524631041)
        ·
          refine ⟨2115423496227809643473281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2820564661637079524631041 2115423496227809643473281)
          ·
            refine ⟨1586567622170857232604961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2115423496227809643473281 1586567622170857232604961)
            ·
              refine ⟨1189925716628142924453721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1586567622170857232604961 1189925716628142924453721)
              ·
                refine ⟨892444287471107193340291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1189925716628142924453721 892444287471107193340291)
                ·
                  refine ⟨1338666431206660790010437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 892444287471107193340291 1338666431206660790010437)
                  ·
                    refine ⟨250999955851248898126957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1338666431206660790010437 250999955851248898126957)
                    ·
                      rfl

theorem cell23_1466462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_1466462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466462 prefixEnd_1466462 := by exact prefixLift 1466462
  have htrace : WordTrace (prefixWord ++ tailWord_1466462) baseStart_1466462 baseEnd_1466462 := by
    simpa [prefixWord, tailWord_1466462, baseEnd_1466462] using wordTrace_append hprefix tailTrace_1466462
  have hstable : (prefixWord ++ tailWord_1466462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466462).length < 2 ^ (prefixWord ++ tailWord_1466462).sum := by decide
  have hdescent : baseEnd_1466462 < baseStart_1466462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466467 : List Nat := [1, 1, 1, 5, 1, 1, 3, 4, 2, 4]
def baseStart_1466467 : Nat := 118140960795 + 1466467 * 2 ^ 59
def prefixEnd_1466467 : Nat := 4983230072969 + 3 ^ 40 * 1466467 * 2
def baseEnd_1466467 : Nat := 251000811652339724939449

theorem tailTrace_1466467 : CollatzResearch.WordTrace tailWord_1466467 prefixEnd_1466467 251000811652339724939449 := by
  unfold tailWord_1466467
  simp only [CollatzResearch.WordTrace]
  refine ⟨53486445578247986469157655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35657630385498657646105103 53486445578247986469157655)
  ·
    refine ⟨80229668367371979703736483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53486445578247986469157655 80229668367371979703736483)
    ·
      refine ⟨120344502551057969555604725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80229668367371979703736483 120344502551057969555604725)
      ·
        refine ⟨11282297114161684645837943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120344502551057969555604725 11282297114161684645837943)
        ·
          refine ⟨16923445671242526968756915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11282297114161684645837943 16923445671242526968756915)
          ·
            refine ⟨25385168506863790453135373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16923445671242526968756915 25385168506863790453135373)
            ·
              refine ⟨9519438190073921419925765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25385168506863790453135373 9519438190073921419925765)
              ·
                refine ⟨1784894660638860266236081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9519438190073921419925765 1784894660638860266236081)
                ·
                  refine ⟨1338670995479145199677061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1784894660638860266236081 1338670995479145199677061)
                  ·
                    refine ⟨251000811652339724939449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1338670995479145199677061 251000811652339724939449)
                    ·
                      rfl

theorem cell23_1466467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 4].length) (baseStart_1466467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466467 prefixEnd_1466467 := by exact prefixLift 1466467
  have htrace : WordTrace (prefixWord ++ tailWord_1466467) baseStart_1466467 baseEnd_1466467 := by
    simpa [prefixWord, tailWord_1466467, baseEnd_1466467] using wordTrace_append hprefix tailTrace_1466467
  have hstable : (prefixWord ++ tailWord_1466467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466467).length < 2 ^ (prefixWord ++ tailWord_1466467).sum := by decide
  have hdescent : baseEnd_1466467 < baseStart_1466467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466477 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_1466477 : Nat := 118140960795 + 1466477 * 2 ^ 59
def prefixEnd_1466477 : Nat := 4983230072969 + 3 ^ 40 * 1466477 * 2
def baseEnd_1466477 : Nat := 753007569763564135693301

theorem tailTrace_1466477 : CollatzResearch.WordTrace tailWord_1466477 prefixEnd_1466477 753007569763564135693301 := by
  unfold tailWord_1466477
  simp only [CollatzResearch.WordTrace]
  refine ⟨53486810308211758177021685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35657873538807838784681123 53486810308211758177021685)
  ·
    refine ⟨5014388466394852329095783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53486810308211758177021685 5014388466394852329095783)
    ·
      refine ⟨7521582699592278493643675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5014388466394852329095783 7521582699592278493643675)
      ·
        refine ⟨11282374049388417740465513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7521582699592278493643675 11282374049388417740465513)
        ·
          refine ⟨8461780537041313305349135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11282374049388417740465513 8461780537041313305349135)
          ·
            refine ⟨12692670805561969958023703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8461780537041313305349135 12692670805561969958023703)
            ·
              refine ⟨19039006208342954937035555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12692670805561969958023703 19039006208342954937035555)
              ·
                refine ⟨28558509312514432405553333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19039006208342954937035555 28558509312514432405553333)
                ·
                  refine ⟨2677360248048228038020625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28558509312514432405553333 2677360248048228038020625)
                  ·
                    refine ⟨2008020186036171028515469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2677360248048228038020625 2008020186036171028515469)
                    ·
                      refine ⟨753007569763564135693301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2008020186036171028515469 753007569763564135693301)
                      ·
                        rfl

theorem cell23_1466477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_1466477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466477 prefixEnd_1466477 := by exact prefixLift 1466477
  have htrace : WordTrace (prefixWord ++ tailWord_1466477) baseStart_1466477 baseEnd_1466477 := by
    simpa [prefixWord, tailWord_1466477, baseEnd_1466477] using wordTrace_append hprefix tailTrace_1466477
  have hstable : (prefixWord ++ tailWord_1466477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466477).length < 2 ^ (prefixWord ++ tailWord_1466477).sum := by decide
  have hdescent : baseEnd_1466477 < baseStart_1466477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466480 : List Nat := [2, 1, 1, 1, 5, 2, 3, 8]
def baseStart_1466480 : Nat := 118140960795 + 1466480 * 2 ^ 59
def prefixEnd_1466480 : Nat := 4983230072969 + 3 ^ 40 * 1466480 * 2
def baseEnd_1466480 : Nat := 27889226303908430516881

theorem tailTrace_1466480 : CollatzResearch.WordTrace tailWord_1466480 prefixEnd_1466480 27889226303908430516881 := by
  unfold tailWord_1466480
  simp only [CollatzResearch.WordTrace]
  refine ⟨26743459863600444844690447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35657946484800593126253929 26743459863600444844690447)
  ·
    refine ⟨40115189795400667267035671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26743459863600444844690447 40115189795400667267035671)
    ·
      refine ⟨60172784693101000900553507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40115189795400667267035671 60172784693101000900553507)
      ·
        refine ⟨90259177039651501350830261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60172784693101000900553507 90259177039651501350830261)
        ·
          refine ⟨8461797847467328251640337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90259177039651501350830261 8461797847467328251640337)
          ·
            refine ⟨6346348385600496188730253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8461797847467328251640337 6346348385600496188730253)
            ·
              refine ⟨2379880644600186070773845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6346348385600496188730253 2379880644600186070773845)
              ·
                refine ⟨27889226303908430516881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2379880644600186070773845 27889226303908430516881)
                ·
                  rfl

theorem cell23_1466480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 8].length) (baseStart_1466480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466480 prefixEnd_1466480 := by exact prefixLift 1466480
  have htrace : WordTrace (prefixWord ++ tailWord_1466480) baseStart_1466480 baseEnd_1466480 := by
    simpa [prefixWord, tailWord_1466480, baseEnd_1466480] using wordTrace_append hprefix tailTrace_1466480
  have hstable : (prefixWord ++ tailWord_1466480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466480).length < 2 ^ (prefixWord ++ tailWord_1466480).sum := by decide
  have hdescent : baseEnd_1466480 < baseStart_1466480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466487 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 4]
def baseStart_1466487 : Nat := 118140960795 + 1466487 * 2 ^ 59
def prefixEnd_1466487 : Nat := 4983230072969 + 3 ^ 40 * 1466487 * 2
def baseEnd_1466487 : Nat := 753012704570109096568255

theorem tailTrace_1466487 : CollatzResearch.WordTrace tailWord_1466487 prefixEnd_1466487 753012704570109096568255 := by
  unfold tailWord_1466487
  simp only [CollatzResearch.WordTrace]
  refine ⟨53487175038175529884885715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35658116692117019923257143 53487175038175529884885715)
  ·
    refine ⟨80230762557263294827328573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53487175038175529884885715 80230762557263294827328573)
    ·
      refine ⟨30086535958973735560248215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80230762557263294827328573 30086535958973735560248215)
      ·
        refine ⟨45129803938460603340372323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30086535958973735560248215 45129803938460603340372323)
        ·
          refine ⟨67694705907690905010558485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45129803938460603340372323 67694705907690905010558485)
          ·
            refine ⟨3173189339423011172369929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67694705907690905010558485 3173189339423011172369929)
            ·
              refine ⟨2379892004567258379277447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3173189339423011172369929 2379892004567258379277447)
              ·
                refine ⟨3569838006850887568916171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2379892004567258379277447 3569838006850887568916171)
                ·
                  refine ⟨5354757010276331353374257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3569838006850887568916171 5354757010276331353374257)
                  ·
                    refine ⟨4016067757707248515030693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5354757010276331353374257 4016067757707248515030693)
                    ·
                      refine ⟨753012704570109096568255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4016067757707248515030693 753012704570109096568255)
                      ·
                        rfl

theorem cell23_1466487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_1466487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466487 prefixEnd_1466487 := by exact prefixLift 1466487
  have htrace : WordTrace (prefixWord ++ tailWord_1466487) baseStart_1466487 baseEnd_1466487 := by
    simpa [prefixWord, tailWord_1466487, baseEnd_1466487] using wordTrace_append hprefix tailTrace_1466487
  have hstable : (prefixWord ++ tailWord_1466487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466487).length < 2 ^ (prefixWord ++ tailWord_1466487).sum := by decide
  have hdescent : baseEnd_1466487 < baseStart_1466487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466524 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_1466524 : Nat := 118140960795 + 1466524 * 2 ^ 59
def prefixEnd_1466524 : Nat := 4983230072969 + 3 ^ 40 * 1466524 * 2
def baseEnd_1466524 : Nat := 753031703354325451805585

theorem tailTrace_1466524 : CollatzResearch.WordTrace tailWord_1466524 prefixEnd_1466524 753031703354325451805585 := by
  unfold tailWord_1466524
  simp only [CollatzResearch.WordTrace]
  refine ⟨26744262269520742601991313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35659016359360990135988417 26744262269520742601991313)
  ·
    refine ⟨20058196702140556951493485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26744262269520742601991313 20058196702140556951493485)
    ·
      refine ⟨7521823763302708856810057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20058196702140556951493485 7521823763302708856810057)
      ·
        refine ⟨5641367822477031642607543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7521823763302708856810057 5641367822477031642607543)
        ·
          refine ⟨8462051733715547463911315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5641367822477031642607543 8462051733715547463911315)
          ·
            refine ⟨12693077600573321195866973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8462051733715547463911315 12693077600573321195866973)
            ·
              refine ⟨4759904100214995448450115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12693077600573321195866973 4759904100214995448450115)
              ·
                refine ⟨7139856150322493172675173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4759904100214995448450115 7139856150322493172675173)
                ·
                  refine ⟨1338723028185467469876595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7139856150322493172675173 1338723028185467469876595)
                  ·
                    refine ⟨2008084542278201204814893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1338723028185467469876595 2008084542278201204814893)
                    ·
                      refine ⟨753031703354325451805585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2008084542278201204814893 753031703354325451805585)
                      ·
                        rfl

theorem cell23_1466524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_1466524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466524 prefixEnd_1466524 := by exact prefixLift 1466524
  have htrace : WordTrace (prefixWord ++ tailWord_1466524) baseStart_1466524 baseEnd_1466524 := by
    simpa [prefixWord, tailWord_1466524, baseEnd_1466524] using wordTrace_append hprefix tailTrace_1466524
  have hstable : (prefixWord ++ tailWord_1466524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466524).length < 2 ^ (prefixWord ++ tailWord_1466524).sum := by decide
  have hdescent : baseEnd_1466524 < baseStart_1466524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466538 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_1466538 : Nat := 118140960795 + 1466538 * 2 ^ 59
def prefixEnd_1466538 : Nat := 4983230072969 + 3 ^ 40 * 1466538 * 2
def baseEnd_1466538 : Nat := 753038892083488397030521

theorem tailTrace_1466538 : CollatzResearch.WordTrace tailWord_1466538 prefixEnd_1466538 753038892083488397030521 := by
  unfold tailWord_1466538
  simp only [CollatzResearch.WordTrace]
  refine ⟨13372258790247691398748067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35659356773993843729994845 13372258790247691398748067)
  ·
    refine ⟨20058388185371537098122101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13372258790247691398748067 20058388185371537098122101)
    ·
      refine ⟨1880473892378581602948947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20058388185371537098122101 1880473892378581602948947)
      ·
        refine ⟨2820710838567872404423421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880473892378581602948947 2820710838567872404423421)
        ·
          refine ⟨1057766564462952151658783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2820710838567872404423421 1057766564462952151658783)
          ·
            refine ⟨1586649846694428227488175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057766564462952151658783 1586649846694428227488175)
            ·
              refine ⟨2379974770041642341232263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1586649846694428227488175 2379974770041642341232263)
              ·
                refine ⟨3569962155062463511848395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2379974770041642341232263 3569962155062463511848395)
                ·
                  refine ⟨5354943232593695267772593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3569962155062463511848395 5354943232593695267772593)
                  ·
                    refine ⟨4016207424445271450829445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5354943232593695267772593 4016207424445271450829445)
                    ·
                      refine ⟨753038892083488397030521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4016207424445271450829445 753038892083488397030521)
                      ·
                        rfl

theorem cell23_1466538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_1466538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466538 prefixEnd_1466538 := by exact prefixLift 1466538
  have htrace : WordTrace (prefixWord ++ tailWord_1466538) baseStart_1466538 baseEnd_1466538 := by
    simpa [prefixWord, tailWord_1466538, baseEnd_1466538] using wordTrace_append hprefix tailTrace_1466538
  have hstable : (prefixWord ++ tailWord_1466538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466538).length < 2 ^ (prefixWord ++ tailWord_1466538).sum := by decide
  have hdescent : baseEnd_1466538 < baseStart_1466538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466541 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_1466541 : Nat := 118140960795 + 1466541 * 2 ^ 59
def prefixEnd_1466541 : Nat := 4983230072969 + 3 ^ 40 * 1466541 * 2
def baseEnd_1466541 : Nat := 753040432525451885293007

theorem tailTrace_1466541 : CollatzResearch.WordTrace tailWord_1466541 prefixEnd_1466541 753040432525451885293007 := by
  unfold tailWord_1466541
  simp only [CollatzResearch.WordTrace]
  refine ⟨53489144579979897107351477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35659429719986598071567651 53489144579979897107351477)
  ·
    refine ⟨5014607304373115353814201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53489144579979897107351477 5014607304373115353814201)
    ·
      refine ⟨3760955478279836515360651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5014607304373115353814201 3760955478279836515360651)
      ·
        refine ⟨5641433217419754773040977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3760955478279836515360651 5641433217419754773040977)
        ·
          refine ⟨4231074913064816079780733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5641433217419754773040977 4231074913064816079780733)
          ·
            refine ⟨1586653092399306029917775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4231074913064816079780733 1586653092399306029917775)
            ·
              refine ⟨2379979638598959044876663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1586653092399306029917775 2379979638598959044876663)
              ·
                refine ⟨3569969457898438567314995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2379979638598959044876663 3569969457898438567314995)
                ·
                  refine ⟨5354954186847657850972493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3569969457898438567314995 5354954186847657850972493)
                  ·
                    refine ⟨2008107820067871694114685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5354954186847657850972493 2008107820067871694114685)
                    ·
                      refine ⟨753040432525451885293007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2008107820067871694114685 753040432525451885293007)
                      ·
                        rfl

theorem cell23_1466541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_1466541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466541 prefixEnd_1466541 := by exact prefixLift 1466541
  have htrace : WordTrace (prefixWord ++ tailWord_1466541) baseStart_1466541 baseEnd_1466541 := by
    simpa [prefixWord, tailWord_1466541, baseEnd_1466541] using wordTrace_append hprefix tailTrace_1466541
  have hstable : (prefixWord ++ tailWord_1466541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466541).length < 2 ^ (prefixWord ++ tailWord_1466541).sum := by decide
  have hdescent : baseEnd_1466541 < baseStart_1466541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466551 : List Nat := [1, 1, 3, 1, 4, 3, 2, 2, 1, 3, 2]
def baseStart_1466551 : Nat := 118140960795 + 1466551 * 2 ^ 59
def prefixEnd_1466551 : Nat := 4983230072969 + 3 ^ 40 * 1466551 * 2
def baseEnd_1466551 : Nat := 753045567331996846167961

theorem tailTrace_1466551 : CollatzResearch.WordTrace tailWord_1466551 prefixEnd_1466551 753045567331996846167961 := by
  unfold tailWord_1466551
  simp only [CollatzResearch.WordTrace]
  refine ⟨53489509309943668815215507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35659672873295779210143671 53489509309943668815215507)
  ·
    refine ⟨80234263964915503222823261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53489509309943668815215507 80234263964915503222823261)
    ·
      refine ⟨30087848986843313708558723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80234263964915503222823261 30087848986843313708558723)
      ·
        refine ⟨45131773480264970562838085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30087848986843313708558723 45131773480264970562838085)
        ·
          refine ⟨8462207527549681980532141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45131773480264970562838085 8462207527549681980532141)
          ·
            refine ⟨3173327822831130742699553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8462207527549681980532141 3173327822831130742699553)
            ·
              refine ⟨2379995867123348057024665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3173327822831130742699553 2379995867123348057024665)
              ·
                refine ⟨1784996900342511042768499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2379995867123348057024665 1784996900342511042768499)
                ·
                  refine ⟨2677495350513766564152749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1784996900342511042768499 2677495350513766564152749)
                  ·
                    refine ⟨1004060756442662461557281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2677495350513766564152749 1004060756442662461557281)
                    ·
                      refine ⟨753045567331996846167961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1004060756442662461557281 753045567331996846167961)
                      ·
                        rfl

theorem cell23_1466551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 3, 2].length) (baseStart_1466551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466551 prefixEnd_1466551 := by exact prefixLift 1466551
  have htrace : WordTrace (prefixWord ++ tailWord_1466551) baseStart_1466551 baseEnd_1466551 := by
    simpa [prefixWord, tailWord_1466551, baseEnd_1466551] using wordTrace_append hprefix tailTrace_1466551
  have hstable : (prefixWord ++ tailWord_1466551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466551).length < 2 ^ (prefixWord ++ tailWord_1466551).sum := by decide
  have hdescent : baseEnd_1466551 < baseStart_1466551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466677 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 8]
def baseStart_1466677 : Nat := 118140960795 + 1466677 * 2 ^ 59
def prefixEnd_1466677 : Nat := 4983230072969 + 3 ^ 40 * 1466677 * 2
def baseEnd_1466677 : Nat := 83678918432718150354709

theorem tailTrace_1466677 : CollatzResearch.WordTrace tailWord_1466677 prefixEnd_1466677 83678918432718150354709 := by
  unfold tailWord_1466677
  simp only [CollatzResearch.WordTrace]
  refine ⟨53494104907487192334302285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35662736604991461556201523 53494104907487192334302285)
  ·
    refine ⟨20060289340307697125363357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53494104907487192334302285 20060289340307697125363357)
    ·
      refine ⟨7522608502615386422011259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20060289340307697125363357 7522608502615386422011259)
      ·
        refine ⟨11283912753923079633016889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7522608502615386422011259 11283912753923079633016889)
        ·
          refine ⟨8462934565442309724762667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11283912753923079633016889 8462934565442309724762667)
          ·
            refine ⟨12694401848163464587144001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8462934565442309724762667 12694401848163464587144001)
            ·
              refine ⟨9520801386122598440358001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12694401848163464587144001 9520801386122598440358001)
              ·
                refine ⟨7140601039591948830268501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9520801386122598440358001 7140601039591948830268501)
                ·
                  refine ⟨83678918432718150354709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7140601039591948830268501 83678918432718150354709)
                  ·
                    rfl

theorem cell23_1466677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 8].length) (baseStart_1466677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466677 prefixEnd_1466677 := by exact prefixLift 1466677
  have htrace : WordTrace (prefixWord ++ tailWord_1466677) baseStart_1466677 baseEnd_1466677 := by
    simpa [prefixWord, tailWord_1466677, baseEnd_1466677] using wordTrace_append hprefix tailTrace_1466677
  have hstable : (prefixWord ++ tailWord_1466677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466677).length < 2 ^ (prefixWord ++ tailWord_1466677).sum := by decide
  have hdescent : baseEnd_1466677 < baseStart_1466677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466707 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 3, 5]
def baseStart_1466707 : Nat := 118140960795 + 1466707 * 2 ^ 59
def prefixEnd_1466707 : Nat := 4983230072969 + 3 ^ 40 * 1466707 * 2
def baseEnd_1466707 : Nat := 251041890104699411939081

theorem tailTrace_1466707 : CollatzResearch.WordTrace tailWord_1466707 prefixEnd_1466707 251041890104699411939081 := by
  unfold tailWord_1466707
  simp only [CollatzResearch.WordTrace]
  refine ⟨53495199097378507457894375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35663466064919004971929583 53495199097378507457894375)
  ·
    refine ⟨80242798646067761186841563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53495199097378507457894375 80242798646067761186841563)
    ·
      refine ⟨120364197969101641780262345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80242798646067761186841563 120364197969101641780262345)
      ·
        refine ⟨90273148476826231335196759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120364197969101641780262345 90273148476826231335196759)
        ·
          refine ⟨135409722715239347002795139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90273148476826231335196759 135409722715239347002795139)
          ·
            refine ⟨203114584072859020504192709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135409722715239347002795139 203114584072859020504192709)
            ·
              refine ⟨38083984513661066344536133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203114584072859020504192709 38083984513661066344536133)
              ·
                refine ⟨7140747096311449939600525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38083984513661066344536133 7140747096311449939600525)
                ·
                  refine ⟨2677780161116793727350197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7140747096311449939600525 2677780161116793727350197)
                  ·
                    refine ⟨251041890104699411939081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2677780161116793727350197 251041890104699411939081)
                    ·
                      rfl

theorem cell23_1466707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 5].length) (baseStart_1466707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466707 prefixEnd_1466707 := by exact prefixLift 1466707
  have htrace : WordTrace (prefixWord ++ tailWord_1466707) baseStart_1466707 baseEnd_1466707 := by
    simpa [prefixWord, tailWord_1466707, baseEnd_1466707] using wordTrace_append hprefix tailTrace_1466707
  have hstable : (prefixWord ++ tailWord_1466707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466707).length < 2 ^ (prefixWord ++ tailWord_1466707).sum := by decide
  have hdescent : baseEnd_1466707 < baseStart_1466707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466737 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 3, 6]
def baseStart_1466737 : Nat := 118140960795 + 1466737 * 2 ^ 59
def prefixEnd_1466737 : Nat := 4983230072969 + 3 ^ 40 * 1466737 * 2
def baseEnd_1466737 : Nat := 251047024911244372814035

theorem tailTrace_1466737 : CollatzResearch.WordTrace tailWord_1466737 prefixEnd_1466737 251047024911244372814035 := by
  unfold tailWord_1466737
  simp only [CollatzResearch.WordTrace]
  refine ⟨53496293287269822581486465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35664195524846548387657643 53496293287269822581486465)
  ·
    refine ⟨40122219965452366936114849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53496293287269822581486465 40122219965452366936114849)
    ·
      refine ⟨30091664974089275202086137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40122219965452366936114849 30091664974089275202086137)
      ·
        refine ⟨22568748730566956401564603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30091664974089275202086137 22568748730566956401564603)
        ·
          refine ⟨33853123095850434602346905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22568748730566956401564603 33853123095850434602346905)
          ·
            refine ⟨25389842321887825951760179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33853123095850434602346905 25389842321887825951760179)
            ·
              refine ⟨38084763482831738927640269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25389842321887825951760179 38084763482831738927640269)
              ·
                refine ⟨14281786306061902097865101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38084763482831738927640269 14281786306061902097865101)
                ·
                  refine ⟨5355669864773213286699413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14281786306061902097865101 5355669864773213286699413)
                  ·
                    refine ⟨251047024911244372814035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5355669864773213286699413 251047024911244372814035)
                    ·
                      rfl

theorem cell23_1466737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_1466737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466737 prefixEnd_1466737 := by exact prefixLift 1466737
  have htrace : WordTrace (prefixWord ++ tailWord_1466737) baseStart_1466737 baseEnd_1466737 := by
    simpa [prefixWord, tailWord_1466737, baseEnd_1466737] using wordTrace_append hprefix tailTrace_1466737
  have hstable : (prefixWord ++ tailWord_1466737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466737).length < 2 ^ (prefixWord ++ tailWord_1466737).sum := by decide
  have hdescent : baseEnd_1466737 < baseStart_1466737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466741 : List Nat := [1, 3, 4, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1466741 : Nat := 118140960795 + 1466741 * 2 ^ 59
def prefixEnd_1466741 : Nat := 4983230072969 + 3 ^ 40 * 1466741 * 2
def baseEnd_1466741 : Nat := 251047709552117034264029

theorem tailTrace_1466741 : CollatzResearch.WordTrace tailWord_1466741 prefixEnd_1466741 251047709552117034264029 := by
  unfold tailWord_1466741
  simp only [CollatzResearch.WordTrace]
  refine ⟨53496439179255331264632077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35664292786170220843088051 53496439179255331264632077)
  ·
    refine ⟨20061164692220749224237029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53496439179255331264632077 20061164692220749224237029)
    ·
      refine ⟨3761468379791390479544443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20061164692220749224237029 3761468379791390479544443)
      ·
        refine ⟨5642202569687085719316665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3761468379791390479544443 5642202569687085719316665)
        ·
          refine ⟨4231651927265314289487499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5642202569687085719316665 4231651927265314289487499)
          ·
            refine ⟨6347477890897971434231249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4231651927265314289487499 6347477890897971434231249)
            ·
              refine ⟨4760608418173478575673437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6347477890897971434231249 4760608418173478575673437)
              ·
                refine ⟨1785228156815054465877539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4760608418173478575673437 1785228156815054465877539)
                ·
                  refine ⟨2677842235222581698816309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785228156815054465877539 2677842235222581698816309)
                  ·
                    refine ⟨251047709552117034264029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2677842235222581698816309 251047709552117034264029)
                    ·
                      rfl

theorem cell23_1466741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1466741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466741 prefixEnd_1466741 := by exact prefixLift 1466741
  have htrace : WordTrace (prefixWord ++ tailWord_1466741) baseStart_1466741 baseEnd_1466741 := by
    simpa [prefixWord, tailWord_1466741, baseEnd_1466741] using wordTrace_append hprefix tailTrace_1466741
  have hstable : (prefixWord ++ tailWord_1466741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466741).length < 2 ^ (prefixWord ++ tailWord_1466741).sum := by decide
  have hdescent : baseEnd_1466741 < baseStart_1466741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466755 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 3, 1, 3]
def baseStart_1466755 : Nat := 118140960795 + 1466755 * 2 ^ 59
def prefixEnd_1466755 : Nat := 4983230072969 + 3 ^ 40 * 1466755 * 2
def baseEnd_1466755 : Nat := 753150317385514048017023

theorem tailTrace_1466755 : CollatzResearch.WordTrace tailWord_1466755 prefixEnd_1466755 753150317385514048017023 := by
  unfold tailWord_1466755
  simp only [CollatzResearch.WordTrace]
  refine ⟨53496949801204611655641719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35664633200803074437094479 53496949801204611655641719)
  ·
    refine ⟨80245424701806917483462579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53496949801204611655641719 80245424701806917483462579)
    ·
      refine ⟨120368137052710376225193869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80245424701806917483462579 120368137052710376225193869)
      ·
        refine ⟨45138051394766391084447701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120368137052710376225193869 45138051394766391084447701)
        ·
          refine ⟨1057923079564837291041743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 45138051394766391084447701 1057923079564837291041743)
          ·
            refine ⟨1586884619347255936562615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057923079564837291041743 1586884619347255936562615)
            ·
              refine ⟨2380326929020883904843923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1586884619347255936562615 2380326929020883904843923)
              ·
                refine ⟨3570490393531325857265885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2380326929020883904843923 3570490393531325857265885)
                ·
                  refine ⟨1338933897574247196474707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3570490393531325857265885 1338933897574247196474707)
                  ·
                    refine ⟨2008400846361370794712061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1338933897574247196474707 2008400846361370794712061)
                    ·
                      refine ⟨753150317385514048017023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2008400846361370794712061 753150317385514048017023)
                      ·
                        rfl

theorem cell23_1466755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 3, 1, 3].length) (baseStart_1466755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466755 prefixEnd_1466755 := by exact prefixLift 1466755
  have htrace : WordTrace (prefixWord ++ tailWord_1466755) baseStart_1466755 baseEnd_1466755 := by
    simpa [prefixWord, tailWord_1466755, baseEnd_1466755] using wordTrace_append hprefix tailTrace_1466755
  have hstable : (prefixWord ++ tailWord_1466755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466755).length < 2 ^ (prefixWord ++ tailWord_1466755).sum := by decide
  have hdescent : baseEnd_1466755 < baseStart_1466755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466764 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 1, 1, 5]
def baseStart_1466764 : Nat := 118140960795 + 1466764 * 2 ^ 59
def prefixEnd_1466764 : Nat := 4983230072969 + 3 ^ 40 * 1466764 * 2
def baseEnd_1466764 : Nat := 753154938711404512804481

theorem tailTrace_1466764 : CollatzResearch.WordTrace tailWord_1466764 prefixEnd_1466764 753154938711404512804481 := by
  unfold tailWord_1466764
  simp only [CollatzResearch.WordTrace]
  refine ⟨26748639029086003096359673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35664852038781337461812897 26748639029086003096359673)
  ·
    refine ⟨20061479271814502322269755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26748639029086003096359673 20061479271814502322269755)
    ·
      refine ⟨30092218907721753483404633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20061479271814502322269755 30092218907721753483404633)
      ·
        refine ⟨22569164180791315112553475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30092218907721753483404633 22569164180791315112553475)
        ·
          refine ⟨33853746271186972668830213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22569164180791315112553475 33853746271186972668830213)
          ·
            refine ⟨6347577425847557375405665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33853746271186972668830213 6347577425847557375405665)
            ·
              refine ⟨4760683069385668031554249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6347577425847557375405665 4760683069385668031554249)
              ·
                refine ⟨3570512302039251023665687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4760683069385668031554249 3570512302039251023665687)
                ·
                  refine ⟨5355768453058876535498531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3570512302039251023665687 5355768453058876535498531)
                  ·
                    refine ⟨8033652679588314803247797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5355768453058876535498531 8033652679588314803247797)
                    ·
                      refine ⟨753154938711404512804481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8033652679588314803247797 753154938711404512804481)
                      ·
                        rfl

theorem cell23_1466764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_1466764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466764 prefixEnd_1466764 := by exact prefixLift 1466764
  have htrace : WordTrace (prefixWord ++ tailWord_1466764) baseStart_1466764 baseEnd_1466764 := by
    simpa [prefixWord, tailWord_1466764, baseEnd_1466764] using wordTrace_append hprefix tailTrace_1466764
  have hstable : (prefixWord ++ tailWord_1466764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466764).length < 2 ^ (prefixWord ++ tailWord_1466764).sum := by decide
  have hdescent : baseEnd_1466764 < baseStart_1466764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466778 : List Nat := [3, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4]
def baseStart_1466778 : Nat := 118140960795 + 1466778 * 2 ^ 59
def prefixEnd_1466778 : Nat := 4983230072969 + 3 ^ 40 * 1466778 * 2
def baseEnd_1466778 : Nat := 753162127440567458029417

theorem tailTrace_1466778 : CollatzResearch.WordTrace tailWord_1466778 prefixEnd_1466778 753162127440567458029417 := by
  unfold tailWord_1466778
  simp only [CollatzResearch.WordTrace]
  refine ⟨13374447170030321645932247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35665192453414191055819325 13374447170030321645932247)
  ·
    refine ⟨20061670755045482468898371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13374447170030321645932247 20061670755045482468898371)
    ·
      refine ⟨30092506132568223703347557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20061670755045482468898371 30092506132568223703347557)
      ·
        refine ⟨5642344899856541944377667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30092506132568223703347557 5642344899856541944377667)
        ·
          refine ⟨8463517349784812916566501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5642344899856541944377667 8463517349784812916566501)
          ·
            refine ⟨1586909503084652421856219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8463517349784812916566501 1586909503084652421856219)
            ·
              refine ⟨2380364254626978632784329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1586909503084652421856219 2380364254626978632784329)
              ·
                refine ⟨1785273190970233974588247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2380364254626978632784329 1785273190970233974588247)
                ·
                  refine ⟨2677909786455350961882371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785273190970233974588247 2677909786455350961882371)
                  ·
                    refine ⟨4016864679683026442823557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2677909786455350961882371 4016864679683026442823557)
                    ·
                      refine ⟨753162127440567458029417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4016864679683026442823557 753162127440567458029417)
                      ·
                        rfl

theorem cell23_1466778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_1466778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466778 prefixEnd_1466778 := by exact prefixLift 1466778
  have htrace : WordTrace (prefixWord ++ tailWord_1466778) baseStart_1466778 baseEnd_1466778 := by
    simpa [prefixWord, tailWord_1466778, baseEnd_1466778] using wordTrace_append hprefix tailTrace_1466778
  have hstable : (prefixWord ++ tailWord_1466778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466778).length < 2 ^ (prefixWord ++ tailWord_1466778).sum := by decide
  have hdescent : baseEnd_1466778 < baseStart_1466778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466791 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_1466791 : Nat := 118140960795 + 1466791 * 2 ^ 59
def prefixEnd_1466791 : Nat := 4983230072969 + 3 ^ 40 * 1466791 * 2
def baseEnd_1466791 : Nat := 753168802689075907166857

theorem tailTrace_1466791 : CollatzResearch.WordTrace tailWord_1466791 prefixEnd_1466791 753168802689075907166857 := by
  unfold tailWord_1466791
  simp only [CollatzResearch.WordTrace]
  refine ⟨53498262829074189803952227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35665508552716126535968151 53498262829074189803952227)
  ·
    refine ⟨80247394243611284705928341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53498262829074189803952227 80247394243611284705928341)
    ·
      refine ⟨3761596605169278970590391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80247394243611284705928341 3761596605169278970590391)
      ·
        refine ⟨5642394907753918455885587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3761596605169278970590391 5642394907753918455885587)
        ·
          refine ⟨8463592361630877683828381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5642394907753918455885587 8463592361630877683828381)
          ·
            refine ⟨3173847135611579131435643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8463592361630877683828381 3173847135611579131435643)
            ·
              refine ⟨4760770703417368697153465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3173847135611579131435643 4760770703417368697153465)
              ·
                refine ⟨3570578027563026522865099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4760770703417368697153465 3570578027563026522865099)
                ·
                  refine ⟨5355867041344539784297649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3570578027563026522865099 5355867041344539784297649)
                  ·
                    refine ⟨4016900281008404838223237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5355867041344539784297649 4016900281008404838223237)
                    ·
                      refine ⟨753168802689075907166857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4016900281008404838223237 753168802689075907166857)
                      ·
                        rfl

theorem cell23_1466791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_1466791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466791 prefixEnd_1466791 := by exact prefixLift 1466791
  have htrace : WordTrace (prefixWord ++ tailWord_1466791) baseStart_1466791 baseEnd_1466791 := by
    simpa [prefixWord, tailWord_1466791, baseEnd_1466791] using wordTrace_append hprefix tailTrace_1466791
  have hstable : (prefixWord ++ tailWord_1466791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466791).length < 2 ^ (prefixWord ++ tailWord_1466791).sum := by decide
  have hdescent : baseEnd_1466791 < baseStart_1466791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466812 : List Nat := [2, 2, 2, 4, 1, 2, 1, 4, 1, 2, 2]
def baseStart_1466812 : Nat := 118140960795 + 1466812 * 2 ^ 59
def prefixEnd_1466812 : Nat := 4983230072969 + 3 ^ 40 * 1466812 * 2
def baseEnd_1466812 : Nat := 753179585782820325004261

theorem tailTrace_1466812 : CollatzResearch.WordTrace tailWord_1466812 prefixEnd_1466812 753179585782820325004261 := by
  unfold tailWord_1466812
  simp only [CollatzResearch.WordTrace]
  refine ⟨26749514380999055195233345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35666019174665406926977793 26749514380999055195233345)
  ·
    refine ⟨20062135785749291396425009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26749514380999055195233345 20062135785749291396425009)
    ·
      refine ⟨15046601839311968547318757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20062135785749291396425009 15046601839311968547318757)
      ·
        refine ⟨2821237844870994102622267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15046601839311968547318757 2821237844870994102622267)
        ·
          refine ⟨4231856767306491153933401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2821237844870994102622267 4231856767306491153933401)
          ·
            refine ⟨3173892575479868365450051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4231856767306491153933401 3173892575479868365450051)
            ·
              refine ⟨4760838863219802548175077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3173892575479868365450051 4760838863219802548175077)
              ·
                refine ⟨892657286853712977782827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4760838863219802548175077 892657286853712977782827)
                ·
                  refine ⟨1338985930280569466674241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 892657286853712977782827 1338985930280569466674241)
                  ·
                    refine ⟨1004239447710427100005681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1338985930280569466674241 1004239447710427100005681)
                    ·
                      refine ⟨753179585782820325004261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1004239447710427100005681 753179585782820325004261)
                      ·
                        rfl

theorem cell23_1466812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_1466812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466812 prefixEnd_1466812 := by exact prefixLift 1466812
  have htrace : WordTrace (prefixWord ++ tailWord_1466812) baseStart_1466812 baseEnd_1466812 := by
    simpa [prefixWord, tailWord_1466812, baseEnd_1466812] using wordTrace_append hprefix tailTrace_1466812
  have hstable : (prefixWord ++ tailWord_1466812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466812).length < 2 ^ (prefixWord ++ tailWord_1466812).sum := by decide
  have hdescent : baseEnd_1466812 < baseStart_1466812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466814 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_1466814 : Nat := 118140960795 + 1466814 * 2 ^ 59
def prefixEnd_1466814 : Nat := 4983230072969 + 3 ^ 40 * 1466814 * 2
def baseEnd_1466814 : Nat := 251060204248043105726417

theorem tailTrace_1466814 : CollatzResearch.WordTrace tailWord_1466814 prefixEnd_1466814 251060204248043105726417 := by
  unfold tailWord_1466814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6687387713498858091504937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35666067805327243154692997 6687387713498858091504937)
  ·
    refine ⟨5015540785124143568628703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6687387713498858091504937 5015540785124143568628703)
    ·
      refine ⟨7523311177686215352943055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5015540785124143568628703 7523311177686215352943055)
      ·
        refine ⟨11284966766529323029414583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7523311177686215352943055 11284966766529323029414583)
        ·
          refine ⟨16927450149793984544121875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11284966766529323029414583 16927450149793984544121875)
          ·
            refine ⟨25391175224690976816182813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16927450149793984544121875 25391175224690976816182813)
            ·
              refine ⟨9521690709259116306068555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25391175224690976816182813 9521690709259116306068555)
              ·
                refine ⟨14282536063888674459102833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9521690709259116306068555 14282536063888674459102833)
                ·
                  refine ⟨10711902047916505844327125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14282536063888674459102833 10711902047916505844327125)
                  ·
                    refine ⟨251060204248043105726417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10711902047916505844327125 251060204248043105726417)
                    ·
                      rfl

theorem cell23_1466814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_1466814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466814 prefixEnd_1466814 := by exact prefixLift 1466814
  have htrace : WordTrace (prefixWord ++ tailWord_1466814) baseStart_1466814 baseEnd_1466814 := by
    simpa [prefixWord, tailWord_1466814, baseEnd_1466814] using wordTrace_append hprefix tailTrace_1466814
  have hstable : (prefixWord ++ tailWord_1466814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466814).length < 2 ^ (prefixWord ++ tailWord_1466814).sum := by decide
  have hdescent : baseEnd_1466814 < baseStart_1466814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466828 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 1, 3, 3]
def baseStart_1466828 : Nat := 118140960795 + 1466828 * 2 ^ 59
def prefixEnd_1466828 : Nat := 4983230072969 + 3 ^ 40 * 1466828 * 2
def baseEnd_1466828 : Nat := 753187801473292262404187

theorem tailTrace_1466828 : CollatzResearch.WordTrace tailWord_1466828 prefixEnd_1466828 753187801473292262404187 := by
  unfold tailWord_1466828
  simp only [CollatzResearch.WordTrace]
  refine ⟨26749806164970072561524569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35666408219960096748699425 26749806164970072561524569)
  ·
    refine ⟨20062354623727554421143427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26749806164970072561524569 20062354623727554421143427)
    ·
      refine ⟨30093531935591331631715141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20062354623727554421143427 30093531935591331631715141)
      ·
        refine ⟨5642537237923374680946589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30093531935591331631715141 5642537237923374680946589)
        ·
          refine ⟨2115951464221265505354971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5642537237923374680946589 2115951464221265505354971)
          ·
            refine ⟨3173927196331898258032457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115951464221265505354971 3173927196331898258032457)
            ·
              refine ⟨2380445397248923693524343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3173927196331898258032457 2380445397248923693524343)
              ·
                refine ⟨3570668095873385540286515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2380445397248923693524343 3570668095873385540286515)
                ·
                  refine ⟨5356002143810078310429773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3570668095873385540286515 5356002143810078310429773)
                  ·
                    refine ⟨2008500803928779366411165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5356002143810078310429773 2008500803928779366411165)
                    ·
                      refine ⟨753187801473292262404187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2008500803928779366411165 753187801473292262404187)
                      ·
                        rfl

theorem cell23_1466828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_1466828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466828 prefixEnd_1466828 := by exact prefixLift 1466828
  have htrace : WordTrace (prefixWord ++ tailWord_1466828) baseStart_1466828 baseEnd_1466828 := by
    simpa [prefixWord, tailWord_1466828, baseEnd_1466828] using wordTrace_append hprefix tailTrace_1466828
  have hstable : (prefixWord ++ tailWord_1466828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466828).length < 2 ^ (prefixWord ++ tailWord_1466828).sum := by decide
  have hdescent : baseEnd_1466828 < baseStart_1466828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466861 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_1466861 : Nat := 118140960795 + 1466861 * 2 ^ 59
def prefixEnd_1466861 : Nat := 4983230072969 + 3 ^ 40 * 1466861 * 2
def baseEnd_1466861 : Nat := 251068248778296877763845

theorem tailTrace_1466861 : CollatzResearch.WordTrace tailWord_1466861 prefixEnd_1466861 251068248778296877763845 := by
  unfold tailWord_1466861
  simp only [CollatzResearch.WordTrace]
  refine ⟨53500815938820591759000437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35667210625880394506000291 53500815938820591759000437)
  ·
    refine ⟨5015701494264430477406291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53500815938820591759000437 5015701494264430477406291)
    ·
      refine ⟨7523552241396645716109437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5015701494264430477406291 7523552241396645716109437)
      ·
        refine ⟨2821332090523742143541039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7523552241396645716109437 2821332090523742143541039)
        ·
          refine ⟨4231998135785613215311559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2821332090523742143541039 4231998135785613215311559)
          ·
            refine ⟨6347997203678419822967339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4231998135785613215311559 6347997203678419822967339)
            ·
              refine ⟨9521995805517629734451009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6347997203678419822967339 9521995805517629734451009)
              ·
                refine ⟨7141496854138222300838257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9521995805517629734451009 7141496854138222300838257)
                ·
                  refine ⟨5356122640603666725628693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7141496854138222300838257 5356122640603666725628693)
                  ·
                    refine ⟨251068248778296877763845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5356122640603666725628693 251068248778296877763845)
                    ·
                      rfl

theorem cell23_1466861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_1466861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466861 prefixEnd_1466861 := by exact prefixLift 1466861
  have htrace : WordTrace (prefixWord ++ tailWord_1466861) baseStart_1466861 baseEnd_1466861 := by
    simpa [prefixWord, tailWord_1466861, baseEnd_1466861] using wordTrace_append hprefix tailTrace_1466861
  have hstable : (prefixWord ++ tailWord_1466861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466861).length < 2 ^ (prefixWord ++ tailWord_1466861).sum := by decide
  have hdescent : baseEnd_1466861 < baseStart_1466861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466864 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 4]
def baseStart_1466864 : Nat := 118140960795 + 1466864 * 2 ^ 59
def prefixEnd_1466864 : Nat := 4983230072969 + 3 ^ 40 * 1466864 * 2
def baseEnd_1466864 : Nat := 753206286776854121554021

theorem tailTrace_1466864 : CollatzResearch.WordTrace tailWord_1466864 prefixEnd_1466864 753206286776854121554021 := by
  unfold tailWord_1466864
  simp only [CollatzResearch.WordTrace]
  refine ⟨26750462678904861635679823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35667283571873148847573097 26750462678904861635679823)
  ·
    refine ⟨40125694018357292453519735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26750462678904861635679823 40125694018357292453519735)
    ·
      refine ⟨60188541027535938680279603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40125694018357292453519735 60188541027535938680279603)
      ·
        refine ⟨90282811541303908020419405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60188541027535938680279603 90282811541303908020419405)
        ·
          refine ⟨33856054327988965507657277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90282811541303908020419405 33856054327988965507657277)
          ·
            refine ⟨12696020372995862065371479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33856054327988965507657277 12696020372995862065371479)
            ·
              refine ⟨19044030559493793098057219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12696020372995862065371479 19044030559493793098057219)
              ·
                refine ⟨28566045839240689647085829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19044030559493793098057219 28566045839240689647085829)
                ·
                  refine ⟨5356133594857629308828593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28566045839240689647085829 5356133594857629308828593)
                  ·
                    refine ⟨4017100196143221981621445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5356133594857629308828593 4017100196143221981621445)
                    ·
                      refine ⟨753206286776854121554021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4017100196143221981621445 753206286776854121554021)
                      ·
                        rfl

theorem cell23_1466864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_1466864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466864 prefixEnd_1466864 := by exact prefixLift 1466864
  have htrace : WordTrace (prefixWord ++ tailWord_1466864) baseStart_1466864 baseEnd_1466864 := by
    simpa [prefixWord, tailWord_1466864, baseEnd_1466864] using wordTrace_append hprefix tailTrace_1466864
  have hstable : (prefixWord ++ tailWord_1466864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466864).length < 2 ^ (prefixWord ++ tailWord_1466864).sum := by decide
  have hdescent : baseEnd_1466864 < baseStart_1466864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466881 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_1466881 : Nat := 118140960795 + 1466881 * 2 ^ 59
def prefixEnd_1466881 : Nat := 4983230072969 + 3 ^ 40 * 1466881 * 2
def baseEnd_1466881 : Nat := 753215015947980555041443

theorem tailTrace_1466881 : CollatzResearch.WordTrace tailWord_1466881 prefixEnd_1466881 753215015947980555041443 := by
  unfold tailWord_1466881
  simp only [CollatzResearch.WordTrace]
  refine ⟨53501545398748135174728497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35667696932498756783152331 53501545398748135174728497)
  ·
    refine ⟨40126159049061101381046373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53501545398748135174728497 40126159049061101381046373)
    ·
      refine ⟨7523654821698956508946195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40126159049061101381046373 7523654821698956508946195)
      ·
        refine ⟨11285482232548434763419293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7523654821698956508946195 11285482232548434763419293)
        ·
          refine ⟨4232055837205663036282235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11285482232548434763419293 4232055837205663036282235)
          ·
            refine ⟨6348083755808494554423353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4232055837205663036282235 6348083755808494554423353)
            ·
              refine ⟨4761062816856370915817515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6348083755808494554423353 4761062816856370915817515)
              ·
                refine ⟨7141594225284556373726273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4761062816856370915817515 7141594225284556373726273)
                ·
                  refine ⟨5356195668963417280294705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7141594225284556373726273 5356195668963417280294705)
                  ·
                    refine ⟨4017146751722562960221029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5356195668963417280294705 4017146751722562960221029)
                    ·
                      refine ⟨753215015947980555041443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4017146751722562960221029 753215015947980555041443)
                      ·
                        rfl

theorem cell23_1466881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_1466881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466881 prefixEnd_1466881 := by exact prefixLift 1466881
  have htrace : WordTrace (prefixWord ++ tailWord_1466881) baseStart_1466881 baseEnd_1466881 := by
    simpa [prefixWord, tailWord_1466881, baseEnd_1466881] using wordTrace_append hprefix tailTrace_1466881
  have hstable : (prefixWord ++ tailWord_1466881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466881).length < 2 ^ (prefixWord ++ tailWord_1466881).sum := by decide
  have hdescent : baseEnd_1466881 < baseStart_1466881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466908 : List Nat := [2, 2, 3, 1, 2, 2, 3, 3, 5]
def baseStart_1466908 : Nat := 118140960795 + 1466908 * 2 ^ 59
def prefixEnd_1466908 : Nat := 4983230072969 + 3 ^ 40 * 1466908 * 2
def baseEnd_1466908 : Nat := 83692097769516883267091

theorem tailTrace_1466908 : CollatzResearch.WordTrace tailWord_1466908 prefixEnd_1466908 83692097769516883267091 := by
  unfold tailWord_1466908
  simp only [CollatzResearch.WordTrace]
  refine ⟨26751265084825159392980689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35668353446433545857307585 26751265084825159392980689)
  ·
    refine ⟨20063448813618869544735517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26751265084825159392980689 20063448813618869544735517)
    ·
      refine ⟨7523793305107076079275819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20063448813618869544735517 7523793305107076079275819)
      ·
        refine ⟨11285689957660614118913729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7523793305107076079275819 11285689957660614118913729)
        ·
          refine ⟨8464267468245460589185297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11285689957660614118913729 8464267468245460589185297)
          ·
            refine ⟨6348200601184095441888973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8464267468245460589185297 6348200601184095441888973)
            ·
              refine ⟨2380575225444035790708365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6348200601184095441888973 2380575225444035790708365)
              ·
                refine ⟨892715709541513421515637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2380575225444035790708365 892715709541513421515637)
                ·
                  refine ⟨83692097769516883267091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 892715709541513421515637 83692097769516883267091)
                  ·
                    rfl

theorem cell23_1466908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 5].length) (baseStart_1466908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466908 prefixEnd_1466908 := by exact prefixLift 1466908
  have htrace : WordTrace (prefixWord ++ tailWord_1466908) baseStart_1466908 baseEnd_1466908 := by
    simpa [prefixWord, tailWord_1466908, baseEnd_1466908] using wordTrace_append hprefix tailTrace_1466908
  have hstable : (prefixWord ++ tailWord_1466908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466908).length < 2 ^ (prefixWord ++ tailWord_1466908).sum := by decide
  have hdescent : baseEnd_1466908 < baseStart_1466908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466911 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 1, 7, 2]
def baseStart_1466911 : Nat := 118140960795 + 1466911 * 2 ^ 59
def prefixEnd_1466911 : Nat := 4983230072969 + 3 ^ 40 * 1466911 * 2
def baseEnd_1466911 : Nat := 753230420367615437666305

theorem tailTrace_1466911 : CollatzResearch.WordTrace tailWord_1466911 prefixEnd_1466911 753230420367615437666305 := by
  unfold tailWord_1466911
  simp only [CollatzResearch.WordTrace]
  refine ⟨53502639588639450298320587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35668426392426300198880391 53502639588639450298320587)
  ·
    refine ⟨80253959382959175447480881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53502639588639450298320587 80253959382959175447480881)
    ·
      refine ⟨60190469537219381585610661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80253959382959175447480881 60190469537219381585610661)
      ·
        refine ⟨11285713038228634047301999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60190469537219381585610661 11285713038228634047301999)
        ·
          refine ⟨16928569557342951070952999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11285713038228634047301999 16928569557342951070952999)
          ·
            refine ⟨25392854336014426606429499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16928569557342951070952999 25392854336014426606429499)
            ·
              refine ⟨38089281504021639909644249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25392854336014426606429499 38089281504021639909644249)
              ·
                refine ⟨28566961128016229932233187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38089281504021639909644249 28566961128016229932233187)
                ·
                  refine ⟨42850441692024344898349781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28566961128016229932233187 42850441692024344898349781)
                  ·
                    refine ⟨1004307227156820583555073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42850441692024344898349781 1004307227156820583555073)
                    ·
                      refine ⟨753230420367615437666305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1004307227156820583555073 753230420367615437666305)
                      ·
                        rfl

theorem cell23_1466911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_1466911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1466911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1466911 prefixEnd_1466911 := by exact prefixLift 1466911
  have htrace : WordTrace (prefixWord ++ tailWord_1466911) baseStart_1466911 baseEnd_1466911 := by
    simpa [prefixWord, tailWord_1466911, baseEnd_1466911] using wordTrace_append hprefix tailTrace_1466911
  have hstable : (prefixWord ++ tailWord_1466911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466911).length < 2 ^ (prefixWord ++ tailWord_1466911).sum := by decide
  have hdescent : baseEnd_1466911 < baseStart_1466911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467008 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 5, 1, 3]
def baseStart_1467008 : Nat := 118140960795 + 1467008 * 2 ^ 59
def prefixEnd_1467008 : Nat := 4983230072969 + 3 ^ 40 * 1467008 * 2
def baseEnd_1467008 : Nat := 753280227991101558153359

theorem tailTrace_1467008 : CollatzResearch.WordTrace tailWord_1467008 prefixEnd_1467008 753280227991101558153359 := by
  unfold tailWord_1467008
  simp only [CollatzResearch.WordTrace]
  refine ⟨26753088734644017932300839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35670784979525357243067785 26753088734644017932300839)
  ·
    refine ⟨40129633101966026898451259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26753088734644017932300839 40129633101966026898451259)
    ·
      refine ⟨60194449652949040347676889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40129633101966026898451259 60194449652949040347676889)
      ·
        refine ⟨45145837239711780260757667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60194449652949040347676889 45145837239711780260757667)
        ·
          refine ⟨67718755859567670391136501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45145837239711780260757667 67718755859567670391136501)
          ·
            refine ⟨6348633361834469099169047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67718755859567670391136501 6348633361834469099169047)
            ·
              refine ⟨9522950042751703648753571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6348633361834469099169047 9522950042751703648753571)
              ·
                refine ⟨14284425064127555473130357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9522950042751703648753571 14284425064127555473130357)
                ·
                  refine ⟨1339164849761958325605971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14284425064127555473130357 1339164849761958325605971)
                  ·
                    refine ⟨2008747274642937488408957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1339164849761958325605971 2008747274642937488408957)
                    ·
                      refine ⟨753280227991101558153359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2008747274642937488408957 753280227991101558153359)
                      ·
                        rfl

theorem cell23_1467008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_1467008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467008 prefixEnd_1467008 := by exact prefixLift 1467008
  have htrace : WordTrace (prefixWord ++ tailWord_1467008) baseStart_1467008 baseEnd_1467008 := by
    simpa [prefixWord, tailWord_1467008, baseEnd_1467008] using wordTrace_append hprefix tailTrace_1467008
  have hstable : (prefixWord ++ tailWord_1467008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467008).length < 2 ^ (prefixWord ++ tailWord_1467008).sum := by decide
  have hdescent : baseEnd_1467008 < baseStart_1467008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467011 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 3, 5]
def baseStart_1467011 : Nat := 118140960795 + 1467011 * 2 ^ 59
def prefixEnd_1467011 : Nat := 4983230072969 + 3 ^ 40 * 1467011 * 2
def baseEnd_1467011 : Nat := 251093922811021682138615

theorem tailTrace_1467011 : CollatzResearch.WordTrace tailWord_1467011 prefixEnd_1467011 251093922811021682138615 := by
  unfold tailWord_1467011
  simp only [CollatzResearch.WordTrace]
  refine ⟨53506286888277167376960887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35670857925518111584640591 53506286888277167376960887)
  ·
    refine ⟨80259430332415751065441331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53506286888277167376960887 80259430332415751065441331)
    ·
      refine ⟨120389145498623626598161997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80259430332415751065441331 120389145498623626598161997)
      ·
        refine ⟨45145929561983859974310749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120389145498623626598161997 45145929561983859974310749)
        ·
          refine ⟨16929723585743947490366531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45145929561983859974310749 16929723585743947490366531)
          ·
            refine ⟨25394585378615921235549797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16929723585743947490366531 25394585378615921235549797)
            ·
              refine ⟨4761484758490485231665587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25394585378615921235549797 4761484758490485231665587)
              ·
                refine ⟨7142227137735727847498381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4761484758490485231665587 7142227137735727847498381)
                ·
                  refine ⟨2678335176650897942811893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7142227137735727847498381 2678335176650897942811893)
                  ·
                    refine ⟨251093922811021682138615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2678335176650897942811893 251093922811021682138615)
                    ·
                      rfl

theorem cell23_1467011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 5].length) (baseStart_1467011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467011 prefixEnd_1467011 := by exact prefixLift 1467011
  have htrace : WordTrace (prefixWord ++ tailWord_1467011) baseStart_1467011 baseEnd_1467011 := by
    simpa [prefixWord, tailWord_1467011, baseEnd_1467011] using wordTrace_append hprefix tailTrace_1467011
  have hstable : (prefixWord ++ tailWord_1467011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467011).length < 2 ^ (prefixWord ++ tailWord_1467011).sum := by decide
  have hdescent : baseEnd_1467011 < baseStart_1467011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467071 : List Nat := [1, 1, 2, 2, 2, 5, 1, 9]
def baseStart_1467071 : Nat := 118140960795 + 1467071 * 2 ^ 59
def prefixEnd_1467071 : Nat := 4983230072969 + 3 ^ 40 * 1467071 * 2
def baseEnd_1467071 : Nat := 27900465824901289320947

theorem tailTrace_1467071 : CollatzResearch.WordTrace tailWord_1467071 prefixEnd_1467071 27900465824901289320947 := by
  unfold tailWord_1467071
  simp only [CollatzResearch.WordTrace]
  refine ⟨53508475268059797624145067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35672316845373198416096711 53508475268059797624145067)
  ·
    refine ⟨80262712902089696436217601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53508475268059797624145067 80262712902089696436217601)
    ·
      refine ⟨60197034676567272327163201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80262712902089696436217601 60197034676567272327163201)
      ·
        refine ⟨45147776007425454245372401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60197034676567272327163201 45147776007425454245372401)
        ·
          refine ⟨33860832005569090684029301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45147776007425454245372401 33860832005569090684029301)
          ·
            refine ⟨3174453000522102251627747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33860832005569090684029301 3174453000522102251627747)
            ·
              refine ⟨4761679500783153377441621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3174453000522102251627747 4761679500783153377441621)
              ·
                refine ⟨27900465824901289320947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4761679500783153377441621 27900465824901289320947)
                ·
                  rfl

theorem cell23_1467071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 9].length) (baseStart_1467071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467071 prefixEnd_1467071 := by exact prefixLift 1467071
  have htrace : WordTrace (prefixWord ++ tailWord_1467071) baseStart_1467071 baseEnd_1467071 := by
    simpa [prefixWord, tailWord_1467071, baseEnd_1467071] using wordTrace_append hprefix tailTrace_1467071
  have hstable : (prefixWord ++ tailWord_1467071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467071).length < 2 ^ (prefixWord ++ tailWord_1467071).sum := by decide
  have hdescent : baseEnd_1467071 < baseStart_1467071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467168 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1467168 : Nat := 118140960795 + 1467168 * 2 ^ 59
def prefixEnd_1467168 : Nat := 4983230072969 + 3 ^ 40 * 1467168 * 2
def baseEnd_1467168 : Nat := 753362384895820932152623

theorem tailTrace_1467168 : CollatzResearch.WordTrace tailWord_1467168 prefixEnd_1467168 753362384895820932152623 := by
  unfold tailWord_1467168
  simp only [CollatzResearch.WordTrace]
  refine ⟨26756006574354191595213079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35674675432472255460284105 26756006574354191595213079)
  ·
    refine ⟨40134009861531287392819619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26756006574354191595213079 40134009861531287392819619)
    ·
      refine ⟨60201014792296931089229429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40134009861531287392819619 60201014792296931089229429)
      ·
        refine ⟨5643845136777837289615259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60201014792296931089229429 5643845136777837289615259)
        ·
          refine ⟨8465767705166755934422889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5643845136777837289615259 8465767705166755934422889)
          ·
            refine ⟨6349325778875066950817167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8465767705166755934422889 6349325778875066950817167)
            ·
              refine ⟨9523988668312600426225751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6349325778875066950817167 9523988668312600426225751)
              ·
                refine ⟨14285983002468900639338627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9523988668312600426225751 14285983002468900639338627)
                ·
                  refine ⟨21428974503703350959007941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14285983002468900639338627 21428974503703350959007941)
                  ·
                    refine ⟨4017932719444378304813989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21428974503703350959007941 4017932719444378304813989)
                    ·
                      refine ⟨753362384895820932152623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4017932719444378304813989 753362384895820932152623)
                      ·
                        rfl

theorem cell23_1467168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1467168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467168 prefixEnd_1467168 := by exact prefixLift 1467168
  have htrace : WordTrace (prefixWord ++ tailWord_1467168) baseStart_1467168 baseEnd_1467168 := by
    simpa [prefixWord, tailWord_1467168, baseEnd_1467168] using wordTrace_append hprefix tailTrace_1467168
  have hstable : (prefixWord ++ tailWord_1467168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467168).length < 2 ^ (prefixWord ++ tailWord_1467168).sum := by decide
  have hdescent : baseEnd_1467168 < baseStart_1467168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467208 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 4, 5]
def baseStart_1467208 : Nat := 118140960795 + 1467208 * 2 ^ 59
def prefixEnd_1467208 : Nat := 4983230072969 + 3 ^ 40 * 1467208 * 2
def baseEnd_1467208 : Nat := 251127641374000258550813

theorem tailTrace_1467208 : CollatzResearch.WordTrace tailWord_1467208 prefixEnd_1467208 251127641374000258550813 := by
  unfold tailWord_1467208
  simp only [CollatzResearch.WordTrace]
  refine ⟨26756736034281735010941139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35675648045708980014588185 26756736034281735010941139)
  ·
    refine ⟨40135104051422602516411709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26756736034281735010941139 40135104051422602516411709)
    ·
      refine ⟨15050664019283475943654391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40135104051422602516411709 15050664019283475943654391)
      ·
        refine ⟨22575996028925213915481587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15050664019283475943654391 22575996028925213915481587)
        ·
          refine ⟨33863994043387820873222381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22575996028925213915481587 33863994043387820873222381)
          ·
            refine ⟨12698997766270432827458393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33863994043387820873222381 12698997766270432827458393)
            ·
              refine ⟨9524248324702824620593795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12698997766270432827458393 9524248324702824620593795)
              ·
                refine ⟨14286372487054236930890693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9524248324702824620593795 14286372487054236930890693)
                ·
                  refine ⟨2678694841322669424542005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14286372487054236930890693 2678694841322669424542005)
                  ·
                    refine ⟨251127641374000258550813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2678694841322669424542005 251127641374000258550813)
                    ·
                      rfl

theorem cell23_1467208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_1467208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467208 prefixEnd_1467208 := by exact prefixLift 1467208
  have htrace : WordTrace (prefixWord ++ tailWord_1467208) baseStart_1467208 baseEnd_1467208 := by
    simpa [prefixWord, tailWord_1467208, baseEnd_1467208] using wordTrace_append hprefix tailTrace_1467208
  have hstable : (prefixWord ++ tailWord_1467208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467208).length < 2 ^ (prefixWord ++ tailWord_1467208).sum := by decide
  have hdescent : baseEnd_1467208 < baseStart_1467208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467218 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_1467218 : Nat := 118140960795 + 1467218 * 2 ^ 59
def prefixEnd_1467218 : Nat := 4983230072969 + 3 ^ 40 * 1467218 * 2
def baseEnd_1467218 : Nat := 753388058928545736527393

theorem tailTrace_1467218 : CollatzResearch.WordTrace tailWord_1467218 prefixEnd_1467218 753388058928545736527393 := by
  unfold tailWord_1467218
  simp only [CollatzResearch.WordTrace]
  refine ⟨13378459199631810432436577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35675891199018161153164205 13378459199631810432436577)
  ·
    refine ⟨10033844399723857824327433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13378459199631810432436577 10033844399723857824327433)
    ·
      refine ⟨7525383299792893368245575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10033844399723857824327433 7525383299792893368245575)
      ·
        refine ⟨11288074949689340052368363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7525383299792893368245575 11288074949689340052368363)
        ·
          refine ⟨16932112424534010078552545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11288074949689340052368363 16932112424534010078552545)
          ·
            refine ⟨12699084318400507558914409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16932112424534010078552545 12699084318400507558914409)
            ·
              refine ⟨9524313238800380669185807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12699084318400507558914409 9524313238800380669185807)
              ·
                refine ⟨14286469858200571003778711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9524313238800380669185807 14286469858200571003778711)
                ·
                  refine ⟨21429704787300856505668067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14286469858200571003778711 21429704787300856505668067)
                  ·
                    refine ⟨32144557180951284758502101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21429704787300856505668067 32144557180951284758502101)
                    ·
                      refine ⟨753388058928545736527393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32144557180951284758502101 753388058928545736527393)
                      ·
                        rfl

theorem cell23_1467218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_1467218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467218 prefixEnd_1467218 := by exact prefixLift 1467218
  have htrace : WordTrace (prefixWord ++ tailWord_1467218) baseStart_1467218 baseEnd_1467218 := by
    simpa [prefixWord, tailWord_1467218, baseEnd_1467218] using wordTrace_append hprefix tailTrace_1467218
  have hstable : (prefixWord ++ tailWord_1467218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467218).length < 2 ^ (prefixWord ++ tailWord_1467218).sum := by decide
  have hdescent : baseEnd_1467218 < baseStart_1467218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467245 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_1467245 : Nat := 118140960795 + 1467245 * 2 ^ 59
def prefixEnd_1467245 : Nat := 4983230072969 + 3 ^ 40 * 1467245 * 2
def baseEnd_1467245 : Nat := 753401922906217130889769

theorem tailTrace_1467245 : CollatzResearch.WordTrace tailWord_1467245 prefixEnd_1467245 753401922906217130889769 := by
  unfold tailWord_1467245
  simp only [CollatzResearch.WordTrace]
  refine ⟨53514821569429425340979189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35676547712952950227319459 53514821569429425340979189)
  ·
    refine ⟨5017014522134008625716799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53514821569429425340979189 5017014522134008625716799)
    ·
      refine ⟨7525521783201012938575199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5017014522134008625716799 7525521783201012938575199)
      ·
        refine ⟨11288282674801519407862799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7525521783201012938575199 11288282674801519407862799)
        ·
          refine ⟨16932424012202279111794199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11288282674801519407862799 16932424012202279111794199)
          ·
            refine ⟨25398636018303418667691299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16932424012202279111794199 25398636018303418667691299)
            ·
              refine ⟨38097954027455128001536949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25398636018303418667691299 38097954027455128001536949)
              ·
                refine ⟨3571683190073918250144089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38097954027455128001536949 3571683190073918250144089)
                ·
                  refine ⟨2678762392555438687608067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3571683190073918250144089 2678762392555438687608067)
                  ·
                    refine ⟨4018143588833158031412101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2678762392555438687608067 4018143588833158031412101)
                    ·
                      refine ⟨753401922906217130889769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4018143588833158031412101 753401922906217130889769)
                      ·
                        rfl

theorem cell23_1467245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_1467245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467245 prefixEnd_1467245 := by exact prefixLift 1467245
  have htrace : WordTrace (prefixWord ++ tailWord_1467245) baseStart_1467245 baseEnd_1467245 := by
    simpa [prefixWord, tailWord_1467245, baseEnd_1467245] using wordTrace_append hprefix tailTrace_1467245
  have hstable : (prefixWord ++ tailWord_1467245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467245).length < 2 ^ (prefixWord ++ tailWord_1467245).sum := by decide
  have hdescent : baseEnd_1467245 < baseStart_1467245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467246 : List Nat := [4, 1, 2, 3, 3, 1, 1, 3, 5]
def baseStart_1467246 : Nat := 118140960795 + 1467246 * 2 ^ 59
def prefixEnd_1467246 : Nat := 4983230072969 + 3 ^ 40 * 1467246 * 2
def baseEnd_1467246 : Nat := 83711381820763514108585

theorem tailTrace_1467246 : CollatzResearch.WordTrace tailWord_1467246 prefixEnd_1467246 83711381820763514108585 := by
  unfold tailWord_1467246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6689357255303225313970699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35676572028283868341177061 6689357255303225313970699)
  ·
    refine ⟨10034035882954837970956049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6689357255303225313970699 10034035882954837970956049)
    ·
      refine ⟨7525526912216128478217037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10034035882954837970956049 7525526912216128478217037)
      ·
        refine ⟨2822072592081048179331389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7525526912216128478217037 2822072592081048179331389)
        ·
          refine ⟨1058277222030393067249271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2822072592081048179331389 1058277222030393067249271)
          ·
            refine ⟨1587415833045589600873907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058277222030393067249271 1587415833045589600873907)
            ·
              refine ⟨2381123749568384401310861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587415833045589600873907 2381123749568384401310861)
              ·
                refine ⟨892921406088144150491573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2381123749568384401310861 892921406088144150491573)
                ·
                  refine ⟨83711381820763514108585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 892921406088144150491573 83711381820763514108585)
                  ·
                    rfl

theorem cell23_1467246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_1467246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467246 prefixEnd_1467246 := by exact prefixLift 1467246
  have htrace : WordTrace (prefixWord ++ tailWord_1467246) baseStart_1467246 baseEnd_1467246 := by
    simpa [prefixWord, tailWord_1467246, baseEnd_1467246] using wordTrace_append hprefix tailTrace_1467246
  have hstable : (prefixWord ++ tailWord_1467246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467246).length < 2 ^ (prefixWord ++ tailWord_1467246).sum := by decide
  have hdescent : baseEnd_1467246 < baseStart_1467246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467272 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 3, 4]
def baseStart_1467272 : Nat := 118140960795 + 1467272 * 2 ^ 59
def prefixEnd_1467272 : Nat := 4983230072969 + 3 ^ 40 * 1467272 * 2
def baseEnd_1467272 : Nat := 251138595627962841750715

theorem tailTrace_1467272 : CollatzResearch.WordTrace tailWord_1467272 prefixEnd_1467272 251138595627962841750715 := by
  unfold tailWord_1467272
  simp only [CollatzResearch.WordTrace]
  refine ⟨26757903170165804476106035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35677204226887739301474713 26757903170165804476106035)
  ·
    refine ⟨40136854755248706714159053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26757903170165804476106035 40136854755248706714159053)
    ·
      refine ⟨15051320533218265017809645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40136854755248706714159053 15051320533218265017809645)
      ·
        refine ⟨5644245199956849381678617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15051320533218265017809645 5644245199956849381678617)
        ·
          refine ⟨4233183899967637036258963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5644245199956849381678617 4233183899967637036258963)
          ·
            refine ⟨6349775849951455554388445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4233183899967637036258963 6349775849951455554388445)
            ·
              refine ⟨2381165943731795832895667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6349775849951455554388445 2381165943731795832895667)
              ·
                refine ⟨3571748915597693749343501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2381165943731795832895667 3571748915597693749343501)
                ·
                  refine ⟨1339405843349135156003813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3571748915597693749343501 1339405843349135156003813)
                  ·
                    refine ⟨251138595627962841750715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1339405843349135156003813 251138595627962841750715)
                    ·
                      rfl

theorem cell23_1467272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_1467272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467272 prefixEnd_1467272 := by exact prefixLift 1467272
  have htrace : WordTrace (prefixWord ++ tailWord_1467272) baseStart_1467272 baseEnd_1467272 := by
    simpa [prefixWord, tailWord_1467272, baseEnd_1467272] using wordTrace_append hprefix tailTrace_1467272
  have hstable : (prefixWord ++ tailWord_1467272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467272).length < 2 ^ (prefixWord ++ tailWord_1467272).sum := by decide
  have hdescent : baseEnd_1467272 < baseStart_1467272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467285 : List Nat := [1, 3, 2, 1, 1, 5, 1, 3, 6]
def baseStart_1467285 : Nat := 118140960795 + 1467285 * 2 ^ 59
def prefixEnd_1467285 : Nat := 4983230072969 + 3 ^ 40 * 1467285 * 2
def baseEnd_1467285 : Nat := 83713606903599663821065

theorem tailTrace_1467285 : CollatzResearch.WordTrace tailWord_1467285 prefixEnd_1467285 83713606903599663821065 := by
  unfold tailWord_1467285
  simp only [CollatzResearch.WordTrace]
  refine ⟨53516280489284512172435309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35677520326189674781623539 53516280489284512172435309)
  ·
    refine ⟨20068605183481692064663241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53516280489284512172435309 20068605183481692064663241)
    ·
      refine ⟨15051453887611269048497431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20068605183481692064663241 15051453887611269048497431)
      ·
        refine ⟨22577180831416903572746147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15051453887611269048497431 22577180831416903572746147)
        ·
          refine ⟨33865771247125355359119221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22577180831416903572746147 33865771247125355359119221)
          ·
            refine ⟨3174916054418002064917427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33865771247125355359119221 3174916054418002064917427)
            ·
              refine ⟨4762374081627003097376141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3174916054418002064917427 4762374081627003097376141)
              ·
                refine ⟨1785890280610126161516053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4762374081627003097376141 1785890280610126161516053)
                ·
                  refine ⟨83713606903599663821065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1785890280610126161516053 83713606903599663821065)
                  ·
                    rfl

theorem cell23_1467285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 6].length) (baseStart_1467285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467285 prefixEnd_1467285 := by exact prefixLift 1467285
  have htrace : WordTrace (prefixWord ++ tailWord_1467285) baseStart_1467285 baseEnd_1467285 := by
    simpa [prefixWord, tailWord_1467285, baseEnd_1467285] using wordTrace_append hprefix tailTrace_1467285
  have hstable : (prefixWord ++ tailWord_1467285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467285).length < 2 ^ (prefixWord ++ tailWord_1467285).sum := by decide
  have hdescent : baseEnd_1467285 < baseStart_1467285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467322 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2]
def baseStart_1467322 : Nat := 118140960795 + 1467322 * 2 ^ 59
def prefixEnd_1467322 : Nat := 4983230072969 + 3 ^ 40 * 1467322 * 2
def baseEnd_1467322 : Nat := 753441460916613329626915

theorem tailTrace_1467322 : CollatzResearch.WordTrace tailWord_1467322 prefixEnd_1467322 753441460916613329626915 := by
  unfold tailWord_1467322
  simp only [CollatzResearch.WordTrace]
  refine ⟨13379407497537616872883055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35678419993433644994354813 13379407497537616872883055)
  ·
    refine ⟨20069111246306425309324583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13379407497537616872883055 20069111246306425309324583)
    ·
      refine ⟨30103666869459637963986875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20069111246306425309324583 30103666869459637963986875)
      ·
        refine ⟨45155500304189456945980313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30103666869459637963986875 45155500304189456945980313)
        ·
          refine ⟨33866625228142092709485235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45155500304189456945980313 33866625228142092709485235)
          ·
            refine ⟨50799937842213139064227853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33866625228142092709485235 50799937842213139064227853)
            ·
              refine ⟨19049976690829927149085445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50799937842213139064227853 19049976690829927149085445)
              ·
                refine ⟨3571870629530611340453521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19049976690829927149085445 3571870629530611340453521)
                ·
                  refine ⟨2678902972147958505340141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3571870629530611340453521 2678902972147958505340141)
                  ·
                    refine ⟨1004588614555484439502553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2678902972147958505340141 1004588614555484439502553)
                    ·
                      refine ⟨753441460916613329626915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1004588614555484439502553 753441460916613329626915)
                      ·
                        rfl

theorem cell23_1467322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2].length) (baseStart_1467322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467322 prefixEnd_1467322 := by exact prefixLift 1467322
  have htrace : WordTrace (prefixWord ++ tailWord_1467322) baseStart_1467322 baseEnd_1467322 := by
    simpa [prefixWord, tailWord_1467322, baseEnd_1467322] using wordTrace_append hprefix tailTrace_1467322
  have hstable : (prefixWord ++ tailWord_1467322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467322).length < 2 ^ (prefixWord ++ tailWord_1467322).sum := by decide
  have hdescent : baseEnd_1467322 < baseStart_1467322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467335 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_1467335 : Nat := 118140960795 + 1467335 * 2 ^ 59
def prefixEnd_1467335 : Nat := 4983230072969 + 3 ^ 40 * 1467335 * 2
def baseEnd_1467335 : Nat := 753448136165121778764355

theorem tailTrace_1467335 : CollatzResearch.WordTrace tailWord_1467335 prefixEnd_1467335 753448136165121778764355 := by
  unfold tailWord_1467335
  simp only [CollatzResearch.WordTrace]
  refine ⟨53518104139103370711755459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35678736092735580474503639 53518104139103370711755459)
  ·
    refine ⟨80277156208655056067633189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53518104139103370711755459 80277156208655056067633189)
    ·
      refine ⟨15051966789122823012681223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80277156208655056067633189 15051966789122823012681223)
      ·
        refine ⟨22577950183684234519021835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15051966789122823012681223 22577950183684234519021835)
        ·
          refine ⟨33866925275526351778532753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22577950183684234519021835 33866925275526351778532753)
          ·
            refine ⟨25400193956644763833899565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33866925275526351778532753 25400193956644763833899565)
            ·
              refine ⟨9525072733741786437712337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25400193956644763833899565 9525072733741786437712337)
              ·
                refine ⟨7143804550306339828284253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9525072733741786437712337 7143804550306339828284253)
                ·
                  refine ⟨2678926706364877435606595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7143804550306339828284253 2678926706364877435606595)
                  ·
                    refine ⟨4018390059547316153409893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2678926706364877435606595 4018390059547316153409893)
                    ·
                      refine ⟨753448136165121778764355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4018390059547316153409893 753448136165121778764355)
                      ·
                        rfl

theorem cell23_1467335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_1467335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467335 prefixEnd_1467335 := by exact prefixLift 1467335
  have htrace : WordTrace (prefixWord ++ tailWord_1467335) baseStart_1467335 baseEnd_1467335 := by
    simpa [prefixWord, tailWord_1467335, baseEnd_1467335] using wordTrace_append hprefix tailTrace_1467335
  have hstable : (prefixWord ++ tailWord_1467335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467335).length < 2 ^ (prefixWord ++ tailWord_1467335).sum := by decide
  have hdescent : baseEnd_1467335 < baseStart_1467335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467345 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 1, 6]
def baseStart_1467345 : Nat := 118140960795 + 1467345 * 2 ^ 59
def prefixEnd_1467345 : Nat := 4983230072969 + 3 ^ 40 * 1467345 * 2
def baseEnd_1467345 : Nat := 251151090323888913213103

theorem tailTrace_1467345 : CollatzResearch.WordTrace tailWord_1467345 prefixEnd_1467345 251151090323888913213103 := by
  unfold tailWord_1467345
  simp only [CollatzResearch.WordTrace]
  refine ⟨53518468869067142419619489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35678979246044761613079659 53518468869067142419619489)
  ·
    refine ⟨40138851651800356814714617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53518468869067142419619489 40138851651800356814714617)
    ·
      refine ⟨30104138738850267611035963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40138851651800356814714617 30104138738850267611035963)
      ·
        refine ⟨45156208108275401416553945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30104138738850267611035963 45156208108275401416553945)
        ·
          refine ⟨33867156081206551062415459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45156208108275401416553945 33867156081206551062415459)
          ·
            refine ⟨50800734121809826593623189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33867156081206551062415459 50800734121809826593623189)
            ·
              refine ⟨2381284411959835621576087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50800734121809826593623189 2381284411959835621576087)
              ·
                refine ⟨3571926617939753432364131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2381284411959835621576087 3571926617939753432364131)
                ·
                  refine ⟨5357889926909630148546197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3571926617939753432364131 5357889926909630148546197)
                  ·
                    refine ⟨251151090323888913213103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5357889926909630148546197 251151090323888913213103)
                    ·
                      rfl

theorem cell23_1467345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_1467345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467345 prefixEnd_1467345 := by exact prefixLift 1467345
  have htrace : WordTrace (prefixWord ++ tailWord_1467345) baseStart_1467345 baseEnd_1467345 := by
    simpa [prefixWord, tailWord_1467345, baseEnd_1467345] using wordTrace_append hprefix tailTrace_1467345
  have hstable : (prefixWord ++ tailWord_1467345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467345).length < 2 ^ (prefixWord ++ tailWord_1467345).sum := by decide
  have hdescent : baseEnd_1467345 < baseStart_1467345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467420 : List Nat := [2, 2, 3, 1, 4, 2, 1, 3, 1, 2, 2]
def baseStart_1467420 : Nat := 118140960795 + 1467420 * 2 ^ 59
def prefixEnd_1467420 : Nat := 4983230072969 + 3 ^ 40 * 1467420 * 2
def baseEnd_1467420 : Nat := 753491782020753946201465

theorem tailTrace_1467420 : CollatzResearch.WordTrace tailWord_1467420 prefixEnd_1467420 753491782020753946201465 := by
  unfold tailWord_1467420
  simp only [CollatzResearch.WordTrace]
  refine ⟨26760602171897715114299857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35680802895863620152399809 26760602171897715114299857)
  ·
    refine ⟨20070451628923286335724893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26760602171897715114299857 20070451628923286335724893)
    ·
      refine ⟨7526419360846232375896835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20070451628923286335724893 7526419360846232375896835)
      ·
        refine ⟨11289629041269348563845253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7526419360846232375896835 11289629041269348563845253)
        ·
          refine ⟨2116805445238002855720985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11289629041269348563845253 2116805445238002855720985)
          ·
            refine ⟨1587604083928502141790739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2116805445238002855720985 1587604083928502141790739)
            ·
              refine ⟨2381406125892753212686109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587604083928502141790739 2381406125892753212686109)
              ·
                refine ⟨893027297209782454757291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2381406125892753212686109 893027297209782454757291)
                ·
                  refine ⟨1339540945814673682135937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893027297209782454757291 1339540945814673682135937)
                  ·
                    refine ⟨1004655709361005261601953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1339540945814673682135937 1004655709361005261601953)
                    ·
                      refine ⟨753491782020753946201465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1004655709361005261601953 753491782020753946201465)
                      ·
                        rfl

theorem cell23_1467420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_1467420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467420 prefixEnd_1467420 := by exact prefixLift 1467420
  have htrace : WordTrace (prefixWord ++ tailWord_1467420) baseStart_1467420 baseEnd_1467420 := by
    simpa [prefixWord, tailWord_1467420, baseEnd_1467420] using wordTrace_append hprefix tailTrace_1467420
  have hstable : (prefixWord ++ tailWord_1467420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467420).length < 2 ^ (prefixWord ++ tailWord_1467420).sum := by decide
  have hdescent : baseEnd_1467420 < baseStart_1467420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467429 : List Nat := [1, 3, 1, 2, 2, 2, 1, 5, 1, 3, 2]
def baseStart_1467429 : Nat := 118140960795 + 1467429 * 2 ^ 59
def prefixEnd_1467429 : Nat := 4983230072969 + 3 ^ 40 * 1467429 * 2
def baseEnd_1467429 : Nat := 753496403346644410988923

theorem tailTrace_1467429 : CollatzResearch.WordTrace tailWord_1467429 prefixEnd_1467429 753496403346644410988923 := by
  unfold tailWord_1467429
  simp only [CollatzResearch.WordTrace]
  refine ⟨53521532600762824765677341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35681021733841883177118227 53521532600762824765677341)
  ·
    refine ⟨20070574725286059287129003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53521532600762824765677341 20070574725286059287129003)
    ·
      refine ⟨30105862087929088930693505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20070574725286059287129003 30105862087929088930693505)
      ·
        refine ⟨22579396565946816698020129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30105862087929088930693505 22579396565946816698020129)
        ·
          refine ⟨16934547424460112523515097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22579396565946816698020129 16934547424460112523515097)
          ·
            refine ⟨12700910568345084392636323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16934547424460112523515097 12700910568345084392636323)
            ·
              refine ⟨19051365852517626588954485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12700910568345084392636323 19051365852517626588954485)
              ·
                refine ⟨1786065548673527492714483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19051365852517626588954485 1786065548673527492714483)
                ·
                  refine ⟨2679098323010291239071725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1786065548673527492714483 2679098323010291239071725)
                  ·
                    refine ⟨1004661871128859214651897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2679098323010291239071725 1004661871128859214651897)
                    ·
                      refine ⟨753496403346644410988923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1004661871128859214651897 753496403346644410988923)
                      ·
                        rfl

theorem cell23_1467429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_1467429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467429 prefixEnd_1467429 := by exact prefixLift 1467429
  have htrace : WordTrace (prefixWord ++ tailWord_1467429) baseStart_1467429 baseEnd_1467429 := by
    simpa [prefixWord, tailWord_1467429, baseEnd_1467429] using wordTrace_append hprefix tailTrace_1467429
  have hstable : (prefixWord ++ tailWord_1467429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467429).length < 2 ^ (prefixWord ++ tailWord_1467429).sum := by decide
  have hdescent : baseEnd_1467429 < baseStart_1467429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467445 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1467445 : Nat := 118140960795 + 1467445 * 2 ^ 59
def prefixEnd_1467445 : Nat := 4983230072969 + 3 ^ 40 * 1467445 * 2
def baseEnd_1467445 : Nat := 753504619037116348388849

theorem tailTrace_1467445 : CollatzResearch.WordTrace tailWord_1467445 prefixEnd_1467445 753504619037116348388849 := by
  unfold tailWord_1467445
  simp only [CollatzResearch.WordTrace]
  refine ⟨53522116168704859498259789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35681410779136572998839859 53522116168704859498259789)
  ·
    refine ⟨20070793563264322311847421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53522116168704859498259789 20070793563264322311847421)
    ·
      refine ⟨7526547586224120866942783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20070793563264322311847421 7526547586224120866942783)
      ·
        refine ⟨11289821379336181300414175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7526547586224120866942783 11289821379336181300414175)
        ·
          refine ⟨16934732069004271950621263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11289821379336181300414175 16934732069004271950621263)
          ·
            refine ⟨25402098103506407925931895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16934732069004271950621263 25402098103506407925931895)
            ·
              refine ⟨38103147155259611888897843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25402098103506407925931895 38103147155259611888897843)
              ·
                refine ⟨57154720732889417833346765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38103147155259611888897843 57154720732889417833346765)
                ·
                  refine ⟨21433020274833531687505037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57154720732889417833346765 21433020274833531687505037)
                  ·
                    refine ⟨8037382603062574382814389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21433020274833531687505037 8037382603062574382814389)
                    ·
                      refine ⟨753504619037116348388849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8037382603062574382814389 753504619037116348388849)
                      ·
                        rfl

theorem cell23_1467445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1467445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467445 prefixEnd_1467445 := by exact prefixLift 1467445
  have htrace : WordTrace (prefixWord ++ tailWord_1467445) baseStart_1467445 baseEnd_1467445 := by
    simpa [prefixWord, tailWord_1467445, baseEnd_1467445] using wordTrace_append hprefix tailTrace_1467445
  have hstable : (prefixWord ++ tailWord_1467445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467445).length < 2 ^ (prefixWord ++ tailWord_1467445).sum := by decide
  have hdescent : baseEnd_1467445 < baseStart_1467445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467453 : List Nat := [1, 4, 1, 3, 1, 4, 2, 1, 2, 1, 3]
def baseStart_1467453 : Nat := 118140960795 + 1467453 * 2 ^ 59
def prefixEnd_1467453 : Nat := 4983230072969 + 3 ^ 40 * 1467453 * 2
def baseEnd_1467453 : Nat := 753508726882352317088813

theorem tailTrace_1467453 : CollatzResearch.WordTrace tailWord_1467453 prefixEnd_1467453 753508726882352317088813 := by
  unfold tailWord_1467453
  simp only [CollatzResearch.WordTrace]
  refine ⟨53522407952675876864551013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35681605301783917909700675 53522407952675876864551013)
  ·
    refine ⟨10035451491126726912103315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53522407952675876864551013 10035451491126726912103315)
    ·
      refine ⟨15053177236690090368154973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10035451491126726912103315 15053177236690090368154973)
      ·
        refine ⟨5644941463758783888058115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15053177236690090368154973 5644941463758783888058115)
        ·
          refine ⟨8467412195638175832087173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5644941463758783888058115 8467412195638175832087173)
          ·
            refine ⟨1587639786682157968516345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8467412195638175832087173 1587639786682157968516345)
            ·
              refine ⟨1190729840011618476387259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1587639786682157968516345 1190729840011618476387259)
              ·
                refine ⟨1786094760017427714580889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190729840011618476387259 1786094760017427714580889)
                ·
                  refine ⟨1339571070013070785935667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1786094760017427714580889 1339571070013070785935667)
                  ·
                    refine ⟨2009356605019606178903501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1339571070013070785935667 2009356605019606178903501)
                    ·
                      refine ⟨753508726882352317088813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2009356605019606178903501 753508726882352317088813)
                      ·
                        rfl

theorem cell23_1467453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_1467453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467453 prefixEnd_1467453 := by exact prefixLift 1467453
  have htrace : WordTrace (prefixWord ++ tailWord_1467453) baseStart_1467453 baseEnd_1467453 := by
    simpa [prefixWord, tailWord_1467453, baseEnd_1467453] using wordTrace_append hprefix tailTrace_1467453
  have hstable : (prefixWord ++ tailWord_1467453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467453).length < 2 ^ (prefixWord ++ tailWord_1467453).sum := by decide
  have hdescent : baseEnd_1467453 < baseStart_1467453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467455 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 4]
def baseStart_1467455 : Nat := 118140960795 + 1467455 * 2 ^ 59
def prefixEnd_1467455 : Nat := 4983230072969 + 3 ^ 40 * 1467455 * 2
def baseEnd_1467455 : Nat := 753509753843661309263803

theorem tailTrace_1467455 : CollatzResearch.WordTrace tailWord_1467455 prefixEnd_1467455 753509753843661309263803 := by
  unfold tailWord_1467455
  simp only [CollatzResearch.WordTrace]
  refine ⟨53522480898668631206123819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35681653932445754137415879 53522480898668631206123819)
  ·
    refine ⟨80283721348002946809185729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53522480898668631206123819 80283721348002946809185729)
    ·
      refine ⟨60212791011002210106889297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80283721348002946809185729 60212791011002210106889297)
      ·
        refine ⟨45159593258251657580166973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60212791011002210106889297 45159593258251657580166973)
        ·
          refine ⟨16934847471844371592562615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45159593258251657580166973 16934847471844371592562615)
          ·
            refine ⟨25402271207766557388843923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16934847471844371592562615 25402271207766557388843923)
            ·
              refine ⟨38103406811649836083265885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25402271207766557388843923 38103406811649836083265885)
              ·
                refine ⟨14288777554368688531224707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38103406811649836083265885 14288777554368688531224707)
                ·
                  refine ⟨21433166331553032796837061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14288777554368688531224707 21433166331553032796837061)
                  ·
                    refine ⟨4018718687166193649406949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21433166331553032796837061 4018718687166193649406949)
                    ·
                      refine ⟨753509753843661309263803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4018718687166193649406949 753509753843661309263803)
                      ·
                        rfl

theorem cell23_1467455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_1467455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467455 prefixEnd_1467455 := by exact prefixLift 1467455
  have htrace : WordTrace (prefixWord ++ tailWord_1467455) baseStart_1467455 baseEnd_1467455 := by
    simpa [prefixWord, tailWord_1467455, baseEnd_1467455] using wordTrace_append hprefix tailTrace_1467455
  have hstable : (prefixWord ++ tailWord_1467455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467455).length < 2 ^ (prefixWord ++ tailWord_1467455).sum := by decide
  have hdescent : baseEnd_1467455 < baseStart_1467455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467492 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 2, 3, 3]
def baseStart_1467492 : Nat := 118140960795 + 1467492 * 2 ^ 59
def prefixEnd_1467492 : Nat := 4983230072969 + 3 ^ 40 * 1467492 * 2
def baseEnd_1467492 : Nat := 753528752627877664501133

theorem tailTrace_1467492 : CollatzResearch.WordTrace tailWord_1467492 prefixEnd_1467492 753528752627877664501133 := by
  unfold tailWord_1467492
  simp only [CollatzResearch.WordTrace]
  refine ⟨26761915199767293262610365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35682553599689724350147153 26761915199767293262610365)
  ·
    refine ⟨10035718199912734973478887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26761915199767293262610365 10035718199912734973478887)
    ·
      refine ⟨15053577299869102460218331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10035718199912734973478887 15053577299869102460218331)
      ·
        refine ⟨22580365949803653690327497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15053577299869102460218331 22580365949803653690327497)
        ·
          refine ⟨16935274462352740267745623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22580365949803653690327497 16935274462352740267745623)
          ·
            refine ⟨25402911693529110401618435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16935274462352740267745623 25402911693529110401618435)
            ·
              refine ⟨38104367540293665602427653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25402911693529110401618435 38104367540293665602427653)
              ·
                refine ⟨7144568913805062300455185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38104367540293665602427653 7144568913805062300455185)
                ·
                  refine ⟨5358426685353796725341389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7144568913805062300455185 5358426685353796725341389)
                  ·
                    refine ⟨2009410007007673772003021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5358426685353796725341389 2009410007007673772003021)
                    ·
                      refine ⟨753528752627877664501133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2009410007007673772003021 753528752627877664501133)
                      ·
                        rfl

theorem cell23_1467492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_1467492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467492 prefixEnd_1467492 := by exact prefixLift 1467492
  have htrace : WordTrace (prefixWord ++ tailWord_1467492) baseStart_1467492 baseEnd_1467492 := by
    simpa [prefixWord, tailWord_1467492, baseEnd_1467492] using wordTrace_append hprefix tailTrace_1467492
  have hstable : (prefixWord ++ tailWord_1467492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467492).length < 2 ^ (prefixWord ++ tailWord_1467492).sum := by decide
  have hdescent : baseEnd_1467492 < baseStart_1467492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
